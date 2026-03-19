import Mica.TinyML.Expr
import Mica.TinyML.WeakestPre
import Mica.Verifier.Functions
import Mica.Verifier.Parser
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Engine.Driver

/-! ## Program-level verification

Iterates over a list of declarations, verifying each one against its spec
and accumulating the spec map for use by subsequent declarations. -/

/-- Parse a spec expression into a `SpecPredicate`. -/
private def parseSpec (e : TinyML.Expr) : Except String SpecPredicate :=
  SpecParser.spec [] e

/-- Extract typed argument names from a function's argument list. -/
private def extractArgs : List (TinyML.Binder × Option TinyML.Type_) → List String → Except String (List (String × TinyML.Type_))
  | [], names =>
    if names.isEmpty then .ok []
    else .error s!"spec has more arguments than function"
  | (_, _) :: _, [] => .ok []  -- spec may bind fewer args than the function has
  | (.named _, .some ty) :: rest, n :: ns => do
    let tail ← extractArgs rest ns
    .ok ((n, ty) :: tail)
  | (_, _) :: _, _ :: _ => .error "Spec.complete: all spec arguments must have type annotations"

/-- Complete a raw spec predicate with type information from a function expression. -/
def Spec.complete (sp : SpecPredicate) (e : TinyML.Expr) : Except String Spec :=
  match e with
  | .fix _ argBinders (.some retTy) _ => do
    let args ← extractArgs argBinders sp.1
    .ok { args, retTy, pred := sp.2 }
  | _ => .error "Spec.complete: expected function with return type annotation"

/-- Check an individual declaration. Each declaration's `checkSpec` runs inside a `seq` bracket so its
    declarations and assertions don't pollute subsequent verifications. -/
def Decl.check (S : SpecMap) (d : TinyML.Decl TinyML.Expr) : VerifM Spec := do
  let specExpr ← match d.spec with
    | some e => .ret e
    | none => .fatal "declaration has no spec"
  let sp ← match parseSpec specExpr with
  | .ok a => .ret a
  | .error msg => .fatal msg
  let spec ← match Spec.complete sp d.body with
    | .ok s => .ret s
    | .error e => .fatal e
  let () ← match Spec.checkWf spec [] with
    | .ok () => .ret ()
    | .error msg => .fatal msg
  VerifM.seq (checkSpec S d.body spec) (pure spec)

/-- Check a `let _ = e` declaration: just compile `e` for safety, no spec. -/
def Decl.checkExpr (S : SpecMap) (d : TinyML.Decl TinyML.Expr) : VerifM Unit :=
  VerifM.seq (do let _ ← compile S [] TinyML.TyCtx.empty d.body; pure ()) (pure ())

/-- Verify all declarations in a program, accumulating specs as we go. -/
def Program.check : SpecMap → TinyML.Program → VerifM Unit
  | _, [] => pure ()
  | S, d :: ds => do
    match d.name, d.spec with
    | .none, none =>
      Decl.checkExpr S d
      Program.check S ds
    | _, _ =>
      let spec ← Decl.check S d
      let S' := match d.name with
        | .named name => S.insert name spec
        | .none => S
      Program.check S' ds

def Program.verify (prog : TinyML.Program) : Strategy Outcome :=
  VerifM.strategy (Program.check ∅ prog)

/-! ## Correctness -/


theorem SpecMap.satisfiedBy_insert_update {S : SpecMap} {γ : TinyML.Subst}
    {x : TinyML.Var} {v : TinyML.Val} {spec : Spec}
    (hS : S.satisfiedBy γ) (hf : spec.isPrecondFor v) :
    SpecMap.satisfiedBy (Finmap.insert x spec S) (γ.update x v) := by
  intro y s' hlookup
  by_cases hyx : y = x
  · subst hyx; rw [Finmap.lookup_insert] at hlookup; simp at hlookup; subst hlookup
    exact ⟨v, by simp [TinyML.Subst.update], hf⟩
  · rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
    obtain ⟨f, hγf, hprecond⟩ := hS y s' hlookup
    exact ⟨f, by simp [TinyML.Subst.update, beq_false_of_ne hyx, hγf], hprecond⟩

theorem SpecMap.satisfiedBy_insert'_update' {S : SpecMap} {γ : TinyML.Subst}
    {b : TinyML.Binder} {v : TinyML.Val} {spec : Spec}
    (hS : S.satisfiedBy γ) (hf : spec.isPrecondFor v) :
    SpecMap.satisfiedBy (S.insert' b spec) (TinyML.Subst.update' b v γ) := by
  cases b with
  | named x => exact SpecMap.satisfiedBy_insert_update hS hf
  | none => exact hS


theorem Decl.checkExpr_correct (S : SpecMap) (d : TinyML.Decl TinyML.Expr) (γ : TinyML.Subst)
    (hS : S.satisfiedBy γ) (hSwf : S.wfIn [])
    (st : TransState) (ρ : Env)
    {Q : Unit → TransState → Env → Prop}
    (heval : VerifM.eval (Decl.checkExpr S d) st ρ Q) :
    wp (d.body.subst γ) (fun _ => True) := by
  simp only [Decl.checkExpr] at heval
  have ⟨hinner, _⟩ := VerifM.eval_seq heval
  -- hinner : VerifM.eval (compile ... >>= fun _ => pure ()) st ρ (fun _ _ _ => True)
  have hcompile := VerifM.eval_bind _ _ _ _ hinner
  -- hcompile : VerifM.eval (compile ...) st ρ (fun x st' ρ' => (pure ()).eval ...)
  exact compile_correct d.body S [] TinyML.TyCtx.empty st ρ γ
    (fun x st' ρ' => VerifM.eval (pure ()) st' ρ' (fun _ _ _ => True))
    (fun _ => True)
    hcompile
    (fun _ _ h => by simp at h)
    (fun _ h => by simp at h)
    (fun _ _ _ h _ => by simp at h)
    hS hSwf
    (fun _ _ _ _ _ _ _ _ _ => trivial)

theorem Decl.check_correct (S : SpecMap) (d : TinyML.Decl TinyML.Expr) (γ : TinyML.Subst)
    (hS : S.satisfiedBy γ) (hSwf : S.wfIn [])
    (st : TransState) (ρ : Env)
    {Q : Spec → TransState → Env → Prop}
    (heval : VerifM.eval (Decl.check S d) st ρ Q) :
    ∃ spec, spec.wfIn [] ∧
            wp (d.body.subst γ) (spec.isPrecondFor ·) ∧
            Q spec st ρ := by
  simp only [Decl.check] at heval
  cases hspec : d.spec with
  | none =>
    simp only [hspec] at heval
    exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim
  | some specExpr =>
    simp only [hspec] at heval
    have h1 := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ heval)
    cases hparse : parseSpec specExpr with
    | error msg =>
      simp only [hparse] at h1
      exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ h1)).elim
    | ok sp =>
      simp only [hparse] at h1
      have h2 := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ h1)
      cases hcomplete : Spec.complete sp d.body with
      | error msg =>
        simp only [hcomplete] at h2
        exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ h2)).elim
      | ok spec =>
        simp only [hcomplete] at h2
        have h3 := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ h2)
        cases hwf : Spec.checkWf spec [] with
        | error msg =>
          simp only [hwf] at h3
          exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ h3)).elim
        | ok u =>
          simp only [hwf] at h3
          have h4 := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ h3)
          have hswf : spec.wfIn [] := Spec.checkWf_ok (by cases u; exact hwf)
          have ⟨hcheckSpec, hpure⟩ := VerifM.eval_seq h4
          exact ⟨spec, hswf, checkSpec_correct S d.body spec γ hswf hSwf hS st ρ hcheckSpec,
                 VerifM.eval_ret hpure⟩

theorem Program.check_correct (S : SpecMap) (prog : TinyML.Program) (γ : TinyML.Subst)
    (hS : S.satisfiedBy γ) (hSwf : S.wfIn [])
    (st : TransState) (ρ : Env) :
    VerifM.eval (Program.check S prog) st ρ (fun _ _ _ => True) →
    pwp (prog.subst γ) := by
  induction prog generalizing S γ st ρ with
  | nil =>
    intro _
    simp [TinyML.Program.subst, pwp]
  | cons d ds ih =>
    intro heval
    simp only [TinyML.Program.subst, TinyML.Decl.subst, pwp]
    simp only [Program.check] at heval
    -- Case-split to match the branching in Program.check
    cases hname : d.name
    -- Case: d.name = .none
    · cases hspec : d.spec
      -- Subcase: let _ = e (no spec) → checkExpr path
      · simp only [hname, hspec] at heval
        have hbind := VerifM.eval_bind _ _ _ _ heval
        have hwp := Decl.checkExpr_correct S d γ hS hSwf st ρ hbind
        have ⟨_, hcont⟩ := VerifM.eval_seq hbind
        apply wp.mono _ hwp
        intro v _
        rw [TinyML.Program.subst_remove_update]
        -- Subst.update' .none v γ = γ by definition
        show pwp (TinyML.Program.subst ds γ)
        exact ih S γ hS hSwf st ρ (VerifM.eval_ret hcont)
      -- Subcase: let _ = e with spec → Decl.check path
      · simp only [hname, hspec] at heval
        obtain ⟨spec, hswf, hwp, hcont⟩ :=
          Decl.check_correct S d γ hS hSwf st ρ (VerifM.eval_bind _ _ _ _ heval)
        apply wp.mono (fun v hprecond => _) hwp
        intro v hprecond
        rw [TinyML.Program.subst_remove_update]
        show pwp (TinyML.Program.subst ds γ)
        exact ih S γ hS hSwf st ρ hcont
    -- Case: d.name = .named n → Decl.check path (for both d.spec values)
    · rename_i n
      cases hspec : d.spec <;> simp only [hname, hspec] at heval <;> (
        obtain ⟨spec, hswf, hwp, hcont⟩ :=
          Decl.check_correct S d γ hS hSwf st ρ (VerifM.eval_bind _ _ _ _ heval)
        apply wp.mono (fun v hprecond => _) hwp
        intro v hprecond
        rw [TinyML.Program.subst_remove_update]
        show pwp (TinyML.Program.subst ds (γ.update n v))
        apply ih (Finmap.insert n spec S) (γ.update n v)
        · exact SpecMap.satisfiedBy_insert_update hS hprecond
        · exact SpecMap.wfIn_insert hSwf hswf
        · exact hcont)

theorem Program.verify_correct p :
  Strategy.checks (Program.verify p) (pwp p) := by
  simp only [Strategy.checks, Program.verify, VerifM.strategy]
  intro st' heval
  -- Translate the Strategy.eval into a ScopedM.eval
  have h1 := ScopedM.strategy_eval_initial_implies_ScopedM_eval heval
  -- Decompose the bind: verif' = verif.bind (fun ...)
  obtain ⟨a, ctx_mid, hverif, hcont⟩ := ScopedM.eval_bind h1
  -- The outcome a must be .ok (), otherwise the continuation can't return .ok ()
  match a with
  | .error e =>
    -- hcont reduces to ScopedM.eval (ScopedM.ret (.error ...)), requiring .ok () = .error ..., contradiction
    cases e <;> simp [ScopedM.eval_ret] at hcont
  | .ok () =>
    -- The initial TransState FlatCtx.empty satisfies holdsFor/wf trivially
    have hholdsFor : TransState.holdsFor FlatCtx.empty default :=
      fun φ hφ => by simp [FlatCtx.empty] at hφ
    have hwf : TransState.wf FlatCtx.empty :=
      ⟨fun φ hφ => by simp [FlatCtx.empty] at hφ,
       fun _ _ _ _ h => by simp [FlatCtx.empty] at h⟩
    -- Lift ScopedM.eval to VerifM.eval
    have hverifM := VerifM.eval_of_translate (Program.check ∅ p)
                      FlatCtx.empty default ctx_mid hverif hholdsFor hwf
    -- Apply the main correctness theorem with empty SpecMap
    have hcorrect := Program.check_correct ∅ p TinyML.Subst.id
                       (SpecMap.empty_satisfiedBy _) (SpecMap.empty_wfIn _)
                       FlatCtx.empty default hverifM
    rwa [TinyML.Program.subst_id] at hcorrect
