import Mica.TinyML.Typed
import Mica.TinyML.Untyped
import Mica.TinyML.Typing
import Mica.Verifier.Functions
import Mica.Frontend.SpecParser
import Mica.Verifier.SpecTranslation
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Engine.Driver

open Iris Iris.BI
open Typed

private def parseSpec (e : Untyped.Expr) : Except String SpecPredicate := do
  let spec ← Spec.parse e
  SpecTranslation.translate spec

/-- Extract typed argument names from a function's argument list. -/
private def extractArgs : List Binder → List String → Except String (List (String × TinyML.Typ))
  | [], names =>
    if names.isEmpty then .ok []
    else .error s!"spec has more arguments than function"
  | _ :: _, [] => .ok []
  | b :: rest, n :: ns => do
    let tail ← extractArgs rest ns
    .ok ((n, b.ty) :: tail)

/-- Complete a raw spec predicate with type information from a function expression. -/
def Spec.complete (sp : SpecPredicate) (e : Expr) : Except String Spec :=
  match e with
  | .fix _ argBinders retTy _ => do
    let args ← extractArgs argBinders sp.1
    .ok { args, retTy, pred := sp.2 }
  | _ => .error "Spec.complete: expected function"

/-! ## Program-level verification

Iterates over a list of declarations, verifying each one against its spec
and accumulating the spec map for use by subsequent declarations. -/

def Program.prepare (prog : Untyped.Program Untyped.Expr) :
    VerifM (TinyML.TypeEnv × Typed.Program Untyped.Expr) :=
  match Typed.Program.elaborate TinyML.TypeEnv.empty TinyML.TyCtx.empty prog with
  | .ok prepared => .ret prepared
  | .error err => .fatal (toString err)

/-- Check an individual declaration. Each declaration's `checkSpec` runs inside a `seq` bracket so its
    declarations and assertions don't pollute subsequent verifications. -/
def ValDecl.check (Θ : TinyML.TypeEnv) (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) : VerifM Spec := do
  let specExpr ← match d.spec with
    | some e => .ret e
    | none => .fatal "declaration has no spec"
  let sp ← match parseSpec specExpr with
  | .ok a => .ret a
  | .error msg => .fatal msg
  let spec ← match Spec.complete sp d.body with
    | .ok s => .ret s
    | .error e => .fatal e
  let () ← match Spec.checkWf spec Signature.empty with
    | .ok () => .ret ()
    | .error msg => .fatal msg
  VerifM.seq (checkSpec Θ S d.body spec) (pure spec)

/-- Check a `let _ = e` declaration: just compile `e` for safety, no spec. -/
def ValDecl.checkExpr (Θ : TinyML.TypeEnv) (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) : VerifM Unit :=
  VerifM.seq (do let _ ← compile Θ S [] TinyML.TyCtx.empty d.body; pure ()) (pure ())

/-- Verify all declarations in a program, accumulating specs as we go. -/
def Program.check (Θ : TinyML.TypeEnv) : SpecMap → Typed.Program Untyped.Expr → VerifM Unit
  | _, [] => pure ()
  | S, d :: ds => do
    match d.name.name, d.spec with
    | none, none =>
      ValDecl.checkExpr Θ S d
      Program.check Θ S ds
    | some n, none =>
    -- Named declaration without a spec: skip if it's a function definition
    -- (no code executes), otherwise check it. Erase any old spec for this
    -- name since the new binding shadows it.
      if d.body.isFunc then
        Program.check Θ (S.erase n) ds
      else
        ValDecl.checkExpr Θ S d
        Program.check Θ (S.erase n) ds
    | _, _ =>
      let spec ← ValDecl.check Θ S d
      let S' := match d.name.name with
        | some name => S.insert name spec
        | none => S
      Program.check Θ S' ds

def Program.verify (prog : Untyped.Program Untyped.Expr) : Smt.Strategy Smt.Strategy.Outcome :=
  VerifM.strategy do
    let (Θ, typed) ← Program.prepare prog
    Program.check Θ ∅ typed

/-! ## Correctness -/

theorem Program.prepare_correct (prog : Untyped.Program Untyped.Expr)
    (st : TransState) (ρ : Env)
    {Q : (TinyML.TypeEnv × Typed.Program Untyped.Expr) → TransState → Env → Prop}
    (heval : VerifM.eval (Program.prepare prog) st ρ Q) :
    ∃ Θ typed, Typed.Program.runtime typed = Untyped.Program.runtime prog ∧ Q (Θ, typed) st ρ := by
  unfold Program.prepare at heval
  cases helab : Typed.Program.elaborate TinyML.TypeEnv.empty TinyML.TyCtx.empty prog with
  | error err =>
    simp [helab] at heval
    exact (VerifM.eval_fatal heval).elim
  | ok prepared =>
    rcases prepared with ⟨Θ, typed⟩
    refine ⟨Θ, typed, Typed.Program.elaborate_runtime TinyML.TypeEnv.empty TinyML.TyCtx.empty prog helab, ?_⟩
    simp [helab] at heval
    exact VerifM.eval_ret heval

theorem ValDecl.checkExpr_correct (Θ : TinyML.TypeEnv) (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) (γ : Runtime.Subst)
    (hSwf : S.wfIn Signature.empty) (ρ : Env)
    {Q : Unit → TransState → Env → Prop}
    (heval : VerifM.eval (ValDecl.checkExpr Θ S d) TransState.empty ρ Q) :
    (S.satisfiedBy Θ γ ⊢ Φ) →
    S.satisfiedBy Θ γ ⊢ wp (d.body.runtime.subst γ) (fun _ => Φ) := by
  intro Hent
  simp only [ValDecl.checkExpr] at heval
  have ⟨hinner, _⟩ := VerifM.eval_seq heval
  have hcompile := VerifM.eval_bind _ _ _ _ hinner
  have hcomp :=
    compile_correct Θ iprop(S.satisfiedBy Θ γ) d.body S [] TinyML.TyCtx.empty TransState.empty ρ γ
    (fun x st' ρ' => VerifM.eval (pure ()) st' ρ' (fun _ _ _ => True))
    (fun _ => Φ)
    hcompile
    (fun _ _ h => by simp at h)
    (fun _ h => by simp at h)
    (fun _ _ _ h _ => by simp at h)
    hSwf
    (fun _ _ _ _ _ _ _ _ => by
      istart
      iintro ⟨_, Hsat⟩
      iapply Hent
      iexact Hsat)
  refine (BIBase.Entails.trans ?_ hcomp)
  istart
  iintro □Hspec
  isplitl []
  . simp [TransState.empty]
    iemp_intro
  . isplitl []
    . iexact Hspec
    . iexact Hspec

theorem ValDecl.check_correct (Θ : TinyML.TypeEnv) (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) (γ : Runtime.Subst)
    (hSwf : S.wfIn Signature.empty) (ρ : Env)
    {Q : Spec → TransState → Env → Prop}
    (heval : VerifM.eval (ValDecl.check Θ S d) TransState.empty ρ Q) :
    ∃ spec, spec.wfIn Signature.empty ∧
            (S.satisfiedBy Θ γ ⊢ wp (d.body.runtime.subst γ) (fun v => spec.isPrecondFor Θ v)) ∧
            Q spec TransState.empty ρ := by
  simp only [ValDecl.check] at heval
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
        cases hwf : Spec.checkWf spec Signature.empty with
        | error msg =>
          simp only [hwf] at h3
          exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ h3)).elim
        | ok u =>
          simp only [hwf] at h3
          have h4 := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ h3)
          have hswf : spec.wfIn Signature.empty := Spec.checkWf_ok (by cases u; exact hwf)
          have ⟨hcheckSpec, hpure⟩ := VerifM.eval_seq h4
          exact ⟨spec, hswf, checkSpec_correct Θ S d.body spec γ hswf hSwf ρ hcheckSpec,
                 VerifM.eval_ret hpure⟩

/-- Strengthen the postcondition of a `wp` using a persistent resource:
    if `R` (persistent) entails `wp e P`, and `R` together with `P v` entails `Q v`,
    then `R` entails `wp e Q`. -/
private theorem wp_strengthen_persistent
    {R : iProp} [Iris.BI.Persistent R] {e : Runtime.Expr}
    {P Q : Runtime.Val → iProp}
    (hwp : R ⊢ wp e P) (hpost : ∀ v, R ⊢ P v -∗ Q v) :
    R ⊢ wp e Q := by
  iintro □HR
  iapply wp.mono
  isplitr
  · iintro %v
    iapply (hpost v)
    iexact HR
  · iapply hwp; iexact HR

theorem Program.check_correct (Θ : TinyML.TypeEnv) (S : SpecMap) (prog : Typed.Program Untyped.Expr) (γ : Runtime.Subst)
    (hSwf : S.wfIn Signature.empty) (ρ : Env) :
    VerifM.eval (Program.check Θ S prog) TransState.empty ρ (fun _ _ _ => True) →
    S.satisfiedBy Θ γ ⊢ pwp ((Typed.Program.runtime prog).subst γ) := by
  induction prog generalizing S γ ρ with
  | nil =>
    intro _
    simp only [Typed.Program.runtime, List.map_nil, Runtime.Program.subst, pwp]
    exact (pure_intro (PROP := iProp) trivial).trans true_emp.1
  | cons d ds ih =>
    intro heval
    have hpwp_unfold : pwp ((Typed.Program.runtime (d :: ds)).subst γ) ⊣⊢
        wp (d.body.runtime.subst γ) (fun v =>
          pwp ((Typed.Program.runtime ds).subst (Runtime.Subst.update' d.name.runtime v γ))) := by
      simp [Typed.Program.runtime, Typed.ValDecl.runtime,
        Runtime.Program.subst, Runtime.Decl.subst, Runtime.Program.subst_remove_update]
    refine BIBase.Entails.trans ?_ hpwp_unfold.2
    simp only [Program.check] at heval
    cases hname : d.name.name with
    | none =>
      -- unnamed: pwp continuation does not depend on `v`
      have hupd : ∀ v, Runtime.Subst.update' d.name.runtime v γ = γ := by
        intro v; simp [Binder.runtime_of_name_none hname, Runtime.Subst.update']
      cases hspec : d.spec with
      | none =>
        -- unnamed, no spec
        simp only [hname, hspec] at heval
        have hbind := VerifM.eval_bind _ _ _ _ heval
        have ⟨_, hcont⟩ := VerifM.eval_seq hbind
        have hih := ih S γ hSwf ρ (VerifM.eval_ret hcont)
        have hwp := ValDecl.checkExpr_correct Θ S d γ hSwf ρ hbind hih
        refine hwp.trans (wp.mono' ?_)
        intro v; rw [hupd v]; exact .rfl
      | some _ =>
        -- unnamed, with spec
        simp only [hname, hspec] at heval
        obtain ⟨spec, _, hwp, hcont⟩ :=
          ValDecl.check_correct Θ S d γ hSwf ρ (VerifM.eval_bind _ _ _ _ heval)
        have hih := ih S γ hSwf ρ hcont
        refine wp_strengthen_persistent hwp ?_
        intro v
        rw [hupd v]
        exact wand_intro (sep_elim_l.trans hih)
    | some n =>
      have hname_rt : d.name.runtime = .named n := Binder.runtime_of_name_some hname
      have herase : S.erase' d.name = S.erase n := by simp [SpecMap.erase', hname]
      have hinsert : ∀ s, S.insert' d.name s = S.insert n s := by
        intro s; simp [SpecMap.insert', hname]
      have hupd : ∀ v, Runtime.Subst.update' d.name.runtime v γ = γ.update n v := by
        intro v; simp [hname_rt, Runtime.Subst.update']
      cases hspec : d.spec with
      | none =>
        simp only [hname, hspec] at heval
        split at heval
        · -- named, no spec, function value
          rename_i hfunc
          obtain ⟨self, args, retTy, body, hbody⟩ := Expr.isFunc_elim hfunc
          have hbody_rt : d.body.runtime.subst γ =
              Runtime.Expr.fix self.runtime (args.map (·.runtime))
                (body.runtime.subst ((γ.remove' self.runtime).removeAll'
                  (args.map (·.runtime)))) := by
            rw [hbody]; conv_lhs => unfold Expr.runtime
            simp only [Runtime.Expr.subst_fix]
          rw [hbody_rt]
          set fval := Runtime.Val.fix self.runtime (args.map (·.runtime))
            (body.runtime.subst ((γ.remove' self.runtime).removeAll'
              (args.map (·.runtime))))
          apply SpatialContext.wp_func
          rw [hupd fval]
          have heval' : VerifM.eval (Program.check Θ (S.erase n) ds) TransState.empty ρ (fun _ _ _ => True) := by
            convert heval
          have hih := ih (S.erase n) (γ.update n fval)
            (SpecMap.wfIn_erase hSwf) ρ heval'
          exact (SpecMap.satisfiedBy_erase (x := n) (v := fval)).trans hih
        · -- named, no spec, not a function
          have hbind := VerifM.eval_bind _ _ _ _ heval
          have ⟨_, hcont⟩ := VerifM.eval_seq hbind
          have hcont' : VerifM.eval (Program.check Θ (S.erase n) ds) TransState.empty ρ (fun _ _ _ => True) :=
            VerifM.eval_ret hcont
          have hwp := ValDecl.checkExpr_correct Θ S d γ hSwf ρ hbind
            (Φ := iprop(emp)) (by istart; iintro _; iemp_intro)
          refine wp_strengthen_persistent hwp ?_
          intro v
          rw [hupd v]
          have hih := ih (S.erase n) (γ.update n v) (SpecMap.wfIn_erase hSwf) ρ hcont'
          exact wand_intro (sep_elim_l.trans <|
            (SpecMap.satisfiedBy_erase (x := n) (v := v)).trans hih)
      | some _ =>
        simp only [hname, hspec] at heval
        obtain ⟨spec, hswf, hwp, hcont⟩ :=
          ValDecl.check_correct Θ S d γ hSwf ρ (VerifM.eval_bind _ _ _ _ heval)
        have hcont' : VerifM.eval (Program.check Θ (S.insert n spec) ds) TransState.empty ρ (fun _ _ _ => True) := by
          convert hcont
        refine wp_strengthen_persistent hwp ?_
        intro v
        rw [hupd v]
        have hih := ih (S.insert n spec) (γ.update n v)
          (SpecMap.wfIn_insert hSwf hswf) ρ hcont'
        exact wand_intro
          ((SpecMap.satisfiedBy_insert_update (x := n) (v := v) (spec := spec)).trans hih)

theorem Program.verify_correct (p : Untyped.Program Untyped.Expr) :
  Smt.Strategy.checks (Program.verify p) (⊢ pwp (Untyped.Program.runtime p)) := by
  simp only [Smt.Strategy.checks, Program.verify, VerifM.strategy]
  intro st' heval
  have h1 := ScopedM.strategy_eval_initial_implies_ScopedM_eval heval
  obtain ⟨a, ctx_mid, hverif, hcont⟩ := ScopedM.eval_bind h1
  match a with
  | .error e =>
    cases e <;> simp [ScopedM.eval_ret] at hcont
  | .ok () =>
    have hholdsFor : TransState.holdsFor TransState.empty default :=
      fun φ hφ => by simp [TransState.empty] at hφ
    have hwf : TransState.wf TransState.empty :=
      ⟨fun φ hφ => by simp [TransState.empty] at hφ,
       by simp [TransState.empty, Signature.empty, Signature.allNames],
       fun a ha => by simp [TransState.empty] at ha⟩
    have hverifM := VerifM.eval_of_translate
                      (do
                        let (Θ, typed) ← Program.prepare p
                        Program.check Θ ∅ typed)
                      TransState.empty default ctx_mid hverif hholdsFor hwf
    have hbind := VerifM.eval_bind _ _ _ _ hverifM
    obtain ⟨Θ, typed, hrt, hcheck⟩ := Program.prepare_correct p TransState.empty default hbind
    have hcorrect := Program.check_correct Θ ∅ typed Runtime.Subst.id
                       (SpecMap.empty_wfIn _) default hcheck
    rw [Runtime.Program.subst_id] at hcorrect
    have hsat : (⊢ SpecMap.satisfiedBy Θ (∅ : SpecMap) Runtime.Subst.id) :=
      SpecMap.empty_satisfiedBy _
    simpa [hrt] using hsat.trans hcorrect
