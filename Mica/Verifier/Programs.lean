import Mica.TinyML.Typed
import Mica.TinyML.Untyped
import Mica.TinyML.Typing
import Mica.TinyML.Erasure
import Mica.TinyML.WeakestPre
import Mica.Verifier.Functions
import Mica.Frontend.SpecParser
import Mica.Verifier.SpecTranslation
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Engine.Driver

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

def Program.prepare (Θ : TinyML.TypeEnv) (prog : Untyped.Program Untyped.Expr) : VerifM (Typed.Program Untyped.Expr) :=
  match Typed.Program.elaborate Θ TinyML.TyCtx.empty prog with
  | .ok typed => .ret typed
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
    match d with
    | .type_ _ =>
      Program.check Θ S ds
    | .val_ d =>
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
    let typed ← Program.prepare TinyML.TypeEnv.empty prog
    Program.check TinyML.TypeEnv.empty ∅ typed

/-! ## Correctness -/

theorem Program.prepare_correct (Θ : TinyML.TypeEnv) (prog : Untyped.Program Untyped.Expr)
    (st : TransState) (ρ : Env)
    {Q : Typed.Program Untyped.Expr → TransState → Env → Prop}
    (heval : VerifM.eval (Program.prepare Θ prog) st ρ Q) :
    ∃ typed, Typed.Program.runtime typed = Untyped.Program.runtime prog ∧ Q typed st ρ := by
  unfold Program.prepare at heval
  cases helab : Typed.Program.elaborate Θ TinyML.TyCtx.empty prog with
  | error err =>
    simp [helab] at heval
    exact (VerifM.eval_fatal heval).elim
  | ok typed =>
    refine ⟨typed, Typed.Program.elaborate_runtime Θ TinyML.TyCtx.empty prog helab, ?_⟩
    simp [helab] at heval
    exact VerifM.eval_ret heval

theorem ValDecl.checkExpr_correct (Θ : TinyML.TypeEnv) (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) (γ : Runtime.Subst)
    (hS : S.satisfiedBy Θ γ) (hSwf : S.wfIn Signature.empty)
    (st : TransState) (ρ : Env)
    {Q : Unit → TransState → Env → Prop}
    (heval : VerifM.eval (ValDecl.checkExpr Θ S d) st ρ Q) :
    wp (d.body.runtime.subst γ) (fun _ => True) := by
  simp only [ValDecl.checkExpr] at heval
  have ⟨hinner, _⟩ := VerifM.eval_seq heval
  have hcompile := VerifM.eval_bind _ _ _ _ hinner
  exact compile_correct Θ d.body S [] TinyML.TyCtx.empty st ρ γ
    (fun x st' ρ' => VerifM.eval (pure ()) st' ρ' (fun _ _ _ => True))
    (fun _ => True)
    hcompile
    (fun _ _ h => by simp at h)
    (fun _ h => by simp at h)
    (fun _ _ _ h _ => by simp at h)
    hS hSwf
    (fun _ _ _ _ _ _ _ _ => trivial)

theorem ValDecl.check_correct (Θ : TinyML.TypeEnv) (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) (γ : Runtime.Subst)
    (hS : S.satisfiedBy Θ γ) (hSwf : S.wfIn Signature.empty)
    (st : TransState) (ρ : Env)
    {Q : Spec → TransState → Env → Prop}
    (heval : VerifM.eval (ValDecl.check Θ S d) st ρ Q) :
    ∃ spec, spec.wfIn Signature.empty ∧
            wp (d.body.runtime.subst γ) (spec.isPrecondFor Θ ·) ∧
            Q spec st ρ := by
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
          exact ⟨spec, hswf, checkSpec_correct Θ S d.body spec γ hswf hSwf hS st ρ hcheckSpec,
                 VerifM.eval_ret hpure⟩

theorem Program.check_correct (Θ : TinyML.TypeEnv) (S : SpecMap) (prog : Typed.Program Untyped.Expr) (γ : Runtime.Subst)
    (hS : S.satisfiedBy Θ γ) (hSwf : S.wfIn Signature.empty)
    (st : TransState) (ρ : Env) :
    VerifM.eval (Program.check Θ S prog) st ρ (fun _ _ _ => True) →
    pwp ((Typed.Program.runtime prog).subst γ) := by
  induction prog generalizing S γ st ρ with
  | nil =>
    intro _
    simp [Typed.Program.runtime, Runtime.Program.subst, pwp]
  | cons d ds ih =>
    intro heval
    cases d with
    | type_ td =>
      simp [Program.check, Typed.Program.runtime] at heval ⊢
      exact ih S γ hS hSwf st ρ heval
    | val_ d =>
      have hpwp_unfold : pwp ((Typed.Program.runtime (.val_ d :: ds)).subst γ) ↔
          wp (d.body.runtime.subst γ) (fun v =>
            pwp ((Typed.Program.runtime ds).subst (Runtime.Subst.update' d.name.runtime v γ))) := by
        simp [Typed.Program.runtime, pwp, Typed.Decl.runtime, Typed.ValDecl.runtime,
          Runtime.Program.subst, Runtime.Decl.subst, Runtime.Program.subst_remove_update]
      rw [hpwp_unfold]
      simp only [Program.check] at heval
      cases hname : d.name.name
      · cases hspec : d.spec
        · simp only [hname, hspec] at heval
          have hbind := VerifM.eval_bind _ _ _ _ heval
          have hwp := ValDecl.checkExpr_correct Θ S d γ hS hSwf st ρ hbind
          have ⟨_, hcont⟩ := VerifM.eval_seq hbind
          apply wp.mono _ hwp
          intro v _
          simp only [Binder.runtime_of_name_none hname, Runtime.Subst.update']
          exact ih S γ hS hSwf st ρ (VerifM.eval_ret hcont)
        · simp only [hname, hspec] at heval
          obtain ⟨spec, hswf, hwp, hcont⟩ :=
            ValDecl.check_correct Θ S d γ hS hSwf st ρ (VerifM.eval_bind _ _ _ _ heval)
          apply wp.mono (fun v hprecond => _) hwp
          intro v hprecond
          simp only [Binder.runtime_of_name_none hname, Runtime.Subst.update']
          exact ih S γ hS hSwf st ρ hcont
      · rename_i n
        cases hspec : d.spec
        · simp only [hname, hspec] at heval
          split at heval
          · rename_i hfunc
            obtain ⟨self, args, retTy, body, hbody⟩ := Expr.isFunc_elim hfunc
            have hbody_rt : d.body.runtime.subst γ =
                Runtime.Expr.fix self.runtime (args.map (·.runtime))
                  (body.runtime.subst ((γ.remove' self.runtime).removeAll'
                    (args.map (·.runtime)))) := by
              rw [hbody]
              conv_lhs => unfold Expr.runtime
              simp only [Runtime.Expr.subst_fix]
            rw [hbody_rt]
            apply wp.func
            simp only [Binder.runtime_of_name_some hname, Runtime.Subst.update']
            simpa [SpecMap.erase', hname, Binder.runtime_of_name_some hname, Runtime.Subst.update'] using
              ih (S.erase' d.name) (Runtime.Subst.update' d.name.runtime _ γ)
              (SpecMap.satisfiedBy_erase' hS) (SpecMap.wfIn_erase' hSwf) st ρ (by
                simpa [SpecMap.erase', hname, Binder.runtime_of_name_some hname, Runtime.Subst.update'] using heval)
          · have hbind := VerifM.eval_bind _ _ _ _ heval
            have hwp := ValDecl.checkExpr_correct Θ S d γ hS hSwf st ρ hbind
            have ⟨_, hcont⟩ := VerifM.eval_seq hbind
            apply wp.mono _ hwp
            intro v _
            simp only [Binder.runtime_of_name_some hname, Runtime.Subst.update']
            simpa [SpecMap.erase', hname, Binder.runtime_of_name_some hname, Runtime.Subst.update'] using
              ih (S.erase' d.name) (Runtime.Subst.update' d.name.runtime v γ)
              (SpecMap.satisfiedBy_erase' hS) (SpecMap.wfIn_erase' hSwf) st ρ (by
                simpa [SpecMap.erase', hname, Binder.runtime_of_name_some hname, Runtime.Subst.update'] using
                  (VerifM.eval_ret hcont))
        · simp only [hname, hspec] at heval
          obtain ⟨spec, hswf, hwp, hcont⟩ :=
            ValDecl.check_correct Θ S d γ hS hSwf st ρ (VerifM.eval_bind _ _ _ _ heval)
          apply wp.mono (fun v hprecond => _) hwp
          intro v hprecond
          simp only [Binder.runtime_of_name_some hname, Runtime.Subst.update']
          simpa [SpecMap.insert', hname, Binder.runtime_of_name_some hname, Runtime.Subst.update'] using
            ih (S.insert' d.name spec) (Runtime.Subst.update' d.name.runtime v γ)
              (SpecMap.satisfiedBy_insert'_update' hS hprecond) (SpecMap.wfIn_insert' hSwf hswf) st ρ
              (by
                simpa [SpecMap.insert', hname, Binder.runtime_of_name_some hname, Runtime.Subst.update'] using hcont)

theorem Program.verify_correct (p : Untyped.Program Untyped.Expr) :
  Smt.Strategy.checks (Program.verify p) (pwp (Untyped.Program.runtime p)) := by
  simp only [Smt.Strategy.checks, Program.verify, VerifM.strategy]
  intro st' heval
  have h1 := ScopedM.strategy_eval_initial_implies_ScopedM_eval heval
  obtain ⟨a, ctx_mid, hverif, hcont⟩ := ScopedM.eval_bind h1
  match a with
  | .error e =>
    cases e <;> simp [ScopedM.eval_ret] at hcont
  | .ok () =>
    have hholdsFor : TransState.holdsFor FlatCtx.empty default :=
      fun φ hφ => by simp [FlatCtx.empty] at hφ
    have hwf : TransState.wf FlatCtx.empty :=
      ⟨fun φ hφ => by simp [FlatCtx.empty] at hφ,
       by simp [FlatCtx.empty, Signature.empty, Signature.allNames]⟩
    have hverifM := VerifM.eval_of_translate
                      (do
                        let typed ← Program.prepare TinyML.TypeEnv.empty p
                        Program.check TinyML.TypeEnv.empty ∅ typed)
                      FlatCtx.empty default ctx_mid hverif hholdsFor hwf
    have hbind := VerifM.eval_bind _ _ _ _ hverifM
    obtain ⟨typed, hrt, hcheck⟩ := Program.prepare_correct TinyML.TypeEnv.empty p FlatCtx.empty default hbind
    have hcorrect := Program.check_correct TinyML.TypeEnv.empty ∅ typed Runtime.Subst.id
                       (SpecMap.empty_satisfiedBy _) (SpecMap.empty_wfIn _)
                       FlatCtx.empty default hcheck
    rw [Runtime.Program.subst_id] at hcorrect
    simpa [hrt] using hcorrect
