-- SUMMARY: End-to-end preparation and verification of programs, from typed elaboration to program-level soundness.
import Mica.TinyML.Typed
import Mica.TinyML.Untyped
import Mica.TinyML.Typing
import Mica.SeparationLogic.PrimitiveLaws
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
def ValDecl.check (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) : VerifM Spec := do
  let specExpr ← match d.spec with
    | some e => .ret e
    | none => .fatal "declaration has no spec"
  let sp ← match parseSpec specExpr with
  | .ok a => .ret a
  | .error msg => .fatal msg
  let spec ← match Spec.complete sp d.body with
    | .ok s => .ret s
    | .error e => .fatal e
  let () ← match Spec.checkWf spec Δ_spec with
    | .ok () => .ret ()
    | .error msg => .fatal msg
  VerifM.seq (checkSpec Θ Δ_spec S d.body spec) (pure spec)

/-- Check a `let _ = e` declaration: just compile `e` for safety, no spec. -/
def ValDecl.checkExpr (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) : VerifM Unit :=
  VerifM.seq (do let _ ← compile Θ Δ_spec S [] TinyML.TyCtx.empty d.body; pure ()) (pure ())

/-- Verify all declarations in a program, accumulating specs as we go. -/
def Program.check (Θ : TinyML.TypeEnv) (Δ_spec : Signature) : SpecMap → Typed.Program Untyped.Expr → VerifM Unit
  | _, [] => pure ()
  | S, d :: ds => do
    match d.name.name, d.spec with
    | none, none =>
      ValDecl.checkExpr Θ Δ_spec S d
      Program.check Θ Δ_spec S ds
    | some n, none =>
    -- Named declaration without a spec: skip if it's a function definition
    -- (no code executes), otherwise check it. Erase any old spec for this
    -- name since the new binding shadows it.
      if d.body.isFunc then
        Program.check Θ Δ_spec (S.erase n) ds
      else
        ValDecl.checkExpr Θ Δ_spec S d
        Program.check Θ Δ_spec (S.erase n) ds
    | _, _ =>
      let spec ← ValDecl.check Θ Δ_spec S d
      let S' := match d.name.name with
        | some name => S.insert name spec
        | none => S
      Program.check Θ Δ_spec S' ds

/-- Initial signature threaded through program verification. -/
def Δ_spec : Signature := Signature.empty

/-- Initial verifier environment threaded through program verification. -/
def ρ_spec : VerifM.Env := VerifM.Env.empty

def Program.verify (prog : Untyped.Program Untyped.Expr) : Smt.Strategy Smt.Strategy.Outcome :=
  VerifM.strategy do
    let (Θ, typed) ← Program.prepare prog
    Program.check Θ Δ_spec ∅ typed

/-! ## Correctness -/

theorem Program.prepare_correct (prog : Untyped.Program Untyped.Expr)
    (st : TransState) (ρ : VerifM.Env)
    {Q : (TinyML.TypeEnv × Typed.Program Untyped.Expr) → TransState → VerifM.Env → Prop}
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

theorem ValDecl.checkExpr_correct (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) (γ : Runtime.Subst)
    (hSwf : S.wfIn Δ_spec) (hΔwf : Δ_spec.wf) (hΔvars : Δ_spec.vars = [])
    (st : TransState) (ρ : VerifM.Env)
    (hΔspec : Δ_spec.Subset st.decls) (hρspec : VerifM.Env.agreeOn Δ_spec ρ_spec ρ)
    {Q : Unit → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (ValDecl.checkExpr Θ Δ_spec S d) st ρ Q) :
    (□ st.sl ρ ∗ S.satisfiedBy Θ Δ_spec ρ_spec γ ⊢ Φ) →
    □ st.sl ρ ∗ S.satisfiedBy Θ Δ_spec ρ_spec γ ⊢ wp (d.body.runtime.subst γ) (fun _ => Φ) := by
  intro Hent
  simp only [ValDecl.checkExpr] at heval
  have ⟨hinner, _⟩ := VerifM.eval_seq heval
  have hcompile := VerifM.eval_bind _ _ _ _ hinner
  have hcomp :=
    compile_correct d.body Θ iprop(□ st.sl ρ ∗ Φ) S [] TinyML.TyCtx.empty st ρ γ Δ_spec ρ_spec
    (fun x st' ρ' => VerifM.eval (pure ()) st' ρ' (fun _ _ _ => True))
    (fun _ => Φ)
    hcompile
    (fun _ _ h => by simp at h)
    (fun _ h => by simp at h)
    hSwf hΔwf hΔvars
    hΔspec
    hρspec
    (fun _ _ _ _ _ _ _ => by
      istart
      iintro ⟨_, _, Hctx⟩
      icases Hctx with ⟨_, HΦ⟩
      iexact HΦ)
  refine (BIBase.Entails.trans ?_ hcomp)
  istart
  iintro ⟨□Hsl, □Hspec⟩
  isplitl [Hsl]
  · iexact Hsl
  · isplitl []
    · iexact Hspec
    · isplitl []
      · iapply Bindings.typedSubst_nil
      · isplitl [Hsl]
        · iexact Hsl
        · iapply Hent
          isplitl [Hsl]
          · iexact Hsl
          · iexact Hspec

theorem ValDecl.check_correct (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) (γ : Runtime.Subst)
    (hSwf : S.wfIn Δ_spec) (hΔwf : Δ_spec.wf) (hΔvars : Δ_spec.vars = [])
    (st : TransState) (ρ : VerifM.Env)
    (hΔspec : Δ_spec.Subset st.decls) (hρspec : VerifM.Env.agreeOn Δ_spec ρ_spec ρ)
    {Q : Spec → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (ValDecl.check Θ Δ_spec S d) st ρ Q) :
    ∃ spec, spec.wfIn Δ_spec ∧
            (□ st.sl ρ ∗ S.satisfiedBy Θ Δ_spec ρ_spec γ ⊢ wp (d.body.runtime.subst γ) (fun v => spec.isPrecondFor Θ Δ_spec ρ_spec v)) ∧
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
        cases hwf : Spec.checkWf spec Δ_spec with
        | error msg =>
          simp only [hwf] at h3
          exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ h3)).elim
        | ok u =>
          simp only [hwf] at h3
          have h4 := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ h3)
          have hswf : spec.wfIn Δ_spec := Spec.checkWf_ok (by cases u; exact hwf)
          have ⟨hcheckSpec, hpure⟩ := VerifM.eval_seq h4
          exact ⟨spec, hswf,
            by
              have hcheck :=
                checkSpec_correct Θ S d.body spec γ Δ_spec ρ_spec
                  hswf hSwf hΔwf hΔvars st ρ hΔspec hρspec hcheckSpec
              refine BIBase.Entails.trans ?_ hcheck
              istart
              iintro ⟨□Hsl, □Hspec⟩
              isplitl [Hsl]
              · iexact Hsl
              · iexact Hspec,
                 VerifM.eval_ret hpure⟩

theorem Program.check_correct (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (S : SpecMap) (prog : Typed.Program Untyped.Expr) (γ : Runtime.Subst)
    (hSwf : S.wfIn Δ_spec) (hΔwf : Δ_spec.wf) (hΔvars : Δ_spec.vars = [])
    (st : TransState) (ρ : VerifM.Env)
    (hΔspec : Δ_spec.Subset st.decls) (hρspec : VerifM.Env.agreeOn Δ_spec ρ_spec ρ) :
    VerifM.eval (Program.check Θ Δ_spec S prog) st ρ (fun _ _ _ => True) →
    □ st.sl ρ ∗ S.satisfiedBy Θ Δ_spec ρ_spec γ ⊢ pwp ((Typed.Program.runtime prog).subst γ) := by
  induction prog generalizing S γ st ρ with
  | nil =>
    intro _
    simp only [Typed.Program.runtime, List.map_nil, Runtime.Program.subst, pwp]
    istart
    iintro _
    iemp_intro
  | cons d ds ih =>
    intro heval
    have hpwp_unfold : pwp ((Typed.Program.runtime (d :: ds)).subst γ) ⊣⊢
        wp (d.body.runtime.subst γ) (fun v =>
          pwp ((Typed.Program.runtime ds).subst (Runtime.Subst.updateBinder d.name.runtime v γ))) := by
      simp [Typed.Program.runtime, Typed.ValDecl.runtime,
        Runtime.Program.subst, Runtime.Decl.subst, Runtime.Program.subst_remove_update]
    refine BIBase.Entails.trans ?_ hpwp_unfold.2
    simp only [Program.check] at heval
    cases hname : d.name.name with
    | none =>
      -- unnamed: pwp continuation does not depend on `v`
      have hupd : ∀ v, Runtime.Subst.updateBinder d.name.runtime v γ = γ := by
        intro v; simp [Binder.runtime_of_name_none hname, Runtime.Subst.updateBinder]
      cases hspec : d.spec with
      | none =>
        -- unnamed, no spec
        simp only [hname, hspec] at heval
        have hbind := VerifM.eval_bind _ _ _ _ heval
        have ⟨_, hcont⟩ := VerifM.eval_seq hbind
        have hih := ih S γ hSwf st ρ hΔspec hρspec (VerifM.eval_ret hcont)
        have hwp := ValDecl.checkExpr_correct Θ Δ_spec ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec hbind hih
        refine hwp.trans (wp.mono ?_)
        intro v; rw [hupd v]; exact .rfl
      | some _ =>
        -- unnamed, with spec
        simp only [hname, hspec] at heval
        obtain ⟨spec, _, hwp, hcont⟩ :=
          ValDecl.check_correct Θ Δ_spec ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec (VerifM.eval_bind _ _ _ _ heval)
        have hih := ih S γ hSwf st ρ hΔspec hρspec hcont
        refine SpatialContext.wp_strengthen_persistent hwp ?_
        intro v
        rw [hupd v]
        exact wand_intro (sep_elim_l.trans hih)
    | some n =>
      have hname_rt : d.name.runtime = .named n := Binder.runtime_of_name_some hname
      have herase : S.eraseBinder d.name = S.erase n := by simp [SpecMap.eraseBinder, hname]
      have hinsert : ∀ s, S.insertBinder d.name s = S.insert n s := by
        intro s; simp [SpecMap.insertBinder, hname]
      have hupd : ∀ v, Runtime.Subst.updateBinder d.name.runtime v γ = γ.update n v := by
        intro v; simp [hname_rt, Runtime.Subst.updateBinder]
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
          have heval' : VerifM.eval (Program.check Θ Δ_spec (S.erase n) ds) st ρ (fun _ _ _ => True) := by
            convert heval
          have hih := ih (S.erase n) (γ.update n fval)
            (SpecMap.wfIn_erase hSwf) st ρ hΔspec hρspec heval'
          refine BIBase.Entails.trans ?_ hih
          istart
          iintro ⟨□Hsl, □Hspec⟩
          isplitl [Hsl]
          · iexact Hsl
          · iapply SpecMap.satisfiedBy_erase
            iexact Hspec
        · -- named, no spec, not a function
          have hbind := VerifM.eval_bind _ _ _ _ heval
          have ⟨_, hcont⟩ := VerifM.eval_seq hbind
          have hcont' : VerifM.eval (Program.check Θ Δ_spec (S.erase n) ds) st ρ (fun _ _ _ => True) :=
            VerifM.eval_ret hcont
          have hwp := ValDecl.checkExpr_correct Θ Δ_spec ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec hbind
            (Φ := iprop(emp)) (by istart; iintro _; iemp_intro)
          refine SpatialContext.wp_strengthen_persistent hwp ?_
          intro v
          rw [hupd v]
          have hih := ih (S.erase n) (γ.update n v) (SpecMap.wfIn_erase hSwf) st ρ hΔspec hρspec hcont'
          exact wand_intro (sep_elim_l.trans <| by
            refine BIBase.Entails.trans ?_ hih
            istart
            iintro ⟨□Hsl, □Hspec⟩
            isplitl [Hsl]
            · iexact Hsl
            · iapply SpecMap.satisfiedBy_erase
              iexact Hspec)
      | some _ =>
        simp only [hname, hspec] at heval
        obtain ⟨spec, hswf, hwp, hcont⟩ :=
          ValDecl.check_correct Θ Δ_spec ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec (VerifM.eval_bind _ _ _ _ heval)
        have hcont' : VerifM.eval (Program.check Θ Δ_spec (S.insert n spec) ds) st ρ (fun _ _ _ => True) := by
          convert hcont
        refine SpatialContext.wp_strengthen_persistent hwp ?_
        intro v
        rw [hupd v]
        have hih := ih (S.insert n spec) (γ.update n v)
          (SpecMap.wfIn_insert hSwf hswf) st ρ hΔspec hρspec hcont'
        have hstep : (□ st.sl ρ ∗ S.satisfiedBy Θ Δ_spec ρ_spec γ) ∗ spec.isPrecondFor Θ Δ_spec ρ_spec v ⊢
            pwp ((Typed.Program.runtime ds).subst (γ.update n v)) := by
          refine BIBase.Entails.trans ?_ hih
          istart
          iintro ⟨Hctx, Hpre⟩
          icases Hctx with ⟨□Hsl, □Hspec⟩
          isplitl [Hsl]
          · iexact Hsl
          · iapply SpecMap.satisfiedBy_insert_update
            isplitl [Hspec]
            · iexact Hspec
            · iexact Hpre
        exact wand_intro hstep

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
    have hholdsFor : TransState.holdsFor TransState.empty VerifM.Env.empty :=
      fun φ hφ => by simp [TransState.empty] at hφ
    have hwf : TransState.wf TransState.empty :=
      ⟨fun φ hφ => by simp [TransState.empty] at hφ,
       by simp [TransState.empty, Signature.empty, Signature.allNames],
       fun a ha => by simp [TransState.empty] at ha⟩
    have hverifM := VerifM.eval_of_translate
                      (do
                        let (Θ, typed) ← Program.prepare p
                        Program.check Θ Δ_spec ∅ typed)
                      TransState.empty VerifM.Env.empty ctx_mid hverif hholdsFor hwf
    have hbind := VerifM.eval_bind _ _ _ _ hverifM
    obtain ⟨Θ, typed, hrt, hcheck⟩ := Program.prepare_correct p TransState.empty VerifM.Env.empty hbind
    have hcorrect := Program.check_correct Θ Δ_spec ρ_spec ∅ typed Runtime.Subst.id
                       (SpecMap.empty_wfIn _)
                       (by simp [Δ_spec, Signature.wf_empty])
                       (by simp [Δ_spec, Signature.empty])
                       TransState.empty VerifM.Env.empty
                       (by
                         constructor <;> intro x hx <;> simp [Δ_spec] at hx)
                       (by
                         change VerifM.Env.agreeOn Signature.empty VerifM.Env.empty VerifM.Env.empty
                         exact ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩)
                       hcheck
    rw [Runtime.Program.subst_id] at hcorrect
    have hctx : (⊢ □ TransState.empty.sl VerifM.Env.empty ∗
        SpecMap.satisfiedBy Θ Δ_spec ρ_spec (∅ : SpecMap) Runtime.Subst.id) := by
      istart
      isplitl []
      · simp [TransState.sl, TransState.empty]
        imodintro
        iemp_intro
      · iapply SpecMap.empty_satisfiedBy
    simpa [hrt] using hctx.trans hcorrect
