-- SUMMARY: Verification of whole programs, one declaration after the other, and program-level soundness.
import Mica.SeparationLogic.Adequacy
import Mica.Verifier.Declaration

open Verifier (State)

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]
open Verifier (Scope)

/-- Declare and check the declarations in order, each in the environment and
the scope the ones before it leave. -/
def Program.declareAndCheck :
    Verifier.Env → Scope → Untyped.Program Untyped.SpecBody → SeqM (Verifier.Env × Scope)
  | env, S, [] => pure (env, S)
  | env, S, d :: ds => do
    let (env', S') ← Verifier.Decl.declareAndCheck env S d
    Program.declareAndCheck env' S' ds

def Program.verify (reg : Verifier.Registry) (prog : Untyped.Program Untyped.SpecBody) :
    Smt.Strategy Smt.Strategy.Outcome :=
  SeqM.strategy do
    reg.introduceRegistry
    let Δ ← SeqM.decls
    let _ ← Program.declareAndCheck (Verifier.Env.initial reg Δ) Scope.empty prog
    pure ()

/-! ## Correctness -/

theorem Program.declareAndCheck_correct (prog : Untyped.Program Untyped.SpecBody) :
    ∀ (env : Verifier.Env) (S : Scope) (st : State) (ρ : _root_.Env) (γ : Runtime.Subst)
      {Q : Verifier.Env × Scope → State → _root_.Env → Prop},
      env.supportedBy st ρ → S.supportedBy env st ρ γ → S.ghostBindings = [] →
      st.owns = [] → st.decls.vars = [] →
      SeqM.eval (Program.declareAndCheck env S prog) st ρ Q →
      S.runtimeBindings.schemeSubst (env.world ρ) S.typingContext γ ⊢
        pwp env.registry.primCtx ((Untyped.Program.runtime prog).subst γ) := by
  induction prog with
  | nil =>
    intro env S st ρ γ Q _ _ _ _ _ _
    simp only [Untyped.Program.runtime, List.filterMap_nil, Runtime.Program.subst]
    refine BIBase.Entails.trans ?_ pwp_nil
    istart
    iintro _
    iempintro
  | cons d ds ih =>
    intro env S st ρ γ Q henv hS hG howns hvars heval
    simp only [Program.declareAndCheck] at heval
    have h := Verifier.Decl.declareAndCheck_correct henv hS hG howns hvars
      (SeqM.eval_bind heval) (Untyped.Program.runtime ds)
      (fun env' S' st' ρ' γ' h1 h2 hG' ho hv h3 h4 => h3 ▸ ih env' S' st' ρ' γ' h1 h2 hG' ho hv h4)
    have hrt : Untyped.Program.runtime (d :: ds) =
        d.runtime.toList ++ Untyped.Program.runtime ds := by
      cases hd : d.runtime <;> simp [Untyped.Program.runtime, hd]
    rw [hrt]
    exact h

omit [MicaGS HasLC.hasLC Sig] in
theorem Program.verify_correct (reg : Verifier.Registry)
    (hSound : Verifier.Registry.Sound reg) (p : Untyped.Program Untyped.SpecBody) :
    Smt.Strategy.checks (Program.verify reg p)
      (∀ [MicaGS HasLC.hasLC Sig], ⊢ pwp reg.primCtx (Untyped.Program.runtime p)) := by
  intro st' heval _inst
  have hrun := SeqM.strategy_correct heval _root_.Env.init State.init_holdsFor
  obtain ⟨st, ρ, _, hdep, hvars, howns, _, hstable, _, hcont⟩ :=
    Verifier.Registry.eval_introduceRegistry reg hSound (SeqM.eval_bind hrun)
  have hprog := SeqM.eval_bind (SeqM.eval_decls (SeqM.eval_bind hcont))
  have henv : (Verifier.Env.initial reg st.decls).supportedBy st ρ :=
    { sound := hSound
      signature := rfl
      specFunctionsWf := ⟨fun _ _ h => (List.not_mem_nil h).elim,
        fun _ _ h => (List.not_mem_nil h).elim⟩
      specFunctionsAgree := fun _ _ h => (List.not_mem_nil h).elim
      lemmas := by simp [Verifier.Env.initial, Lemmas.Sound]
      symbols := fun i hi =>
        (Verifier.Registry.extendWithSym_subset_sigOf_of_mem hi).trans hdep
      interpretations := fun i hi => hstable ρ Env.agreeOn_refl i hi
      types := fun _ _ h => by simp [Verifier.Env.initial, TinyML.TypeEnv.empty] at h }
  have hS : Scope.empty.supportedBy (Verifier.Env.initial reg st.decls) st ρ Runtime.Subst.id :=
    { closed := TinyML.TyCtx.empty_closed
      types := fun _ _ h => by simp [Scope.empty, TinyML.TyCtx.empty] at h
      ghostFnsWf := fun _ h => by simp [Scope.empty] at h
      ghostFns := GhostFunctions.wellTyped.empty _ _ _
      runtimeLinked := by intro x x' h; simp [Scope.empty] at h
      runtimeDeclared := by intro p hp; simp [Scope.empty] at hp }
  have h := Program.declareAndCheck_correct p _ _ st ρ _ henv hS rfl howns
    (by rw [hvars]; rfl) hprog
  rw [Runtime.Program.subst_id] at h
  exact (Bindings.schemeSubst_empty _ _ _).trans h

omit [MicaGS HasLC.hasLC Sig] in
/-- End-to-end adequacy: a successful verifier run guarantees that executions
    of the program — folded into a single expression by `Runtime.Program.expr`,
    starting from the empty heap — never get stuck: every reachable expression
    is a value or can step. Derived from `Program.verify_correct` through the
    `pwp`-to-`wp` bridge and `Runtime.Program.adequacy`. -/
theorem Program.verify_adequate (reg : Verifier.Registry)
    (hSound : Verifier.Registry.Sound reg) (p : Untyped.Program Untyped.SpecBody) :
    Smt.Strategy.checks (Program.verify reg p)
      (∀ {e' : Runtime.Expr} {μ' : TinyML.Heap},
        TinyML.Steps reg.primCtx (Untyped.Program.runtime p).expr ∅ e' μ' →
        (∃ v, e' = .val v) ∨ ∃ e'' μ'', TinyML.Step reg.primCtx e' μ' e'' μ'') :=
  (Program.verify_correct reg hSound p).imp fun Hpwp _ _ hsteps =>
    (Runtime.Program.adequacy (φ := fun _ => True)
      (by intro inst; exact Hpwp.trans (pwp.wp_expr _)) hsteps).1
