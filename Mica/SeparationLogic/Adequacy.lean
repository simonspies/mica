-- SUMMARY: Adequacy of the Mica weakest precondition: programs with a proven `pwp` never get stuck.
import Iris.ProgramLogic.Adequacy
import Mica.SeparationLogic.Wp

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

/-!
Adequacy connects a (ghost-state-parametric) `pwp` proof back to the
operational semantics: every execution of the program — folded into a single
expression by `Runtime.Program.expr` — from the empty heap reaches only
configurations that are values or can step.

The results here are unconditional theorems of the Iris instantiation. A `pwp`
produced by the verifier is connected to primitive calls through the
registry's per-intrinsic soundness proofs.
-/

section
variable [MicaGS HasLC.hasLC Sig]

/-- `pwp` of a program entails `wp` of its nested-let expression form. -/
theorem pwp.wp_expr {ctx : TinyML.PrimCtx} (p : Runtime.Program) :
    pwp ctx p ⊢ wp ctx p.expr (fun _ => (⌜True⌝ : iProp)) := by
  unfold pwp
  exact wp.mono fun _ => pure_intro trivial

end

/-- Adequacy of `wp`: a ghost-state-parametric `wp` proof yields Iris
    `adequate`: executions from any initial heap never get stuck, and
    terminal values satisfy the postcondition. -/
theorem wp.adequacy {ctx : TinyML.PrimCtx} (e : Runtime.Expr) (μ : TinyML.Heap)
    (φ : Runtime.Val → Prop)
    (Hwp : ∀ [MicaGS HasLC.hasLC Sig], ⊢ wp ctx e (fun v => (⌜φ v⌝ : iProp))) :
    adequate .NotStuck (show TinyML.LExpr ctx from e) μ (fun v _ => φ v) := by
  refine wp_adequacy (GF := Sig) .NotStuck _ _ _ ?_
  intro inst κs
  istart
  imod (genHeap_init (F := PNat) (GF := Sig) (H := TinyML.HeapF) μ) with ⟨%G, Hinterp, -, -⟩
  letI : MicaGS HasLC.hasLC Sig := { toInvGS_gen := inst, heap := G }
  imodintro
  iexists fun σ _ => genHeapInterp (F := PNat) (GF := Sig) (H := TinyML.HeapF) σ
  iexists fun _ => iprop(True)
  isplitl [Hinterp]
  · iexact Hinterp
  · exact wp_def (ctx := ctx) ▸ Hwp

/-- OpSem step sequences lift to Iris thread-pool executions (singleton
    thread pool; TinyML never forks). -/
theorem TinyML.Steps.erased {ctx : TinyML.PrimCtx} {e e' : Runtime.Expr}
    {μ μ' : TinyML.Heap} (h : TinyML.Steps ctx e μ e' μ') :
    ([show TinyML.LExpr ctx from e], μ) -·->ₜₚ* ([show TinyML.LExpr ctx from e'], μ') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih =>
    exact .head
      ⟨[], Language.Step.of_primStep (TinyML.Step.iff_primStep.mp hs) (t₁ := []) (t₂ := [])⟩
      ih

/-- Top-level adequacy: from a ghost-state-parametric `wp` proof establishing a
    postcondition `φ`, executions of the program's expression form from the empty
    heap (a) never get stuck — every reachable expression is a value or can step
    — and (b) whenever they reach a value, that value satisfies `φ`. This mirrors
    the two fields of Iris's `adequate` in Mica's own operational semantics. -/
theorem Runtime.Program.adequacy {ctx : TinyML.PrimCtx} {p : Runtime.Program}
    (φ : Runtime.Val → Prop)
    (Hwp : ∀ [MicaGS HasLC.hasLC Sig], ⊢ wp ctx p.expr (fun v => (⌜φ v⌝ : iProp)))
    {e' : Runtime.Expr} {μ' : TinyML.Heap}
    (hsteps : TinyML.Steps ctx p.expr ∅ e' μ') :
    ((∃ v, e' = .val v) ∨ ∃ e'' μ'', TinyML.Step ctx e' μ' e'' μ'') ∧
      (∀ v, e' = .val v → φ v) := by
  have had : adequate .NotStuck (show TinyML.LExpr ctx from p.expr) ∅ (fun v _ => φ v) :=
    wp.adequacy _ _ _ (by intro inst; exact Hwp)
  refine ⟨?_, ?_⟩
  · have hns := had.adequate_not_stuck _ _ _ rfl hsteps.erased (List.mem_singleton.mpr rfl)
    rcases hns with hval | ⟨obs, e'', σ'', eₜ, hps⟩
    · left
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hval
      exact ⟨v, TinyML.exprVal_eq_some hv⟩
    · right
      exact ⟨e'', σ'', TinyML.Step.of_primStep hps⟩
  · rintro v rfl
    exact had.adequate_result [] μ' v hsteps.erased
