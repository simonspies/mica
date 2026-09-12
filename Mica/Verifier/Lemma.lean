-- SUMMARY: Facts kept out of the solver context, which a check takes into its query or publishes as a ghost function.
import Mica.Verifier.Bindings
import Mica.Verifier.Guard

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]

/-- What a withheld fact says. A check selects by description, not by producer. -/
inductive Lemma.Kind where
  | definingEquation (f : TinyML.Var)
  deriving DecidableEq, BEq, Repr

/-- A fact proved where it was produced and kept out of the solver context. -/
structure Lemma where
  kind : Lemma.Kind
  fact : Axiom

namespace Lemma

/-- The fact holds and mentions nothing beyond the signature. -/
def Sound (l : Lemma) (Δ : Signature) (ρ : Env) : Prop :=
  l.fact.formula.wfIn Δ ∧ l.fact.formula.eval ρ

omit [MicaGS HasLC.hasLC Sig] in
theorem Sound.mono {l : Lemma} {Δ Δ' : Signature} {ρ ρ' : Env}
    (h : l.Sound Δ ρ) (hs : Δ.Subset Δ') (ha : Env.agreeOn Δ ρ ρ') (hw : Δ'.wf) :
    l.Sound Δ' ρ' :=
  ⟨Formula.wfIn_mono _ h.1 hs hw, (Formula.eval_env_agree h.1 ha).mp h.2⟩

/-! ## Publication

A fact `∀ x. φ → ψ` becomes a ghost function of one argument. The call proves
`φ` at its argument and learns `ψ` there. Nothing quantified reaches the
query. -/

/-- Binding this name changes nothing the fact mentions: it is neither the
    bound variable nor a signature symbol. -/
private def resultName (Δ : Signature) (x : String) : String :=
  Fresh.freshName (x :: Δ.allNames) "result"

/-- The argument takes the name the quantifier binds, so `φ` and `ψ` speak
    about it. -/
private def instance_ (x result : String) (φ ψ : Formula) : Spec TinyML.Typ :=
  { args := [x], ghost := [],
    pred := .assert φ (.ret ⟨result, .assert ψ (.ret ())⟩) }

/-- Offer the fact as a ghost function of one argument. Only a quantified
    implication can be published. -/
def publish (l : Lemma) (Δ : Signature) (name : TinyML.Var) (ty : TinyML.Typ) :
    Except String (TinyML.Var × GhostFns.Entry) :=
  match l.fact.formula with
  | .forall_ x .value _ (.implies φ ψ) =>
      .ok (name, ⟨.arrow [ty] .unit (some (instance_ x (resultName Δ x) φ ψ)), none⟩)
  | _ => .error s!"the fact published as '{name}' is not a quantified implication"

omit [MicaGS HasLC.hasLC Sig] in
/-- The result binder is fresh, so adding it leaves the instance alone. -/
private theorem instance_eval {Δ : Signature} {ρ ρ' : Env} {x : String} {ps : List Pattern}
    {φ ψ : Formula} (hwf : (Formula.forall_ x .value ps (.implies φ ψ)).wfIn Δ)
    (hev : (Formula.forall_ x .value ps (.implies φ ψ)).eval ρ)
    (hag : Env.agreeOn Δ ρ ρ') (v r : Runtime.Val)
    (hφ : φ.eval (ρ'.updateConst .value x v)) :
    ψ.eval ((ρ'.updateConst .value x v).updateConst .value (resultName Δ x) r) := by
  have hres : resultName Δ x ∉ (Δ.declVar ⟨x, .value⟩).allNames := by
    have h := Fresh.freshName_not_in_avoid (x :: Δ.allNames) "result"
    simp only [List.mem_cons, not_or] at h
    exact Signature.not_mem_allNames_declVar h.2 h.1
  exact (Formula.eval_env_agree hwf.2.2 (Δ := Δ.declVar ⟨x, .value⟩)
    (Env.agreeOn_update_fresh_const (c := ⟨resultName Δ x, .value⟩) hres)).mp
    (((Formula.eval_env_agree hwf hag).mp hev) v hφ)

/-- A call proves the premise at its argument and gets the conclusion there. -/
theorem publish_wellTyped (W : TinyML.World) (Δ : Signature) (ρ : Env) {l : Lemma}
    {name : TinyML.Var} {ty : TinyML.Typ} {entry : TinyML.Var × GhostFns.Entry}
    (h : l.Sound W.Δ_spec W.ρ_spec) (hp : l.publish W.Δ_spec name ty = .ok entry) :
    GhostFns.wellTyped W Δ ρ [entry] := by
  obtain ⟨hwf, hev⟩ := h
  unfold publish at hp
  split at hp
  case h_2 => exact absurd hp (by simp)
  rename_i x ps φ ψ hform
  rw [hform] at hwf hev
  cases hp
  intro η f argTys retTy s guard hlookup
  by_cases hf : f = name
  · subst hf
    simp only [List.lookup, beq_self_eq_true, Option.some.injEq,
      GhostFns.Entry.mk.injEq] at hlookup
    obtain ⟨hty, hguard⟩ := hlookup
    cases hty; cases hguard
    unfold Spec.isGhostPrecondFor
    simp only [instance_, Spec.allArgs, PredTrans.apply, Assertion.pre, Assertion.post,
      List.map_nil, List.append_nil]
    istart
    imodintro
    iintro %ρ_call %Φ %vs %gs %hagree_call %hlen_vs %hlen_gs Hvals Hgvals Hpred
    obtain ⟨v₀, rfl⟩ : ∃ v₀, vs = [v₀] := by
      match vs, hlen_vs with
      | [v₀], _ => exact ⟨v₀, rfl⟩
    obtain rfl : gs = [] := List.eq_nil_of_length_eq_zero (by simpa [instance_] using hlen_gs)
    icases Hpred with ⟨%hφ, Hpred⟩
    imodintro
    iexists Runtime.Val.unit
    ispecialize Hpred $$ %Runtime.Val.unit
    ispecialize Hpred $$ %(instance_eval hwf hev hagree_call v₀ Runtime.Val.unit hφ)
    iapply Hpred
    iapply TinyML.ValHasType.unit_intro
  · have hne : (f == name) = false := by simpa using hf
    simp only [List.lookup, hne] at hlookup
    exact absurd hlookup (by simp)

end Lemma

abbrev Lemmas := List Lemma

namespace Lemmas

/-- The fact a declaration withholds: the defining equation of the function it
    declares. -/
def ofDeclaration (ls : Lemmas) : Option TinyML.Var → Option Lemma
  | none => none
  | some f => ls.find? fun l => l.kind == .definingEquation f

/-- What a declaration's own check takes into its query. -/
def enterDeclaration (ls : Lemmas) (f : Option TinyML.Var) : List Axiom :=
  match ls.ofDeclaration f with
  | none => []
  | some l => [l.fact]

def Sound (ls : Lemmas) (Δ : Signature) (ρ : Env) : Prop :=
  ∀ l ∈ ls, l.Sound Δ ρ

omit [MicaGS HasLC.hasLC Sig] in
theorem Sound.mono {ls : Lemmas} {Δ Δ' : Signature} {ρ ρ' : Env}
    (h : ls.Sound Δ ρ) (hs : Δ.Subset Δ') (ha : Env.agreeOn Δ ρ ρ') (hw : Δ'.wf) :
    ls.Sound Δ' ρ' :=
  fun l hl => (h l hl).mono hs ha hw

omit [MicaGS HasLC.hasLC Sig] in
theorem ofDeclaration_sound {ls : Lemmas} {Δ : Signature} {ρ : Env} {l : Lemma}
    {f : Option TinyML.Var} (h : ls.Sound Δ ρ) (hl : ls.ofDeclaration f = some l) :
    l.Sound Δ ρ := by
  cases f with
  | none => simp [ofDeclaration] at hl
  | some f => exact h l (List.mem_of_find?_eq_some (by simpa [ofDeclaration] using hl))

omit [MicaGS HasLC.hasLC Sig] in
theorem enterDeclaration_sound {ls : Lemmas} {Δ : Signature} {ρ : Env}
    (h : ls.Sound Δ ρ) (f : Option TinyML.Var) :
    ∀ ax ∈ ls.enterDeclaration f, ax.formula.wfIn Δ ∧ ax.formula.eval ρ := by
  intro ax hax
  unfold enterDeclaration at hax
  split at hax
  · simp at hax
  · rename_i l hl
    simp only [List.mem_singleton] at hax
    subst hax
    exact ofDeclaration_sound h hl

end Lemmas
