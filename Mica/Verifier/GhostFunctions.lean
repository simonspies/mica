-- SUMMARY: The ghost functions in scope: their types, the guard on the declaration being checked, and the specs they meet.
import Mica.SourceTinyML.Typed
import Mica.SourceTinyML.LogicalRelation

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]

/-- The guard on the declaration being checked: the measure a recursive call
    must lower, and the rank standing for it at the declaration's own arguments. -/
structure GhostFns.Guard where
  measure : Typed.Measure
  rank : Term .int

/-- Only the declaration being checked carries a guard. -/
structure GhostFns.Entry where
  ty : TinyML.Typ
  guard : Option GhostFns.Guard

/-- A ghost function has no value, so it has no `Bindings` entry, and the type a
    use site carries is checked against the entry rather than trusted. -/
abbrev GhostFns := List (TinyML.Var × GhostFns.Entry)

abbrev GhostFns.empty : GhostFns := []

/-- Ghost code is pure, so a declaration's proof is a side condition rather than
    a resource. The type assignment is quantified because a body that calls a
    ghost function is checked at each assignment. A guarded entry keeps the
    ranked guarantee only, which is what makes a recursive self-entry
    consistent. -/
def GhostFns.wellTyped (W : TinyML.World) (Δ : Signature) (ρ : Env) (Gf : GhostFns) : Prop :=
  ∀ (η : TinyML.SemTypeAssign) f argTys retTy s guard,
    Gf.lookup f = some ⟨.arrow argTys retTy (some s), guard⟩ →
      match guard with
      | none =>
        ⊢ Spec.isGhostPrecondFor { W with eta := η } (TinyML.ValHasType { W with eta := η })
            argTys retTy s
      | some g =>
        g.rank.wfIn Δ ∧
        g.measure.term.wfIn (W.Δ_spec.declVars (Spec.argVars s.allArgs)) ∧
        (⊢ Spec.isGhostPrecondForAt { W with eta := η } (TinyML.ValHasType { W with eta := η })
            argTys retTy s (g.measure.denote s W.ρ_spec) (Term.eval ρ g.rank).toNat)

theorem GhostFns.wellTyped.empty (W : TinyML.World) (Δ : Signature) (ρ : Env) :
    GhostFns.wellTyped W Δ ρ .empty :=
  fun _ _ _ _ _ _ h => by simp [GhostFns.empty] at h

omit [MicaGS HasLC.hasLC Sig] in
private theorem GhostFns.lookup_append (Gf Gf' : GhostFns) (x : TinyML.Var) :
    (Gf ++ Gf').lookup x = (Gf.lookup x).or (Gf'.lookup x) := by
  induction Gf with
  | nil => simp
  | cons p Gf ih =>
    rw [List.cons_append, List.lookup_cons, List.lookup_cons]
    split <;> simp [ih]

theorem GhostFns.wellTyped.append {W : TinyML.World} {Δ : Signature} {ρ : Env}
    {Gf Gf' : GhostFns} (h : GhostFns.wellTyped W Δ ρ Gf)
    (h' : GhostFns.wellTyped W Δ ρ Gf') :
    GhostFns.wellTyped W Δ ρ (Gf ++ Gf') := by
  intro η f argTys retTy s guard hlookup
  rw [GhostFns.lookup_append] at hlookup
  cases hf : Gf.lookup f with
  | some e => rw [hf] at hlookup; exact h η f argTys retTy s guard (hf.trans hlookup)
  | none => rw [hf] at hlookup; exact h' η f argTys retTy s guard hlookup

/-- A run-time declaration hides every earlier ghost declaration of its name. -/
def GhostFns.remove (Gf : GhostFns) (x : TinyML.Var) : GhostFns :=
  Gf.filter fun p => p.1 != x

omit [MicaGS HasLC.hasLC Sig] in
theorem GhostFns.mem_of_lookup {l : GhostFns} {f : TinyML.Var}
    {e : GhostFns.Entry} (h : l.lookup f = some e) : (f, e) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨g, e'⟩ := p
    by_cases hfg : f = g
    · subst hfg
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact .head _
    · have hne : (f == g) = false := by simpa using hfg
      rw [List.lookup, hne] at h
      exact .tail _ (ih h)

omit [MicaGS HasLC.hasLC Sig] in
theorem GhostFns.mem_remove {Gf : GhostFns} {x : TinyML.Var}
    {p : TinyML.Var × GhostFns.Entry} (h : p ∈ Gf.remove x) : p ∈ Gf :=
  (List.mem_filter.mp h).1

/-- Every entry has no guard and a type well formed in `Δ` and `Θ`. Such
    entries carry over to a larger world. -/
def GhostFns.wfIn (Δ : Signature) (Θ : TinyML.TypeEnv) (Gf : GhostFns) : Prop :=
  ∀ p ∈ Gf, p.2.guard = none ∧ TinyML.Typ.wfIn Δ Θ p.2.ty

omit [MicaGS HasLC.hasLC Sig] in
theorem GhostFns.wfIn_append {Δ : Signature} {Θ : TinyML.TypeEnv} {Gf Gf' : GhostFns}
    (h : Gf.wfIn Δ Θ) (h' : Gf'.wfIn Δ Θ) : (Gf ++ Gf').wfIn Δ Θ :=
  fun p hp => (List.mem_append.mp hp).elim (h p) (h' p)

omit [MicaGS HasLC.hasLC Sig] in
theorem GhostFns.wfIn_remove {Δ : Signature} {Θ : TinyML.TypeEnv} {Gf : GhostFns}
    (h : Gf.wfIn Δ Θ) (x : TinyML.Var) : (Gf.remove x).wfIn Δ Θ :=
  fun p hp => h p (GhostFns.mem_remove hp)

omit [MicaGS HasLC.hasLC Sig] in
theorem GhostFns.wfIn_mono {Δ Δ' : Signature} {Θ Θ' : TinyML.TypeEnv} {Gf : GhostFns}
    (h : Gf.wfIn Δ Θ) (hΔ : Δ.Subset Δ') (hwf : Δ'.wf)
    (hΘ : ∀ T d, Θ T = some d → Θ' T = some d) : Gf.wfIn Δ' Θ' :=
  fun p hp => ⟨(h p hp).1, TinyML.Typ.wfIn_mono hΔ hwf hΘ (h p hp).2⟩

omit [MicaGS HasLC.hasLC Sig] in
@[simp] private theorem GhostFns.lookup_remove (Gf : GhostFns) (x y : TinyML.Var) :
    (Gf.remove x).lookup y = if y == x then none else Gf.lookup y := by
  induction Gf with
  | nil => simp [GhostFns.remove]
  | cons p Gf ih =>
    obtain ⟨z, entry⟩ := p
    by_cases hzx : z = x <;> by_cases hyz : y = z <;> by_cases hyx : y = x <;>
      simp_all [GhostFns.remove, List.lookup_cons] <;> aesop

theorem GhostFns.wellTyped.remove {W : TinyML.World} {Δ : Signature} {ρ : Env}
    {Gf : GhostFns} (h : GhostFns.wellTyped W Δ ρ Gf) (x : TinyML.Var) :
    GhostFns.wellTyped W Δ ρ (Gf.remove x) := by
  intro η f argTys retTy s guard hlookup
  rw [GhostFns.lookup_remove] at hlookup
  split at hlookup
  · contradiction
  · exact h η f argTys retTy s guard hlookup

theorem GhostFns.wellTyped.step {W : TinyML.World} {Δ Δ' : Signature} {ρ ρ' : Env}
    {Gf : GhostFns} (h : GhostFns.wellTyped W Δ ρ Gf)
    (hΔ : Δ.Subset Δ') (hρ : Env.agreeOn Δ ρ ρ') (hwf : Δ'.wf) :
    GhostFns.wellTyped W Δ' ρ' Gf := by
  intro η f argTys retTy s guard hlookup
  have h := h η f argTys retTy s guard hlookup
  cases guard with
  | none => exact h
  | some g =>
    obtain ⟨hrank, hmwf, hreal⟩ := h
    exact ⟨Term.wfIn_mono _ hrank hΔ hwf, hmwf,
      Term.eval_agreeOn hrank hρ ▸ hreal⟩

/-- Strong induction on the rank. The type assignment is quantified inside the
    induction because a recursive call is checked at every one of them. -/
theorem Spec.isGhostPrecondFor.induction_eta {W : TinyML.World}
    {argTys : List TinyML.Typ} {retTy : TinyML.Typ} {s : Spec TinyML.Typ}
    (μ : List Runtime.Val → List Runtime.Val → Nat)
    (step : ∀ (k : Nat) (η : TinyML.SemTypeAssign),
      (∀ j < k, ∀ η', ⊢ Spec.isGhostPrecondForAt { W with eta := η' }
          (TinyML.ValHasType { W with eta := η' }) argTys retTy s μ j) →
      ⊢ Spec.isGhostPrecondForAt { W with eta := η } (TinyML.ValHasType { W with eta := η })
          argTys retTy s μ k)
    (η : TinyML.SemTypeAssign) :
    ⊢ Spec.isGhostPrecondFor { W with eta := η } (TinyML.ValHasType { W with eta := η })
        argTys retTy s := by
  have key : ∀ (k : Nat) (η : TinyML.SemTypeAssign),
      ⊢ Spec.isGhostPrecondForAt { W with eta := η } (TinyML.ValHasType { W with eta := η })
          argTys retTy s μ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih => exact fun η => step k η fun j hj η' => ih j hj η'
  exact BIBase.Entails.trans (forall_intro fun k => key k η)
    (Spec.isGhostPrecondForAt.forall_iff μ).mp

theorem GhostFns.wellTyped.eta {W : TinyML.World} {Δ : Signature} {ρ : Env}
    {Gf : GhostFns} {η : TinyML.SemTypeAssign}
    (h : GhostFns.wellTyped W Δ ρ Gf) :
    GhostFns.wellTyped { W with eta := η } Δ ρ Gf :=
  fun η' => h η'

open TinyML in
/-- Unguarded ghost functions whose types are well formed in the smaller of two
    worlds meet their specs in the larger one when they do in the smaller one. -/
theorem GhostFns.wellTyped_of_subset {W₀ W : World} (h : W₀.Subset W)
    (hΘ : TypeEnv.wfIn W₀.Δ_spec W₀.Θ) {Gf : GhostFns} {Δ Δ' : Signature} {ρ ρ' : Env}
    (hGf : Gf.wfIn W₀.Δ_spec W₀.Θ) (hwt : GhostFns.wellTyped W₀ Δ ρ Gf) :
    GhostFns.wellTyped W Δ' ρ' Gf := by
  intro η f argTys retTy s guard hl
  obtain ⟨hguard, hT⟩ := hGf _ (GhostFns.mem_of_lookup hl)
  cases hguard
  have h₀ := World.subset_refl { W₀ with eta := η }
  have h₁ := World.subset_withEta h η
  have hag := ValHasType.agreeOn h₀ h₁ hΘ
  have htr := ValueRelation.agreeOn_isGhostPrecondFor (V := ValHasType { W₀ with eta := η })
    (V' := ValHasType { W with eta := η }) h₀ h₁ hT
  show ⊢ Spec.isGhostPrecondFor { W with eta := η } (ValHasType { W with eta := η })
    argTys retTy s
  istart
  iapply htr
  · imodintro
    iapply hag
  · iapply hwt η f argTys retTy s none hl
