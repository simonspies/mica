-- SUMMARY: Semantics of atoms, assertions, and specifications, parametric in the value relation interpreting types.
import Mica.SourceTinyML.WellFormedness
import Mica.SourceTinyML.Typed
import Mica.SourceTinyML.World
import Mica.SeparationLogic.Wp
import Mica.SourceTinyML.SpecFn

open Iris Iris.BI Iris.OFE

variable [MicaGS HasLC.hasLC Sig]

/-!
# Specification semantics

The Iris meaning of the assertion syntax in `Mica/SourceTinyML/Assertions.lean`,
up to `Spec.isPrecondFor`, the predicate saying that a runtime value satisfies a
specification.

Everything here is parametric in a `ValueRelation`, the interpretation of types
as predicates on runtime values. That parameter is what puts this file *below*
the logical relation rather than above it: a specified function type is
interpreted by `isPrecondFor` at the relation's own approximation, so the
specification semantics may not itself depend on the logical relation.

The verifier operations on the same syntax — `toItem`, `resolve`,
`assume`/`prove`, `call`/`implement` — and all well-formedness conditions and
correctness proofs live in `Mica/Verifier/`, above the logical relation, where
they instantiate `V := TinyML.ValHasType W`.
-/

namespace TinyML

/-- An interpretation of closed types as predicates on runtime values. Both
    the outer approximation of the recursive relation and the specification
    semantics range over these. -/
abbrev ValueRelation := Runtime.Val → Typ → iProp

/-- Pointwise lifting of a value relation to a list of values and types.
    Lists of different lengths are unrelated. -/
def ValsRel (V : ValueRelation) : List Runtime.Val → List Typ → iProp
  | [], []           => iprop(emp)
  | v :: vs, t :: ts => iprop(V v t ∗ ValsRel V vs ts)
  | _, _             => iprop(False)

omit [MicaGS HasLC.hasLC Sig] in
theorem ValsRel.persistent (V : ValueRelation) (hV : ∀ v t, Persistent (V v t)) :
    ∀ (vs : List Runtime.Val) (ts : List Typ), Persistent (ValsRel V vs ts)
  | [], [] => by unfold ValsRel; infer_instance
  | [], _ :: _ => by unfold ValsRel; infer_instance
  | _ :: _, [] => by unfold ValsRel; infer_instance
  | v :: vs, t :: ts => by
      have := hV v t
      have := ValsRel.persistent V hV vs ts
      unfold ValsRel; infer_instance

omit [MicaGS HasLC.hasLC Sig] in
/-- Related lists have equal lengths, for any value relation. -/
theorem ValsRel.length_eq {V : ValueRelation} :
    ∀ {vs : List Runtime.Val} {ts : List Typ},
      ValsRel V vs ts ⊢ iprop(⌜vs.length = ts.length⌝)
  | [], [] => by unfold ValsRel; exact pure_intro rfl
  | [], _ :: _ | _ :: _, [] => by unfold ValsRel; exact false_elim
  | v :: vs, t :: ts => by
      unfold ValsRel
      exact (sep_elim_right.trans (ValsRel.length_eq (vs := vs) (ts := ts))).trans
        (pure_mono (by simp))

omit [MicaGS HasLC.hasLC Sig] in
/-- The lifting is non-expansive in the value relation. -/
theorem ValsRel.ne {n : Nat} {V V' : ValueRelation} (hV : V ≡{n}≡ V') :
    ∀ (vs : List Runtime.Val) (ts : List Typ), ValsRel V vs ts ≡{n}≡ ValsRel V' vs ts
  | [], [] => Dist.rfl
  | [], _ :: _ | _ :: _, [] => Dist.rfl
  | v :: vs, t :: ts => by
      unfold ValsRel
      exact sep_ne.ne (hV v t) (ValsRel.ne hV vs ts)

/-! ### Instantiating the types a definition mentions

Each of the following says that a relation interpreting every type variable the
way `σ` instantiates it interprets a whole definition the way `σ` instantiates
*it*. They mirror the `_ne` lemmas above, at bi-entailment rather than at a step
index: nothing here needs the index, and the logical relation consumes
`isPrecondFor_subst` as an equivalence. -/

omit [MicaGS HasLC.hasLC Sig] in
theorem ValsRel.subst {V V' : ValueRelation} {σ : TyVar → Typ}
    (hV : ∀ v t, V' v t ⊣⊢ V v (Typ.subst σ t)) :
    ∀ (vs : List Runtime.Val) (ts : List Typ),
      ValsRel V' vs ts ⊣⊢ ValsRel V vs (ts.map (Typ.subst σ))
  | [], [] => .rfl
  | [], _ :: _ | _ :: _, [] => .rfl
  | v :: vs, t :: ts => by
      unfold ValsRel
      exact sep_congr (hV v t) (ValsRel.subst hV vs ts)

end TinyML

-- ---------------------------------------------------------------------------
-- Atoms
-- ---------------------------------------------------------------------------

/-- The Iris meaning of an atom: what it takes for the term it constrains to
    evaluate to the given sorted value. The spatial atoms `own`/`arr` are the
    only ones mentioning the value relation. -/
def Atom.eval (V : TinyML.ValueRelation) {τ : Srt} (p : Atom TinyML.Typ τ) (ρ : Env) : τ.denote → iProp :=
  match p with
  | isint t  => λ v => ⌜.int v = t.eval ρ⌝
  | isbool t => λ v => ⌜.bool v = t.eval ρ⌝
  | isinj tag arity t => λ v => ⌜.inj tag arity v = t.eval ρ⌝
  | own l ty => λ v => ∃ loc : Runtime.Location,
      ⌜l.eval ρ = .loc loc⌝ ∗ loc ↦ [v] ∗ V v ty
  | arr a ty => λ v => ∃ loc : Runtime.Location, ∃ vs : List Runtime.Val,
      ⌜a.eval ρ = .array vs.length loc⌝ ∗ ⌜v = .vec vs⌝ ∗ loc ↦ vs ∗
        V (.vec vs) (.vec ty)
  | rel name arg => λ v =>
    ⌜(SpecFn.isDefined name arg).eval ρ ∧ (SpecFn.call name arg).eval ρ = v⌝

/-- Atom semantics is non-expansive in the value relation. Only the spatial
    atoms mention it, and they do so under a separating conjunction. -/
theorem Atom.eval_ne {n : Nat} {V V' : TinyML.ValueRelation} (hV : V ≡{n}≡ V')
    (p : Atom TinyML.Typ τ) (ρ : Env) (v : τ.denote) :
    p.eval V ρ v ≡{n}≡ p.eval V' ρ v := by
  cases p with
  | isint _ => exact OFE.Dist.rfl
  | isbool _ => exact OFE.Dist.rfl
  | isinj _ _ _ => exact OFE.Dist.rfl
  | rel _ _ => exact OFE.Dist.rfl
  | own l ty =>
    simp only [Atom.eval]
    exact exists_ne fun _ => sep_ne.ne .rfl (sep_ne.ne .rfl (hV v ty))
  | arr a ty =>
    simp only [Atom.eval]
    exact exists_ne fun _ => exists_ne fun vs =>
      sep_ne.ne .rfl (sep_ne.ne .rfl (sep_ne.ne .rfl (hV (.vec vs) (.vec ty))))

/-- Atom semantics commutes with instantiating the types the atom mentions. -/
theorem Atom.eval_substTy {V V' : TinyML.ValueRelation} {σ : TinyML.TyVar → TinyML.Typ}
    (hV : ∀ v t, V' v t ⊣⊢ V v (TinyML.Typ.subst σ t))
    (p : Atom TinyML.Typ τ) (ρ : Env) (v : τ.denote) :
    p.eval V' ρ v ⊣⊢ (TinyML.Typ.substAtom σ p).eval V ρ v := by
  cases p with
  | isint _ => exact .rfl
  | isbool _ => exact .rfl
  | isinj _ _ _ => exact .rfl
  | rel _ _ => exact .rfl
  | own l ty =>
    simp only [Atom.eval, TinyML.Typ.substAtom]
    exact exists_congr fun _ => sep_congr .rfl (sep_congr .rfl (hV v ty))
  | arr a ty =>
    simp only [Atom.eval, TinyML.Typ.substAtom]
    exact exists_congr fun _ => exists_congr fun vs =>
      sep_congr .rfl (sep_congr .rfl (sep_congr .rfl (hV (.vec vs) (.vec ty))))

theorem Atom.eval_agreeOn {V : TinyML.ValueRelation} {p : Atom TinyML.Typ τ}
    {ρ ρ' : Env} {Δ : Signature} (v : τ.denote)
    (hwf : p.wfIn Δ) (hagree : Env.agreeOn Δ ρ ρ') : p.eval V ρ v ⊣⊢ p.eval V ρ' v := by
  cases p with
  | isint t  => simp [Atom.eval, Term.eval_agreeOn hwf hagree]
  | isbool t => simp [Atom.eval, Term.eval_agreeOn hwf hagree]
  | isinj tag arity t => simp [Atom.eval, Term.eval_agreeOn hwf hagree]
  | own l ty => simp [Atom.eval, Term.eval_agreeOn hwf hagree]
  | arr a ty => simp [Atom.eval, Term.eval_agreeOn hwf hagree]
  | rel name t =>
    simp only [Atom.eval]
    rw [(Formula.eval_agreeOn hwf.1 hagree),
        Term.eval_agreeOn hwf.2 hagree]
    exact .rfl

-- ---------------------------------------------------------------------------
-- Assertions
-- ---------------------------------------------------------------------------

def Assertion.pre (V : TinyML.ValueRelation) (Φ : α → Env → iProp) (m : Assertion TinyML.Typ α) (ρ : Env) : iProp :=
  (match m with
  | .ret a        => Φ a ρ
  | .assert φ k   => ⌜φ.eval ρ⌝ ∗ Assertion.pre V Φ k ρ
  | .let_ x t k   => let v := t.eval ρ; Assertion.pre V Φ k (ρ.updateConst x.sort x.name v)
  | .pred x p k   => ∃ (v : x.sort.denote), p.eval V ρ v ∗ Assertion.pre V Φ k (ρ.updateConst x.sort x.name v)
  | .ite φ kt ke  =>
      iprop((⌜φ.eval ρ⌝ -∗ Assertion.pre V Φ kt ρ) ∧
            (⌜¬ φ.eval ρ⌝ -∗ Assertion.pre V Φ ke ρ)))

def Assertion.post (V : TinyML.ValueRelation) {α} (Φ : α → Env → iProp) (m : Assertion TinyML.Typ α) (ρ : Env) : iProp :=
  match m with
  | .ret a        => Φ a ρ
  | .assert φ k   => ⌜φ.eval ρ⌝ -∗ Assertion.post V Φ k ρ
  | .let_ x t k   => let v := t.eval ρ; Assertion.post V Φ k (ρ.updateConst x.sort x.name v)
  | .pred x p k   => iprop(∀ (v : x.sort.denote),
      p.eval V ρ v -∗ Assertion.post V Φ k (ρ.updateConst x.sort x.name v))
  | .ite φ kt ke  =>
      iprop((⌜φ.eval ρ⌝ -∗ Assertion.post V Φ kt ρ) ∧
            (⌜¬ φ.eval ρ⌝ -∗ Assertion.post V Φ ke ρ))

/-- Both assertion semantics are non-expansive in the value relation and in the
    return continuation. The two are proved together because a predicate
    transformer nests a `post` inside the continuation of a `pre`. -/
theorem Assertion.pre_ne {n : Nat} {V V' : TinyML.ValueRelation}
    {Φ Φ' : α → Env → iProp}
    (hV : V ≡{n}≡ V') (hΦ : ∀ a ρ, Φ a ρ ≡{n}≡ Φ' a ρ) :
    ∀ (m : Assertion TinyML.Typ α) (ρ : Env),
      Assertion.pre V Φ m ρ ≡{n}≡ Assertion.pre V' Φ' m ρ := by
  intro m
  induction m with
  | ret a => exact fun ρ => hΦ a ρ
  | assert φ k ih => exact fun ρ => sep_ne.ne .rfl (ih ρ)
  | let_ x t k ih => exact fun ρ => ih _
  | pred x p k ih =>
    exact fun ρ => exists_ne fun v => sep_ne.ne (Atom.eval_ne hV p ρ v) (ih _)
  | ite φ kt ke iht ihe =>
    exact fun ρ => and_ne.ne (wand_ne.ne .rfl (iht ρ)) (wand_ne.ne .rfl (ihe ρ))

theorem Assertion.post_ne {n : Nat} {V V' : TinyML.ValueRelation}
    {Φ Φ' : α → Env → iProp}
    (hV : V ≡{n}≡ V') (hΦ : ∀ a ρ, Φ a ρ ≡{n}≡ Φ' a ρ) :
    ∀ (m : Assertion TinyML.Typ α) (ρ : Env),
      Assertion.post V Φ m ρ ≡{n}≡ Assertion.post V' Φ' m ρ := by
  intro m
  induction m with
  | ret a => exact fun ρ => hΦ a ρ
  | assert φ k ih => exact fun ρ => wand_ne.ne .rfl (ih ρ)
  | let_ x t k ih => exact fun ρ => ih _
  | pred x p k ih =>
    exact fun ρ => forall_ne fun v => wand_ne.ne (Atom.eval_ne hV p ρ v) (ih _)
  | ite φ kt ke iht ihe =>
    exact fun ρ => and_ne.ne (wand_ne.ne .rfl (iht ρ)) (wand_ne.ne .rfl (ihe ρ))

/-- A postcondition means at the instantiated relation what its instantiation
means at the original one. -/
theorem Assertion.post_subst {V V' : TinyML.ValueRelation}
    {σ : TinyML.TyVar → TinyML.Typ} {Φ Φ' : Unit → Env → iProp}
    (hV : ∀ v t, V' v t ⊣⊢ V v (TinyML.Typ.subst σ t))
    (hΦ : ∀ a ρ, Φ' a ρ ⊣⊢ Φ a ρ) :
    ∀ (m : Assertion TinyML.Typ Unit) (ρ : Env),
      Assertion.post V' Φ' m ρ ⊣⊢ Assertion.post V Φ (TinyML.Typ.substPost σ m) ρ := by
  intro m
  induction m with
  | ret a => exact fun ρ => hΦ a ρ
  | assert φ k ih => exact fun ρ => wand_congr .rfl (ih ρ)
  | let_ x t k ih => exact fun ρ => ih _
  | pred x p k ih =>
    exact fun ρ => forall_congr fun v => wand_congr (Atom.eval_substTy hV p ρ v) (ih _)
  | ite φ kt ke iht ihe =>
    exact fun ρ => and_congr (wand_congr .rfl (iht ρ)) (wand_congr .rfl (ihe ρ))

/-- The same for a predicate transformer, whose continuation is a
postcondition and so carries the substitution through `hΦ`. -/
theorem Assertion.pre_subst {V V' : TinyML.ValueRelation}
    {σ : TinyML.TyVar → TinyML.Typ} {Φ Φ' : Post TinyML.Typ → Env → iProp}
    (hV : ∀ v t, V' v t ⊣⊢ V v (TinyML.Typ.subst σ t))
    (hΦ : ∀ p ρ, Φ' p ρ ⊣⊢ Φ ⟨p.name, TinyML.Typ.substPost σ p.body⟩ ρ) :
    ∀ (m : PredTrans TinyML.Typ) (ρ : Env),
      Assertion.pre V' Φ' m ρ ⊣⊢ Assertion.pre V Φ (TinyML.Typ.substPredTrans σ m) ρ := by
  intro m
  induction m with
  | ret p => exact fun ρ => hΦ p ρ
  | assert φ k ih => exact fun ρ => sep_congr .rfl (ih ρ)
  | let_ x t k ih => exact fun ρ => ih _
  | pred x p k ih =>
    exact fun ρ => exists_congr fun v => sep_congr (Atom.eval_substTy hV p ρ v) (ih _)
  | ite φ kt ke iht ihe =>
    exact fun ρ => and_congr (wand_congr .rfl (iht ρ)) (wand_congr .rfl (ihe ρ))

theorem Assertion.pre_agreeOn (V : TinyML.ValueRelation) {m : Assertion TinyML.Typ α} {retWf : α → Signature → Prop}
    {Φ : α → Env → iProp} {ρ ρ' : Env} {Δ : Signature}
    (hwf : m.wfIn retWf Δ) (hagree : Env.agreeOn Δ ρ ρ')
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ ⊢ Φ a ρ₂) :
    Assertion.pre V Φ m ρ ⊢ Assertion.pre V Φ m ρ' := by
  induction m generalizing Δ ρ ρ' with
  | ret a => exact hΦ a Δ ρ ρ' hwf hagree
  | assert φ k ih =>
    obtain ⟨hφwf, hkwf⟩ := hwf
    simp only [Assertion.pre]
    istart
    iintro ⟨%hφ, Hk⟩
    isplitr
    · ipureintro
      exact (Formula.eval_agreeOn hφwf hagree).mp hφ
    · iapply (ih hkwf hagree)
      iexact Hk
  | let_ v t k ih =>
    obtain ⟨htwf, hkwf⟩ := hwf
    simp only [Assertion.pre]
    rw [← Term.eval_agreeOn htwf hagree]
    exact ih hkwf (Env.agreeOn_declVar hagree)
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    simp only [Assertion.pre]
    istart
    iintro ⟨%w, Hsep⟩
    iexists w
    iapply (sep_mono (Atom.eval_agreeOn w hpwf hagree).1
      (ih hkwf (Env.agreeOn_declVar hagree)))
    iexact Hsep
  | ite φ kt ke iht ihe =>
    obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
    simp only [Assertion.pre]
    apply BI.and_intro
    · apply BI.and_elim_l.trans
      iintro Hkt
      iintro Hφ
      have hφ : BIBase.Entails (⌜φ.eval ρ'⌝ : iProp) ⌜φ.eval ρ⌝ := by
        iintro %hφ
        ipureintro
        exact (Formula.eval_agreeOn hφwf hagree).mpr hφ
      iapply (iht hktwf hagree)
      iapply Hkt
      iapply hφ
      iapply Hφ
    · apply BI.and_elim_r.trans
      iintro Hke
      iintro Hnφ
      have hnφ : BIBase.Entails (⌜¬ φ.eval ρ'⌝ : iProp) ⌜¬ φ.eval ρ⌝ := by
        iintro %hnφ
        ipureintro
        exact mt (Formula.eval_agreeOn hφwf hagree).mp hnφ
      iapply (ihe hkewf hagree)
      iapply Hke
      iapply hnφ
      iapply Hnφ

theorem Assertion.post_agreeOn (V : TinyML.ValueRelation) {m : Assertion TinyML.Typ α} {retWf : α → Signature → Prop}
    {Φ : α → Env → iProp} {ρ ρ' : Env} {Δ : Signature}
    (hwf : m.wfIn retWf Δ) (hagree : Env.agreeOn Δ ρ ρ')
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ ⊢ Φ a ρ₂) :
    Assertion.post V Φ m ρ ⊢ Assertion.post V Φ m ρ' := by
  induction m generalizing Δ ρ ρ' with
  | ret a => exact hΦ a Δ ρ ρ' hwf hagree
  | assert φ k ih =>
    obtain ⟨hφwf, hkwf⟩ := hwf
    simp only [Assertion.post]
    iintro H
    iintro %hφ
    have hφ' : φ.eval ρ := (Formula.eval_agreeOn hφwf hagree).mpr hφ
    iapply (ih hkwf hagree)
    iapply H
    ipureintro
    exact hφ'
  | let_ v t k ih =>
    obtain ⟨htwf, hkwf⟩ := hwf
    simp only [Assertion.post]
    rw [← Term.eval_agreeOn htwf hagree]
    exact ih hkwf (Env.agreeOn_declVar hagree)
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    simp only [Assertion.post]
    iintro H
    iintro %w Hw
    iapply (ih hkwf (Env.agreeOn_declVar hagree))
    iapply H
    iapply (Atom.eval_agreeOn w hpwf hagree).2
    iexact Hw
  | ite φ kt ke iht ihe =>
    obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
    simp only [Assertion.post]
    apply BI.and_intro
    · apply BI.and_elim_l.trans
      iintro Hkt
      iintro %hφ
      have hφ' : φ.eval ρ := (Formula.eval_agreeOn hφwf hagree).mpr hφ
      iapply (iht hktwf hagree)
      iapply Hkt
      ipureintro
      exact hφ'
    · apply BI.and_elim_r.trans
      iintro Hke
      iintro %hnφ
      have hnφ' : ¬ φ.eval ρ := mt (Formula.eval_agreeOn hφwf hagree).mp hnφ
      iapply (ihe hkewf hagree)
      iapply Hke
      ipureintro
      exact hnφ'

-- ---------------------------------------------------------------------------
-- Predicate transformers
-- ---------------------------------------------------------------------------

def PredTrans.apply (V : TinyML.ValueRelation) (Φ : Runtime.Val → iProp) (m : PredTrans TinyML.Typ) (ρ : Env) : iProp :=
  Assertion.pre V (fun post ρ' =>
    BIBase.forall fun v : Runtime.Val =>
      Assertion.post V (fun () _ => Φ v) post.body (ρ'.updateConst .value post.name v)
  ) m ρ

/-- Applying a predicate transformer is non-expansive in the value relation and
    in the postcondition. -/
theorem PredTrans.apply_ne {n : Nat} {V V' : TinyML.ValueRelation}
    {Φ Φ' : Runtime.Val → iProp} (hV : V ≡{n}≡ V') (hΦ : ∀ v, Φ v ≡{n}≡ Φ' v)
    (m : PredTrans TinyML.Typ) (ρ : Env) :
    PredTrans.apply V Φ m ρ ≡{n}≡ PredTrans.apply V' Φ' m ρ :=
  Assertion.pre_ne hV
    (fun _ _ => forall_ne fun v => Assertion.post_ne hV (fun _ _ => hΦ v) _ _) m ρ

/-- Applying a predicate transformer commutes with instantiating the types it
mentions. -/
theorem PredTrans.apply_subst {V V' : TinyML.ValueRelation}
    {σ : TinyML.TyVar → TinyML.Typ} {Φ Φ' : Runtime.Val → iProp}
    (hV : ∀ v t, V' v t ⊣⊢ V v (TinyML.Typ.subst σ t)) (hΦ : ∀ v, Φ' v ⊣⊢ Φ v)
    (m : PredTrans TinyML.Typ) (ρ : Env) :
    PredTrans.apply V' Φ' m ρ ⊣⊢ PredTrans.apply V Φ (TinyML.Typ.substPredTrans σ m) ρ :=
  Assertion.pre_subst hV
    (fun _ _ => forall_congr fun v => Assertion.post_subst hV (fun _ _ => hΦ v) _ _) m ρ

theorem PredTrans.apply_agreeOn (V : TinyML.ValueRelation) {pt : PredTrans TinyML.Typ} {Φ : Runtime.Val → iProp}
    {ρ ρ' : Env} {Δ : Signature}
    (hwf : pt.wfIn Δ) (hagree : Env.agreeOn Δ ρ ρ') :
    PredTrans.apply V Φ pt ρ ⊢ PredTrans.apply V Φ pt ρ' := by
  unfold PredTrans.apply at ⊢
  apply Assertion.pre_agreeOn V hwf hagree
  intro ⟨postName, postBody⟩ Δ' ρ₁ ρ₂ hwf_post hagree_post
  apply forall_intro
  intro v
  exact (forall_elim v).trans <|
    Assertion.post_agreeOn V hwf_post
      (Env.agreeOn_declVar hagree_post)
      (fun _ _ _ _ _ _ => .rfl)

-- ---------------------------------------------------------------------------
-- Specifications
-- ---------------------------------------------------------------------------

namespace Spec

/-- Build an environment binding each argument name to its value, left-to-right.
    Later arguments shadow earlier ones with the same name. -/
def argsEnv (ρ : Env) : List String → List Runtime.Val → Env
  | [], _ | _, [] => ρ
  | name :: rest, v :: vs => argsEnv (ρ.updateConst .value name v) rest vs

omit [MicaGS HasLC.hasLC Sig] in
theorem argsEnv_append (ρ : Env) :
    ∀ (names names' : List String) (vs gs : List Runtime.Val), names.length = vs.length →
      argsEnv ρ (names ++ names') (vs ++ gs) = argsEnv (argsEnv ρ names vs) names' gs
  | [], _, [], _, _ => rfl
  | _ :: _, _, [], _, h => by simp at h
  | [], _, _ :: _, _, h => by simp at h
  | n :: ns, names', v :: vs, gs, h => by
      simp only [List.cons_append, argsEnv]
      exact argsEnv_append _ ns names' vs gs (by simpa using h)

/-- `f` satisfies the specification `s` at argument types `argTys` and result
    type `retTy`: applying it to arguments related at `argTys` and a proof of
    the precondition yields the postcondition, with the result related at
    `retTy`. Types are interpreted using `V` in world `W`.

    A ghost argument is related at the type its ghost parameter declares, the
    same way a run-time argument is related at the arrow's. Nothing distinguishes
    the two here: a ghost argument has no run-time footprint, but it still stands
    for a value of a type the specification may reason about.

    Every resource premise is guarded. That is what makes the predicate
    contractive in `V` — every occurrence of the value relation sits under the
    `later` — while leaving the conclusion unguarded, so a caller holding this
    predicate can use it directly. The guard is discharged by the function's own
    beta step: `isPrecondFor_fix` gets the premises back, unguarded, in the body.
    The argument count is a separate pure premise because the beta step needs it
    *before* the guard can be stripped. -/
def isPrecondFor (W : TinyML.World) (V : TinyML.ValueRelation)
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ)
    (f : Runtime.Val) (s : Spec TinyML.Typ) : iProp :=
  iprop(□ ∀ (ρ : Env) (Φ : Runtime.Val → iProp) (vs gs : List Runtime.Val),
      ⌜Env.agreeOn W.Δ_spec W.ρ_spec ρ⌝ -∗
      ⌜vs.length = argTys.length⌝ -∗
      ⌜gs.length = s.ghost.length⌝ -∗
      ▷ TinyML.ValsRel V vs argTys -∗
      ▷ TinyML.ValsRel V gs (s.ghost.map Prod.snd) -∗
        ▷ PredTrans.apply V (fun r => V r retTy -∗ Φ r) s.pred
          (argsEnv ρ s.allArgs (vs ++ gs)) -∗
        wp W.pctx (Runtime.Expr.app (.val f) (vs.map fun v => .val v)) Φ)

instance : Iris.BI.Persistent (isPrecondFor W V argTys retTy f s) := by
  unfold isPrecondFor
  infer_instance

/-- The ghost analogue of `isPrecondFor`: the specification `s` is realizable
    at argument types `argTys` and result type `retTy`, meaning that given
    arguments related at those types and a proof of the precondition, a value
    satisfying the postcondition exists. This is what a ghost function
    guarantees.

    Ghost code is erased, so there is no application left to take a step: where
    `isPrecondFor` concludes with the weakest precondition of the call, this
    concludes that a value exists. No premise is guarded, because there is no
    beta step to discharge a guard with. -/
def isGhostPrecondFor (W : TinyML.World) (V : TinyML.ValueRelation)
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ) (s : Spec TinyML.Typ) : iProp :=
  iprop(□ ∀ (ρ : Env) (Φ : Runtime.Val → iProp) (vs gs : List Runtime.Val),
      ⌜Env.agreeOn W.Δ_spec W.ρ_spec ρ⌝ -∗
      ⌜vs.length = argTys.length⌝ -∗
      ⌜gs.length = s.ghost.length⌝ -∗
      TinyML.ValsRel V vs argTys -∗
      TinyML.ValsRel V gs (s.ghost.map Prod.snd) -∗
      PredTrans.apply V (fun r => V r retTy -∗ Φ r) s.pred
        (argsEnv ρ s.allArgs (vs ++ gs)) -∗
      |==> ∃ v, Φ v)

instance : Iris.BI.Persistent (isGhostPrecondFor W V argTys retTy s) := by
  unfold isGhostPrecondFor
  infer_instance

/-- Use a realizable specification: an obligation held against every value the
    specification admits is discharged by the value it produces. -/
theorem isGhostPrecondFor.apply {W : TinyML.World} {V : TinyML.ValueRelation}
    {argTys : List TinyML.Typ} {retTy : TinyML.Typ} {s : Spec TinyML.Typ}
    {ρ : Env} {Φ : Runtime.Val → iProp} {vs gs : List Runtime.Val}
    (hρ : Env.agreeOn W.Δ_spec W.ρ_spec ρ)
    (hvs : vs.length = argTys.length) (hgs : gs.length = s.ghost.length) :
    isGhostPrecondFor W V argTys retTy s ∗ TinyML.ValsRel V vs argTys ∗
        TinyML.ValsRel V gs (s.ghost.map Prod.snd) ∗
        PredTrans.apply V (fun r => V r retTy -∗ Φ r) s.pred (argsEnv ρ s.allArgs (vs ++ gs)) ⊢
      |==> ∃ v, Φ v := by
  unfold isGhostPrecondFor
  istart
  iintro ⟨#Hr, Hvs, Hgs, H⟩
  ispecialize Hr $$ %ρ %Φ %vs %gs %hρ %hvs %hgs
  ispecialize Hr $$ Hvs
  ispecialize Hr $$ Hgs
  ispecialize Hr $$ H
  iexact Hr

/-- A ghost specification holds for arguments whose measure is below `k`.

    The measure is a natural number: a declaration whose written measure goes
    negative ranks those arguments at zero, and a call from rank zero is
    impossible, since a call must lower a nonnegative measure. -/
def isGhostPrecondForAt (W : TinyML.World) (V : TinyML.ValueRelation)
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ) (s : Spec TinyML.Typ)
    (μ : List Runtime.Val → List Runtime.Val → Nat) (k : Nat) : iProp :=
  iprop(□ ∀ (ρ : Env) (Φ : Runtime.Val → iProp) (vs gs : List Runtime.Val),
      ⌜Env.agreeOn W.Δ_spec W.ρ_spec ρ⌝ -∗
      ⌜vs.length = argTys.length⌝ -∗
      ⌜gs.length = s.ghost.length⌝ -∗
      ⌜μ vs gs < k⌝ -∗
      TinyML.ValsRel V vs argTys -∗
      TinyML.ValsRel V gs (s.ghost.map Prod.snd) -∗
      PredTrans.apply V (fun r => V r retTy -∗ Φ r) s.pred
        (argsEnv ρ s.allArgs (vs ++ gs)) -∗
      |==> ∃ v, Φ v)

instance : Iris.BI.Persistent (isGhostPrecondForAt W V argTys retTy s μ k) := by
  unfold isGhostPrecondForAt
  infer_instance

theorem isGhostPrecondForAt.apply {W : TinyML.World} {V : TinyML.ValueRelation}
    {argTys : List TinyML.Typ} {retTy : TinyML.Typ} {s : Spec TinyML.Typ}
    {μ : List Runtime.Val → List Runtime.Val → Nat} {k : Nat}
    {ρ : Env} {Φ : Runtime.Val → iProp} {vs gs : List Runtime.Val}
    (hρ : Env.agreeOn W.Δ_spec W.ρ_spec ρ)
    (hvs : vs.length = argTys.length) (hgs : gs.length = s.ghost.length)
    (hrank : μ vs gs < k) :
    isGhostPrecondForAt W V argTys retTy s μ k ∗ TinyML.ValsRel V vs argTys ∗
        TinyML.ValsRel V gs (s.ghost.map Prod.snd) ∗
        PredTrans.apply V (fun r => V r retTy -∗ Φ r) s.pred (argsEnv ρ s.allArgs (vs ++ gs)) ⊢
      |==> ∃ v, Φ v := by
  unfold isGhostPrecondForAt
  istart
  iintro ⟨#Hr, Hvs, Hgs, H⟩
  ispecialize Hr $$ %ρ %Φ %vs %gs %hρ %hvs %hgs %hrank
  ispecialize Hr $$ Hvs
  ispecialize Hr $$ Hgs
  ispecialize Hr $$ H
  iexact Hr

theorem isGhostPrecondForAt.mono {W : TinyML.World} {V : TinyML.ValueRelation}
    {argTys : List TinyML.Typ} {retTy : TinyML.Typ} {s : Spec TinyML.Typ}
    {μ : List Runtime.Val → List Runtime.Val → Nat} {j k : Nat} (hjk : j ≤ k) :
    isGhostPrecondForAt W V argTys retTy s μ k ⊢ isGhostPrecondForAt W V argTys retTy s μ j := by
  unfold isGhostPrecondForAt
  iintro #H
  imodintro
  iintro %ρ %Φ %vs %gs %hρ %hvs %hgs %hrank Hvs Hgs Hpred
  have hrank' : μ vs gs < k := by omega
  ispecialize H $$ %ρ %Φ %vs %gs %hρ %hvs %hgs %hrank' Hvs Hgs Hpred
  iexact H

/-- Every bound together is the unranked guarantee: any arguments are below
    one of them. -/
theorem isGhostPrecondForAt.forall_iff {W : TinyML.World} {V : TinyML.ValueRelation}
    {argTys : List TinyML.Typ} {retTy : TinyML.Typ} {s : Spec TinyML.Typ}
    (μ : List Runtime.Val → List Runtime.Val → Nat) :
    (iprop(∀ k, isGhostPrecondForAt W V argTys retTy s μ k)) ⊣⊢
      isGhostPrecondFor W V argTys retTy s := by
  constructor
  · unfold isGhostPrecondForAt isGhostPrecondFor
    iintro H
    ihave #H' := H
    imodintro
    iintro %ρ %Φ %vs %gs %hρ %hvs %hgs Hvs Hgs Hpred
    have hrank : μ vs gs < μ vs gs + 1 := by omega
    ispecialize H' $$ %(μ vs gs + 1) %ρ %Φ %vs %gs %hρ %hvs %hgs %hrank
      Hvs Hgs Hpred
    iexact H'
  · unfold isGhostPrecondForAt isGhostPrecondFor
    iintro #H
    iintro %k
    imodintro
    iintro %ρ %Φ %vs %gs %hρ %hvs %hgs %_ Hvs Hgs Hpred
    ispecialize H $$ %ρ %Φ %vs %gs %hρ %hvs %hgs Hvs Hgs Hpred
    iexact H

/-- Prove a ghost declaration by strong induction, with recursive guarantees
    available only below the current bound. -/
theorem isGhostPrecondFor.induction {W : TinyML.World} {V : TinyML.ValueRelation}
    {argTys : List TinyML.Typ} {retTy : TinyML.Typ} {s : Spec TinyML.Typ}
    (μ : List Runtime.Val → List Runtime.Val → Nat)
    (step : ∀ k : Nat,
      (∀ j < k, ⊢ isGhostPrecondForAt W V argTys retTy s μ j) →
      ⊢ isGhostPrecondForAt W V argTys retTy s μ k) :
    ⊢ isGhostPrecondFor W V argTys retTy s := by
  apply BIBase.Entails.trans ?_ (isGhostPrecondForAt.forall_iff μ).mp
  apply forall_intro
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih => exact step k ih

/-- The specification predicate is non-expansive in the value relation. The
    argument relation occurs negatively and the result relation positively, so
    this is the strongest uniform statement available. -/
theorem isPrecondFor_ne {n : Nat} {W : TinyML.World} {V V' : TinyML.ValueRelation}
    (hV : V ≡{n}≡ V') (argTys : List TinyML.Typ) (retTy : TinyML.Typ)
    (f : Runtime.Val) (s : Spec TinyML.Typ) :
    s.isPrecondFor W V argTys retTy f ≡{n}≡ s.isPrecondFor W V' argTys retTy f := by
  unfold isPrecondFor
  refine intuitionistically_ne.ne (forall_ne fun ρ => forall_ne fun Φ => forall_ne fun vs =>
    forall_ne fun gs => ?_)
  refine wand_ne.ne .rfl (wand_ne.ne .rfl (wand_ne.ne .rfl
    (wand_ne.ne (later_ne.ne (TinyML.ValsRel.ne hV vs argTys))
      (wand_ne.ne (later_ne.ne (TinyML.ValsRel.ne hV gs (s.ghost.map Prod.snd)))
        (wand_ne.ne ?_ .rfl)))))
  exact later_ne.ne (PredTrans.apply_ne hV (fun r => wand_ne.ne (hV r retTy) .rfl) s.pred _)

/-- A specification means at the instantiated relation what its instantiation
means at the original one: the arrow's argument and result types and every type
the specification itself mentions are substituted together. -/
theorem isPrecondFor_subst {W : TinyML.World} {V V' : TinyML.ValueRelation}
    {σ : TinyML.TyVar → TinyML.Typ}
    (hV : ∀ v t, V' v t ⊣⊢ V v (TinyML.Typ.subst σ t))
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ)
    (f : Runtime.Val) (s : Spec TinyML.Typ) :
    s.isPrecondFor W V' argTys retTy f ⊣⊢
      (TinyML.Typ.substSpec σ s).isPrecondFor W V (argTys.map (TinyML.Typ.subst σ))
        (TinyML.Typ.subst σ retTy) f := by
  unfold isPrecondFor
  have hlen : (argTys.map (TinyML.Typ.subst σ)).length = argTys.length := by simp
  simp only [TinyML.Typ.substSpec, hlen, Spec.allArgs, TinyML.Typ.substGhost_fst,
    TinyML.Typ.substGhost_length, TinyML.Typ.substGhost_snd]
  refine intuitionistically_congr
    (forall_congr fun ρ => forall_congr fun Φ => forall_congr fun vs => forall_congr fun gs => ?_)
  refine wand_congr .rfl (wand_congr .rfl (wand_congr .rfl
    (wand_congr (later_congr (TinyML.ValsRel.subst hV vs argTys))
      (wand_congr (later_congr (TinyML.ValsRel.subst hV gs (s.ghost.map Prod.snd)))
        (wand_congr ?_ .rfl)))))
  exact later_congr
    (PredTrans.apply_subst hV (fun r => wand_congr (hV r retTy) .rfl) s.pred _)

/-- Guarding both resource premises makes the specification predicate
    contractive in the value relation: every occurrence of `V` sits under a
    `later`. This is what lets the value relation interpret a specified function
    type by its own approximation. -/
theorem isPrecondFor_contractive {n : Nat} {W : TinyML.World}
    {V V' : TinyML.ValueRelation} (hV : Iris.OFE.DistLater n V V')
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ)
    (f : Runtime.Val) (s : Spec TinyML.Typ) :
    s.isPrecondFor W V argTys retTy f ≡{n}≡ s.isPrecondFor W V' argTys retTy f := by
  unfold isPrecondFor
  refine intuitionistically_ne.ne (forall_ne fun ρ => forall_ne fun Φ => forall_ne fun vs =>
    forall_ne fun gs => ?_)
  refine wand_ne.ne .rfl (wand_ne.ne .rfl (wand_ne.ne .rfl
    (wand_ne.ne ?_ (wand_ne.ne ?_ (wand_ne.ne ?_ .rfl)))))
  · exact Iris.OFE.Contractive.distLater_dist (f := fun P : iProp => iprop(▷ P))
      fun m hm => TinyML.ValsRel.ne (hV m hm) vs argTys
  · exact Iris.OFE.Contractive.distLater_dist (f := fun P : iProp => iprop(▷ P))
      fun m hm => TinyML.ValsRel.ne (hV m hm) gs (s.ghost.map Prod.snd)
  · exact Iris.OFE.Contractive.distLater_dist (f := fun P : iProp => iprop(▷ P))
      fun m hm => PredTrans.apply_ne (hV m hm)
        (fun r => wand_ne.ne ((hV m hm) r retTy) .rfl) s.pred _

omit [MicaGS HasLC.hasLC Sig] in
/-- `argsEnv` preserves `agreeOn`: if two envs agree on `Δ`,
    then after applying the same updates, they agree on `argVars args ++ Δ`. -/
theorem argsEnv_agreeOn {Δ : Signature} {ρ₁ ρ₂ : Env}
    (h : Env.agreeOn Δ ρ₁ ρ₂) :
    ∀ (args : List String) (vals : List Runtime.Val),
    args.length ≤ vals.length →
    Env.agreeOn (Δ.declVars (argVars args))
      (argsEnv ρ₁ args vals) (argsEnv ρ₂ args vals) := by
  intro args
  induction args generalizing Δ ρ₁ ρ₂ with
  | nil => intro vals _; simp only [argVars, List.map, argsEnv, Signature.declVars]; exact h
  | cons name rest ih =>
    intro vals hlen
    cases vals with
    | nil => simp at hlen
    | cons v vs =>
      simp only [argsEnv, argVars, List.map]
      simpa [Signature.declVars] using
        ih (Env.agreeOn_declVar h) vs (by simp [List.length] at hlen ⊢; omega)

end Spec

/-! ## Agreement of value relations

Two value relations that agree on the types well formed in `Δ` and `Θ` give the
same meaning to the atoms, assertions and specifications that mention only such
types. Arrows are the only types whose meaning depends on more than the type
environment and the assignment: a specification is read in the spec
environment, so two worlds must agree on the symbols it mentions. -/

namespace TinyML

/-- `R` and `R'` agree on the types well formed in `Δ` and `Θ`. -/
abbrev ValueRelation.agreeOn (Δ : Signature) (Θ : TypeEnv) (R R' : ValueRelation) : iProp :=
  iprop(∀ w u, ⌜Typ.wfIn Δ Θ u⌝ -∗ (R w u ∗-∗ R' w u))

omit [MicaGS HasLC.hasLC Sig] in
theorem ValueRelation.agreeOn_symm {Δ : Signature} {Θ : TypeEnv} {R R' : ValueRelation} :
    ValueRelation.agreeOn Δ Θ R R' ⊢ ValueRelation.agreeOn Δ Θ R' R := by
  simp only [ValueRelation.agreeOn, wandIff]
  iintro H %w %u %hu
  isplit
  · icases H $$ %w %u %hu with ⟨-, H2⟩
    iexact H2
  · icases H $$ %w %u %hu with ⟨H1, -⟩
    iexact H1

omit [MicaGS HasLC.hasLC Sig] in
/-- Relations that agree give a well-formed type the same values. -/
theorem ValueRelation.agreeOn_iff {Δ : Signature} {Θ : TypeEnv} {R R' : ValueRelation}
    (h : ⊢ ValueRelation.agreeOn Δ Θ R R') {t : Typ} (ht : Typ.wfIn Δ Θ t) (v : Runtime.Val) :
    R v t ⊣⊢ R' v t := by
  simp only [ValueRelation.agreeOn, wandIff] at h
  constructor
  · iintro Hv
    icases h $$ %v %t %ht with ⟨H1, -⟩
    iapply H1 $$ Hv
  · iintro Hv
    icases h $$ %v %t %ht with ⟨-, H2⟩
    iapply H2 $$ Hv

omit [MicaGS HasLC.hasLC Sig] in
theorem ValueRelation.agreeOn_symm_intuitionistically {Δ : Signature} {Θ : TypeEnv}
    {R R' : ValueRelation} :
    iprop(□ ValueRelation.agreeOn Δ Θ R R') ⊢ iprop(□ ValueRelation.agreeOn Δ Θ R' R) :=
  intuitionistically_mono ValueRelation.agreeOn_symm

section AgreeOn

variable {Δ : Signature} {Θ : TypeEnv} {V V' : ValueRelation}

omit [MicaGS HasLC.hasLC Sig] in
theorem ValueRelation.agreeOn_vals :
    ∀ (vs : List Runtime.Val) (ts : List Typ), (∀ t ∈ ts, Typ.wfIn Δ Θ t) →
      ⊢ □ ValueRelation.agreeOn Δ Θ V V' -∗ ValsRel V vs ts -∗ ValsRel V' vs ts
  | [], [], _ => by
      simp only [ValsRel]
      iintro _ H
      iexact H
  | v :: vs, t :: ts, h => by
      simp only [ValsRel]
      iintro #HR ⟨Hv, Hvs⟩
      isplitl [Hv]
      · icases HR $$ %v %t %(h t (.head _)) with ⟨H1, -⟩
        iapply H1 $$ Hv
      · iapply ValueRelation.agreeOn_vals vs ts (fun t ht => h t (.tail _ ht))
        · iexact HR
        · iexact Hvs
  | [], _ :: _, _ | _ :: _, [], _ => by
      simp only [ValsRel]
      iintro _ H
      iexact H

theorem ValueRelation.agreeOn_atom {τ : Srt}
    (p : Atom Typ τ) (hp : ∀ t ∈ p.types, Typ.wfIn Δ Θ t) (ρ : Env) (v : τ.denote) :
    ⊢ □ ValueRelation.agreeOn Δ Θ V V' -∗ p.eval V ρ v -∗ p.eval V' ρ v := by
  cases p with
  | isint _ | isbool _ | isinj _ _ _ | rel _ _ =>
    simp only [Atom.eval]
    iintro _ H
    iexact H
  | own l ty =>
    simp only [Atom.eval]
    iintro #HR ⟨%loc, %hl, Hpt, Hv⟩
    iexists loc
    isplitr
    · ipureintro
      exact hl
    isplitl [Hpt]
    · iexact Hpt
    · icases HR $$ %v %ty %(hp ty (.head _)) with ⟨H1, -⟩
      iapply H1 $$ Hv
  | arr a ty =>
    simp only [Atom.eval]
    iintro #HR ⟨%loc, %vs, %ha, %hv, Hpt, Hv⟩
    iexists loc, vs
    isplitr
    · ipureintro
      exact ha
    isplitr
    · ipureintro
      exact hv
    isplitl [Hpt]
    · iexact Hpt
    · icases HR $$ %(.vec vs) %(.vec ty) %(.vec (hp ty (.head _))) with ⟨H1, -⟩
      iapply H1 $$ Hv

theorem ValueRelation.agreeOn_post {ret : α → List Typ}
    {Φ Φ' : α → Env → iProp}
    (hΦ : ∀ a ρ, (∀ t ∈ ret a, Typ.wfIn Δ Θ t) →
      ⊢ □ ValueRelation.agreeOn Δ Θ V V' -∗ Φ a ρ -∗ Φ' a ρ) :
    ∀ (m : Assertion Typ α), (∀ t ∈ m.types ret, Typ.wfIn Δ Θ t) → ∀ ρ,
      ⊢ □ ValueRelation.agreeOn Δ Θ V V' -∗ Assertion.post V Φ m ρ -∗ Assertion.post V' Φ' m ρ := by
  intro m
  induction m with
  | ret a => exact fun h ρ => hΦ a ρ h
  | assert φ k ih =>
    intro h ρ
    simp only [Assertion.post]
    iintro #HR H %hφ
    iapply ih h ρ
    · iexact HR
    · iapply H
      ipureintro
      exact hφ
  | let_ x t k ih =>
    intro h ρ
    exact ih h _
  | pred x p k ih =>
    intro h ρ
    simp only [Assertion.types] at h
    simp only [Assertion.post]
    iintro #HR H %v Hp
    iapply ih (fun t ht => h t (List.mem_append_right _ ht)) _
    · iexact HR
    · iapply H
      iapply (ValueRelation.agreeOn_atom (V := V') (V' := V) p
        (fun t ht => h t (List.mem_append_left _ ht)) ρ v)
      · iapply ValueRelation.agreeOn_symm_intuitionistically
        iexact HR
      · iexact Hp
  | ite φ kt ke iht ihe =>
    intro h ρ
    simp only [Assertion.types] at h
    simp only [Assertion.post]
    iintro #HR H
    isplit
    · iintro %hφ
      icases H with ⟨H1, -⟩
      iapply iht (fun t ht => h t (List.mem_append_left _ ht)) ρ
      · iexact HR
      · iapply H1
        ipureintro
        exact hφ
    · iintro %hφ
      icases H with ⟨-, H2⟩
      iapply ihe (fun t ht => h t (List.mem_append_right _ ht)) ρ
      · iexact HR
      · iapply H2
        ipureintro
        exact hφ

theorem ValueRelation.agreeOn_pre {ret : α → List Typ}
    {Φ Φ' : α → Env → iProp}
    (hΦ : ∀ a ρ, (∀ t ∈ ret a, Typ.wfIn Δ Θ t) →
      ⊢ □ ValueRelation.agreeOn Δ Θ V V' -∗ Φ a ρ -∗ Φ' a ρ) :
    ∀ (m : Assertion Typ α), (∀ t ∈ m.types ret, Typ.wfIn Δ Θ t) → ∀ ρ,
      ⊢ □ ValueRelation.agreeOn Δ Θ V V' -∗ Assertion.pre V Φ m ρ -∗ Assertion.pre V' Φ' m ρ := by
  intro m
  induction m with
  | ret a => exact fun h ρ => hΦ a ρ h
  | assert φ k ih =>
    intro h ρ
    simp only [Assertion.pre]
    iintro #HR ⟨%hφ, H⟩
    isplitr
    · ipureintro
      exact hφ
    · iapply ih h ρ
      · iexact HR
      · iexact H
  | let_ x t k ih =>
    intro h ρ
    exact ih h _
  | pred x p k ih =>
    intro h ρ
    simp only [Assertion.types] at h
    simp only [Assertion.pre]
    iintro #HR ⟨%v, Hp, H⟩
    iexists v
    isplitl [Hp]
    · iapply (ValueRelation.agreeOn_atom p (fun t ht => h t (List.mem_append_left _ ht)) ρ v)
      · iexact HR
      · iexact Hp
    · iapply ih (fun t ht => h t (List.mem_append_right _ ht)) _
      · iexact HR
      · iexact H
  | ite φ kt ke iht ihe =>
    intro h ρ
    simp only [Assertion.types] at h
    simp only [Assertion.pre]
    iintro #HR H
    isplit
    · iintro %hφ
      icases H with ⟨H1, -⟩
      iapply iht (fun t ht => h t (List.mem_append_left _ ht)) ρ
      · iexact HR
      · iapply H1
        ipureintro
        exact hφ
    · iintro %hφ
      icases H with ⟨-, H2⟩
      iapply ihe (fun t ht => h t (List.mem_append_right _ ht)) ρ
      · iexact HR
      · iapply H2
        ipureintro
        exact hφ

theorem ValueRelation.agreeOn_apply {Φ Φ' : Runtime.Val → iProp}
    (hΦ : ∀ v, ⊢ □ ValueRelation.agreeOn Δ Θ V V' -∗ Φ v -∗ Φ' v)
    (m : PredTrans Typ) (hm : ∀ t ∈ m.types fun post => post.body.types fun _ => [], Typ.wfIn Δ Θ t)
    (ρ : Env) :
    ⊢ □ ValueRelation.agreeOn Δ Θ V V' -∗ PredTrans.apply V Φ m ρ -∗ PredTrans.apply V' Φ' m ρ := by
  unfold PredTrans.apply
  refine ValueRelation.agreeOn_pre (fun post ρ' hpost => ?_) m hm ρ
  iintro #HR H %v
  iapply (ValueRelation.agreeOn_post (ret := fun _ => [])
    (fun _ _ _ => hΦ v) post.body hpost)
  · iexact HR
  · iexact H

end AgreeOn

variable {W₀ W₁ W₂ : World} {V V' : ValueRelation}

/-- Two worlds that extend `W₀` read a specification well formed in `W₀` at the
    same arguments alike: the first at its own spec environment, the second at
    any environment that agrees with its own. -/
private theorem Spec.apply_argsEnv_iff (h₁ : W₀.Subset W₁) (h₂ : W₀.Subset W₂)
    {s : Spec Typ} (hs : s.wfIn W₀.Δ_spec) {ρ : Env} (hρ : Env.agreeOn W₂.Δ_spec W₂.ρ_spec ρ)
    (V : ValueRelation) (Φ : Runtime.Val → iProp) {vs : List Runtime.Val}
    (hvs : s.allArgs.length ≤ vs.length) :
    PredTrans.apply V Φ s.pred (Spec.argsEnv W₁.ρ_spec s.allArgs vs) ⊣⊢
      PredTrans.apply V Φ s.pred (Spec.argsEnv ρ s.allArgs vs) := by
  have hag : Env.agreeOn W₀.Δ_spec W₁.ρ_spec ρ :=
    Env.agreeOn_trans (Env.agreeOn_symm h₁.agree)
      (Env.agreeOn_trans h₂.agree (Env.agreeOn_mono h₂.signature hρ))
  have hargs := Spec.argsEnv_agreeOn hag s.allArgs vs hvs
  exact ⟨PredTrans.apply_agreeOn V hs hargs, PredTrans.apply_agreeOn V hs (Env.agreeOn_symm hargs)⟩

omit [MicaGS HasLC.hasLC Sig] in
/-- The result premise of a call, read at relations that agree. -/
private theorem ValueRelation.agreeOn_ret {ret : Typ} (hret : Typ.wfIn W₀.Δ_spec W₀.Θ ret)
    (Φ : Runtime.Val → iProp) (r : Runtime.Val) :
    ⊢ □ ValueRelation.agreeOn W₀.Δ_spec W₀.Θ V' V -∗ (V' r ret -∗ Φ r) -∗ (V r ret -∗ Φ r) := by
  iintro #HR' Hw Hv
  iapply Hw
  icases HR' $$ %r %ret %hret with ⟨-, H2⟩
  iapply H2 $$ Hv

/-- Two worlds that extend `W₀` read alike a specified arrow well formed in `W₀`. -/
theorem ValueRelation.agreeOn_isPrecondFor (h₁ : W₀.Subset W₁) (h₂ : W₀.Subset W₂)
    {args : List Typ} {ret : Typ} {s : Spec Typ}
    (hT : Typ.wfIn W₀.Δ_spec W₀.Θ (.arrow args ret (some s))) (f : Runtime.Val) :
    ⊢ □ ▷ ValueRelation.agreeOn W₀.Δ_spec W₀.Θ V V' -∗
      Spec.isPrecondFor W₁ V args ret f s -∗ Spec.isPrecondFor W₂ V' args ret f s := by
  obtain _ | _ | _ | _ | _ | ⟨hargs, hret, hs, hlen, htys⟩ := hT
  unfold Spec.isPrecondFor
  iintro #HR #H
  imodintro
  iintro %ρ %Φ %vs %gs %hρ %hvs %hgs Hvs Hgs Hpred
  have heq := Spec.apply_argsEnv_iff h₁ h₂ hs hρ V (fun r => V r ret -∗ Φ r) (vs := vs ++ gs)
    (by simp [Spec.allArgs, hvs, hgs, hlen])
  rw [h₂.pctx, ← h₁.pctx]
  iapply H $$ %W₁.ρ_spec %Φ %vs %gs %Env.agreeOn_refl %hvs %hgs [Hvs] [Hgs] [Hpred]
  · inext
    iapply ValueRelation.agreeOn_vals vs args hargs
    · iapply ValueRelation.agreeOn_symm_intuitionistically
      iexact HR
    · iexact Hvs
  · inext
    iapply ValueRelation.agreeOn_vals gs _ fun t ht => htys t (List.mem_append_left _ ht)
    · iapply ValueRelation.agreeOn_symm_intuitionistically
      iexact HR
    · iexact Hgs
  · inext
    iapply heq.2
    iapply ValueRelation.agreeOn_apply (V := V') (V' := V) (ValueRelation.agreeOn_ret hret Φ) s.pred
      fun t ht => htys t (List.mem_append_right _ ht)
    · iapply ValueRelation.agreeOn_symm_intuitionistically
      iexact HR
    · iexact Hpred

/-- The ghost analogue of `ValueRelation.agreeOn_isPrecondFor`. -/
theorem ValueRelation.agreeOn_isGhostPrecondFor (h₁ : W₀.Subset W₁) (h₂ : W₀.Subset W₂)
    {args : List Typ} {ret : Typ} {s : Spec Typ}
    (hT : Typ.wfIn W₀.Δ_spec W₀.Θ (.arrow args ret (some s))) :
    ⊢ □ ValueRelation.agreeOn W₀.Δ_spec W₀.Θ V V' -∗
      Spec.isGhostPrecondFor W₁ V args ret s -∗ Spec.isGhostPrecondFor W₂ V' args ret s := by
  obtain _ | _ | _ | _ | _ | ⟨hargs, hret, hs, hlen, htys⟩ := hT
  unfold Spec.isGhostPrecondFor
  iintro #HR #H
  imodintro
  iintro %ρ %Φ %vs %gs %hρ %hvs %hgs Hvs Hgs Hpred
  have heq := Spec.apply_argsEnv_iff h₁ h₂ hs hρ V (fun r => V r ret -∗ Φ r) (vs := vs ++ gs)
    (by simp [Spec.allArgs, hvs, hgs, hlen])
  iapply H $$ %W₁.ρ_spec %Φ %vs %gs %Env.agreeOn_refl %hvs %hgs [Hvs] [Hgs] [Hpred]
  · iapply ValueRelation.agreeOn_vals vs args hargs
    · iapply ValueRelation.agreeOn_symm_intuitionistically
      iexact HR
    · iexact Hvs
  · iapply ValueRelation.agreeOn_vals gs _ fun t ht => htys t (List.mem_append_left _ ht)
    · iapply ValueRelation.agreeOn_symm_intuitionistically
      iexact HR
    · iexact Hgs
  · iapply heq.2
    iapply ValueRelation.agreeOn_apply (V := V') (V' := V) (ValueRelation.agreeOn_ret hret Φ) s.pred
      fun t ht => htys t (List.mem_append_right _ ht)
    · iapply ValueRelation.agreeOn_symm_intuitionistically
      iexact HR
    · iexact Hpred

end TinyML

-- ---------------------------------------------------------------------------
-- Measures
-- ---------------------------------------------------------------------------

/-- The measure read where the specification's parameters stand for the
    arguments. A negative measure ranks at zero, from which no call is possible. -/
def Typed.Measure.denote (measure : Typed.Measure) (s : Spec TinyML.Typ) (ρ : Env)
    (vs gs : List Runtime.Val) : Nat :=
  (Term.eval (Spec.argsEnv ρ s.allArgs (vs ++ gs)) measure.term).toNat
