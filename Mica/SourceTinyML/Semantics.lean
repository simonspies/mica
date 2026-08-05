-- SUMMARY: Semantics of atoms, assertions, and specifications, parametric in the value relation interpreting types.
import Mica.SourceTinyML.Assertions
import Mica.SourceTinyML.World
import Mica.SeparationLogic.Wp
import Mica.FOL.SpecFn

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

-- ---------------------------------------------------------------------------
-- Specifications
-- ---------------------------------------------------------------------------

namespace Spec

/-- Build an environment binding each argument name to its value, left-to-right.
    Later arguments shadow earlier ones with the same name. -/
def argsEnv (ρ : Env) : List String → List Runtime.Val → Env
  | [], _ | _, [] => ρ
  | name :: rest, v :: vs => argsEnv (ρ.updateConst .value name v) rest vs

/-- `f` satisfies the specification `s` at argument types `argTys` and result
    type `retTy`: applying it to arguments related at `argTys` and a proof of
    the precondition yields the postcondition, with the result related at
    `retTy`. Types are interpreted using `V` in world `W`.

    Both resource premises are guarded. That is what makes the predicate
    contractive in `V` — every occurrence of the value relation sits under the
    `later` — while leaving the conclusion unguarded, so a caller holding this
    predicate can use it directly. The guard is discharged by the function's own
    beta step: `isPrecondFor_fix` gets the premises back, unguarded, in the body.
    The argument count is a separate pure premise because the beta step needs it
    *before* the guard can be stripped. -/
def isPrecondFor (W : TinyML.World) (V : TinyML.ValueRelation)
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ)
    (f : Runtime.Val) (s : Spec TinyML.Typ) : iProp :=
  iprop(□ ∀ (ρ : Env) (Φ : Runtime.Val → iProp) (vs : List Runtime.Val),
      ⌜Env.agreeOn W.Δ_spec W.ρ_spec ρ⌝ -∗
      ⌜vs.length = argTys.length⌝ -∗
      ▷ TinyML.ValsRel V vs argTys -∗
        ▷ PredTrans.apply V (fun r => V r retTy -∗ Φ r) s.pred
          (argsEnv ρ s.args vs) -∗
        wp W.pctx (Runtime.Expr.app (.val f) (vs.map fun v => .val v)) Φ)

instance : Iris.BI.Persistent (isPrecondFor W V argTys retTy f s) := by
  unfold isPrecondFor
  infer_instance

/-- The specification predicate is non-expansive in the value relation. The
    argument relation occurs negatively and the result relation positively, so
    this is the strongest uniform statement available. -/
theorem isPrecondFor_ne {n : Nat} {W : TinyML.World} {V V' : TinyML.ValueRelation}
    (hV : V ≡{n}≡ V') (argTys : List TinyML.Typ) (retTy : TinyML.Typ)
    (f : Runtime.Val) (s : Spec TinyML.Typ) :
    s.isPrecondFor W V argTys retTy f ≡{n}≡ s.isPrecondFor W V' argTys retTy f := by
  unfold isPrecondFor
  refine intuitionistically_ne.ne (forall_ne fun ρ => forall_ne fun Φ => forall_ne fun vs => ?_)
  refine wand_ne.ne .rfl (wand_ne.ne .rfl
    (wand_ne.ne (later_ne.ne (TinyML.ValsRel.ne hV vs argTys)) (wand_ne.ne ?_ .rfl)))
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
  simp only [TinyML.Typ.substSpec, hlen]
  refine intuitionistically_congr
    (forall_congr fun ρ => forall_congr fun Φ => forall_congr fun vs => ?_)
  refine wand_congr .rfl (wand_congr .rfl
    (wand_congr (later_congr (TinyML.ValsRel.subst hV vs argTys)) (wand_congr ?_ .rfl)))
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
  refine intuitionistically_ne.ne (forall_ne fun ρ => forall_ne fun Φ => forall_ne fun vs => ?_)
  refine wand_ne.ne .rfl (wand_ne.ne .rfl (wand_ne.ne ?_ (wand_ne.ne ?_ .rfl)))
  · exact Iris.OFE.Contractive.distLater_dist (f := fun P : iProp => iprop(▷ P))
      fun m hm => TinyML.ValsRel.ne (hV m hm) vs argTys
  · exact Iris.OFE.Contractive.distLater_dist (f := fun P : iProp => iprop(▷ P))
      fun m hm => PredTrans.apply_ne (hV m hm)
        (fun r => wand_ne.ne ((hV m hm) r retTy) .rfl) s.pred _

end Spec
