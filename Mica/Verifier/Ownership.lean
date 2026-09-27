-- SUMMARY: Finding, consuming, and acquiring ownership of spatial atoms in the verifier state.
import Mica.Verifier.SpatialAtom
import Mica.Verifier.Monad

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]

-- ---------------------------------------------------------------------------
-- Spatial resolution (linear search over st.owns)
-- ---------------------------------------------------------------------------

/-- Walk a spatial context and return the index and stored value term at the
    first atom of kind `k` and type `ty` whose key the SMT solver can prove
    equal to `tq`. The returned index is into the input list; consumption is
    the caller's job. -/
def VerifM.findMatchIn (k : SpatialAtom.Kind) (tq : Term .value) (ty : TinyML.Typ) :
    SpatialContext → VerifM (Option (Nat × Term .value))
  | [] => pure none
  | a :: rest => do
      if a.kind == k && a.ty == ty then
        if ← VerifM.test (.eq .value tq a.key) then
          return some (0, a.val)
      return (← VerifM.findMatchIn k tq ty rest).map fun (n, v') => (n + 1, v')

/-- Search the current ownership context for an atom of kind `k` with key `tq`,
    returning its stored value term and consuming the matched entry from
    `st.owns`. -/
def VerifM.findMatch (k : SpatialAtom.Kind) (tq : Term .value) (ty : TinyML.Typ) :
    VerifM (Option (Term .value)) := do
  let owns ← VerifM.ctx (fun st => (st.owns, st.owns))
  match ← VerifM.findMatchIn k tq ty owns with
  | none => pure none
  | some (n, v) =>
      match SpatialContext.remove owns n with
      | none => VerifM.fatal "findMatch: returned index out of range"
      | some (_, rest) => do
          let _ ← VerifM.ctx (fun _ => ((), rest))
          pure (some v)

omit [MicaGS HasLC.hasLC Sig] in
/-- Correctness of `findMatchIn`: on a `some (n, v)` result, `remove ctx n`
    extracts an atom of kind `k` whose key the solver has proved equal to `tq`. -/
theorem VerifM.eval_findMatchIn {k : SpatialAtom.Kind} {tq : Term .value} {ty : TinyML.Typ}
    {ctx : SpatialContext} {st : TransState} {ρ : Env}
    {Q : Option (Nat × Term .value) → TransState → Env → Prop}
    (h : VerifM.eval (VerifM.findMatchIn k tq ty ctx) st ρ Q)
    (htq : tq.wfIn st.decls) (hctx : ctx.wfIn st.decls) :
    ∃ result,
      Q result st ρ ∧
      (∀ n v, result = some (n, v) →
        ∃ t rest,
          SpatialContext.remove ctx n = some (k.atom t v ty, rest) ∧
          Term.eval ρ tq = Term.eval ρ t) := by
  induction ctx generalizing Q with
  | nil =>
    simp only [VerifM.findMatchIn] at h
    refine ⟨none, VerifM.eval_ret h, ?_⟩
    intros n v hvr; simp at hvr
  | cons a ctx ih =>
    simp only [VerifM.findMatchIn] at h
    have hcons := (SpatialContext.wfIn_cons _ _ _).1 hctx
    have hrecurse :
        VerifM.eval
          (return (← VerifM.findMatchIn k tq ty ctx).map fun (n, v') => (n + 1, v'))
          st ρ Q →
        ∃ result,
          Q result st ρ ∧
          (∀ n v', result = some (n, v') →
            ∃ t' rest',
              SpatialContext.remove (a :: ctx) n = some (k.atom t' v' ty, rest') ∧
              Term.eval ρ tq = Term.eval ρ t') := by
      intro hrec
      have hb' := VerifM.eval_bind hrec
      obtain ⟨result', hres', hsome'⟩ := ih hb' hcons.2
      cases result' with
      | none =>
        simp at hres'
        refine ⟨none, VerifM.eval_ret hres', ?_⟩
        intros n' v' hnv; simp at hnv
      | some pair =>
        obtain ⟨n₀, v₀⟩ := pair
        simp at hres'
        refine ⟨some (n₀ + 1, v₀), VerifM.eval_ret hres', ?_⟩
        intros n' v' hnv
        simp at hnv
        obtain ⟨rfl, rfl⟩ := hnv
        obtain ⟨t', rest', hrem, heq⟩ := hsome' n₀ v₀ rfl
        refine ⟨t', a :: rest', ?_, heq⟩
        simp [SpatialContext.remove, hrem]
    split at h
    · -- the kind and type match, so ask the solver whether the keys are equal
      rename_i hmatch
      have hwfeq : (Formula.eq .value tq a.key).wfIn st.decls :=
        ⟨htq, SpatialAtom.wfIn.key hcons.1⟩
      have hb := VerifM.eval_bind h
      obtain ⟨b, hb_sound, hq⟩ := VerifM.eval_check hb hwfeq
      split at hq
      · -- the solver proved the keys equal
        rename_i hbtrue
        refine ⟨some (0, a.val), VerifM.eval_ret hq, ?_⟩
        intros n' v' hnv
        simp at hnv
        obtain ⟨rfl, rfl⟩ := hnv
        have heq : Term.eval ρ tq = Term.eval ρ a.key := by
          simpa [Formula.eval] using hb_sound hbtrue
        simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
        refine ⟨a.key, ctx, ?_, heq⟩
        simp [SpatialContext.remove, ← hmatch.1, ← hmatch.2]
      · exact hrecurse hq
    · -- the kind or type does not match, so skip the solver and keep searching
      exact hrecurse h

/-- Correctness of `findMatch` in CPS style: the caller supplies Iris-level
    continuations for the `some` and `none` branches. On `some v`, the
    postcondition state has the matched atom consumed from `st.owns`, and the
    caller receives its interpretation at key `tq` separately. -/
theorem VerifM.eval_findMatch (W : TinyML.World) {k : SpatialAtom.Kind}
    {tq : Term .value} {ty : TinyML.Typ}
    {st : TransState} {ρ : Env}
    {Q : Option (Term .value) → TransState → Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (VerifM.findMatch k tq ty) st ρ Q)
    (htq : tq.wfIn st.decls)
    (hsome : ∀ v st', Q (some v) st' ρ →
        st'.decls = st.decls → v.wfIn st.decls →
        SpatialAtom.interp W ρ (k.atom tq v ty) ∗ st'.sl W ρ ∗ R ⊢ Φ)
    (hnone : Q none st ρ → st.sl W ρ ∗ R ⊢ Φ) :
    st.sl W ρ ∗ R ⊢ Φ := by
  unfold VerifM.findMatch at h
  have hb := VerifM.eval_bind h
  have ⟨hk, howns, _, _⟩ := VerifM.eval_ctx hb
  have hst_eq : ({ st with owns := st.owns } : TransState) = st := rfl
  rw [hst_eq] at hk
  have hk' := hk howns
  have hb2 := VerifM.eval_bind hk'
  obtain ⟨result, hres, hprop⟩ := eval_findMatchIn hb2 htq howns
  cases result with
  | none =>
    simp at hres
    exact hnone (VerifM.eval_ret hres)
  | some pair =>
    obtain ⟨n, v⟩ := pair
    obtain ⟨t, rest, hrem, heq⟩ := hprop n v rfl
    have hrest_wf : SpatialContext.wfIn rest st.decls :=
      (SpatialContext.wfIn_remove howns hrem).2
    have hatom_wf : SpatialAtom.wfIn (k.atom t v ty) st.decls :=
      (SpatialContext.wfIn_remove howns hrem).1
    have hv_wf : v.wfIn st.decls := (SpatialAtom.atom_wfIn.1 hatom_wf).2
    simp [hrem] at hres
    have hb3 := VerifM.eval_bind hres
    have ⟨hk3, _, _, _⟩ := VerifM.eval_ctx hb3
    have hk3' := hk3 hrest_wf
    have hQ : Q (some v) { st with owns := rest } ρ := VerifM.eval_ret hk3'
    have hsplit := SpatialContext.interp_remove W ρ st.owns n _ _ hrem
    have hcong := SpatialAtom.congr W (k := k) (t := t) (t' := tq) (v := v) (v' := v)
      (ty := ty) heq.symm rfl
    -- goal: st.owns.interp ρ ∗ R ⊢ Φ
    -- st.owns.interp ρ ⊣⊢ (k.atom t v ty).interp ρ ∗ rest.interp ρ
    --                ⊣⊢ (k.atom tq v ty).interp ρ ∗ rest.interp ρ
    refine (Iris.BI.sep_mono hsplit.1 BIBase.Entails.rfl).trans ?_
    refine (Iris.BI.sep_mono (Iris.BI.sep_mono hcong.1 BIBase.Entails.rfl) BIBase.Entails.rfl).trans ?_
    refine Iris.BI.sep_assoc.1.trans ?_
    exact hsome v { st with owns := rest } hQ rfl hv_wf

/-- Like `findMatch`, but aborts with a fatal error if no matching atom is
    found in the current ownership context. -/
def VerifM.findMatchForce (k : SpatialAtom.Kind) (tq : Term .value) (ty : TinyML.Typ) :
    VerifM (Term .value) := do
  match ← VerifM.findMatch k tq ty with
  | some v => pure v
  | none => VerifM.fatal s!"no matching {k.print}"

/-- CPS correctness for `findMatchForce`: only a `some`-style continuation is
    required, since the `none` branch is discharged by the fatal error. -/
theorem VerifM.eval_findMatchForce (W : TinyML.World) {k : SpatialAtom.Kind}
    {tq : Term .value} {ty : TinyML.Typ}
    {st : TransState} {ρ : Env}
    {Q : Term .value → TransState → Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (VerifM.findMatchForce k tq ty) st ρ Q)
    (htq : tq.wfIn st.decls)
    (hsome : ∀ v st', Q v st' ρ →
        st'.decls = st.decls → v.wfIn st.decls →
        SpatialAtom.interp W ρ (k.atom tq v ty) ∗ st'.sl W ρ ∗ R ⊢ Φ) :
    st.sl W ρ ∗ R ⊢ Φ := by
  unfold VerifM.findMatchForce at h
  have hb := VerifM.eval_bind h
  refine eval_findMatch W (R := R) (Φ := Φ) hb htq ?_ ?_
  · intros v st' hQ hdecls hv
    simp at hQ
    exact hsome v st' (VerifM.eval_ret hQ) hdecls hv
  · intro hQ
    simp at hQ
    exact (VerifM.eval_fatal hQ).elim


-- ---------------------------------------------------------------------------
-- Acquisition (adding items to the context)
-- ---------------------------------------------------------------------------

/-- Assume a context item together with the pure facts implied by its
    interpretation, making them available to the solver. -/
def VerifM.acquire (item : CtxItem) : VerifM Unit := do
  VerifM.assume item
  VerifM.assumeAll item.facts

omit [MicaGS HasLC.hasLC Sig] in
/-- Correctness of `acquire`: the resulting state extends the input state by
    the item; its pure facts must hold in the current environment. -/
theorem VerifM.eval_acquire {item : CtxItem} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop}
    (h : VerifM.eval (VerifM.acquire item) st ρ Q)
    (hwf : item.wfIn st.decls)
    (hpure : item.purePart ρ)
    (hfacts : ∀ φ ∈ item.facts, φ.eval ρ) :
    ∃ st', st'.decls = st.decls ∧ st'.owns = (st.addItem item).owns ∧ Q () st' ρ := by
  unfold VerifM.acquire at h
  have hb := VerifM.eval_bind h
  have h1 := VerifM.eval_assume hb hwf hpure
  have hfacts_wf : ∀ φ ∈ item.facts, φ.wfIn (st.addItem item).decls := by
    have hdecls : (st.addItem item).decls = st.decls := by cases item <;> rfl
    rw [hdecls]
    exact CtxItem.facts_wfIn hwf
  obtain ⟨st', hdecls', howns', _hasserts', hq⟩ := VerifM.eval_assumeAll h1 hfacts_wf hfacts
  refine ⟨st', ?_, howns', hq⟩
  rw [hdecls']
  cases item <;> rfl

/-- CPS correctness for acquiring a spatial atom: the ownership context is
    extended by the atom, whose pure facts are justified from its
    interpretation. -/
theorem VerifM.eval_acquireSpatial (W : TinyML.World) {a : SpatialAtom}
    {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop} {R Φ : iProp}
    (h : VerifM.eval (VerifM.acquire (.spatial a)) st ρ Q)
    (hwf : a.wfIn st.decls)
    (hk : ∀ st', Q () st' ρ → st'.decls = st.decls → st'.owns = a :: st.owns →
      st'.sl W ρ ∗ R ⊢ Φ) :
    SpatialAtom.interp W ρ a ∗ st.sl W ρ ∗ R ⊢ Φ := by
  istart
  iintro ⟨Ha, Howns, HR⟩
  ihave Hfacts := SpatialAtom.interp_facts W a $$ Ha
  icases Hfacts with ⟨%hfacts, Ha⟩
  obtain ⟨st', hdecls, howns, hq⟩ := VerifM.eval_acquire h hwf trivial hfacts
  have howns' : st'.owns = a :: st.owns := howns
  iapply (hk st' hq hdecls howns')
  simp only [TransState.sl_eq, howns', SpatialContext.interp]
  iframe

