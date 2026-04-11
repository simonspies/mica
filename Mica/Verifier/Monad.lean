import Mica.Engine.Driver
import Mica.Verifier.Scoped
import Mica.Verifier.Utils
import Mica.Base.Fresh
import Mica.SeparationLogic.SpatialAtom


/-! ## Verification Monad

A free monad over verification-relevant SMT operations,
with branching (all/any) for exploring multiple verification paths. -/

inductive VerifError where
  /-- Recoverable failure: this verification path didn't work out.
      Can be caught by `any`. -/
  | failed : String → VerifError
  /-- Fatal error: something is fundamentally wrong (e.g. unimplemented feature).
      Always propagates. -/
  | fatal : String → VerifError

inductive VerifM : Type → Type 1 where
  | ret : α → VerifM α
  | bind : VerifM α → (α → VerifM β) → VerifM β
  /-- Declare a fresh SMT constant. -/
  | decl : Option String → Srt → VerifM FOL.Const
  /-- Add a formula to the assertion context (permanent, no check). -/
  | assume : Formula → VerifM Unit
  /-- Check whether φ is provable from the current context.
      Returns `true` if UNSAT (provable), `false` otherwise. Never fails. -/
  | check : Formula → VerifM Bool
  /-- Abort with a fatal error. -/
  | fatal : String → VerifM α
  /-- Abort with a recoverable failure. -/
  | failed : String → VerifM α
  /-- Execute all branches; succeed only if every branch succeeds. -/
  | all : List α → VerifM α
  /-- Try branches in order; succeed if any branch succeeds (non-fatally). -/
  | any : List α → VerifM α
  /-- Read the current assertion context. -/
  | ctx : (List Formula → α) → VerifM α
  /-- Run a scoped computation: declarations and assertions from the body
      are discarded after it completes. Only the return value is kept. -/
  | seq : VerifM Unit → VerifM β → VerifM β

instance : Monad VerifM where
  pure := VerifM.ret
  bind := VerifM.bind

/-- Assert-and-check: check φ is provable, fail if not. -/
def VerifM.assert (φ : Formula) : VerifM Unit := do
  if ← VerifM.check φ then pure ()
  else VerifM.failed s!"assertion failed"

/-- Check that two elaboration-time values match exactly, otherwise abort fatally. -/
def VerifM.expectEq [DecidableEq α] [Repr α] (msg : String) (actual expected : α) : VerifM Unit := do
  if actual = expected then pure ()
  else VerifM.fatal s!"{msg}: expected {repr expected}, got {repr actual}"

/-- Unwrap an `Option`, otherwise abort fatally. -/
def VerifM.expectSome (msg : String) (x : Option α) : VerifM α := do
  match x with
  | some x => pure x
  | none => VerifM.fatal msg

/-- Assume all formulas in a list via `VerifM.assume`. -/
def VerifM.assumeAll : List Formula → VerifM Unit
  | [] => pure ()
  | φ :: φs => do VerifM.assume φ; VerifM.assumeAll φs

/-! ### Translation to ScopedM -/

structure TransState where
  decls   : Signature
  asserts : Context
  owns    : SpatialContext

def TransState.toFlatCtx (st : TransState) : FlatCtx :=
  ⟨st.decls, st.asserts⟩

@[simp] theorem TransState.toFlatCtx_decls (st : TransState) :
    st.toFlatCtx.decls = st.decls := rfl

@[simp] theorem TransState.toFlatCtx_asserts (st : TransState) :
    st.toFlatCtx.asserts = st.asserts := rfl

@[simp] theorem TransState.toFlatCtx_addConst (st : TransState) (c : FOL.Const) :
    { st with decls := st.decls.addConst c }.toFlatCtx = st.toFlatCtx.addConst c.name c.sort := by
  simp [toFlatCtx, FlatCtx.addConst]

@[simp] theorem TransState.toFlatCtx_addAssert (st : TransState) (φ : Formula) :
    { st with asserts := φ :: st.asserts }.toFlatCtx = st.toFlatCtx.addAssert φ := by
  simp [toFlatCtx, FlatCtx.addAssert]

def TransState.empty : TransState := ⟨Signature.empty, [], []⟩

@[simp] theorem TransState.empty_toFlatCtx : TransState.empty.toFlatCtx = FlatCtx.empty := rfl

def TransState.holdsFor (st : TransState) (ρ : Env) := ∀ φ ∈ st.asserts, φ.eval ρ

theorem TransState.holdsFor_mono {st st' : TransState} {ρ : Env}
    (hsub : st.asserts ⊆ st'.asserts) (h : st'.holdsFor ρ) : st.holdsFor ρ :=
  fun φ hφ => h φ (hsub hφ)

structure TransState.wf (st : TransState) : Prop where
  assertsWf : st.asserts.wfIn st.decls
  namesDisjoint : st.decls.allNames.Nodup
  ownsWf : st.owns.wfIn st.decls

def TransState.freshConst (hint : Option String) (t : Srt) (st : TransState) : FOL.Const :=
  let base := hint.getD "_v"
  let x' := fresh (addNumbers base) st.decls.allNames
  ⟨x', t⟩

theorem TransState.freshConst.wf {hint t} (st : TransState) :
  TransState.wf st →
  TransState.wf { st with decls := st.decls.addConst (st.freshConst hint t) } := by
  intro hwf
  have hfresh : (st.freshConst hint t).name ∉ st.decls.allNames :=
    fresh_not_mem (addNumbers (hint.getD "_v")) st.decls.allNames (addNumbers_injective _)
  have hwf' := Signature.wf_addConst hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addConst _ _) hwf'
  · exact Signature.nodup_allNames_addConst hwf.namesDisjoint hfresh
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addConst _ _) hwf'

theorem TransState.addAssert.wf (st : TransState) :
  TransState.wf st →
  φ.wfIn st.decls →
  TransState.wf { st with asserts := φ :: st.asserts } := by
  intro hwf hφ
  constructor
  · intro ψ hψ
    simp only [List.mem_cons] at hψ
    rcases hψ with rfl | hψ
    · exact hφ
    · exact hwf.assertsWf ψ hψ
  · exact hwf.namesDisjoint
  · exact hwf.ownsWf


def TransCont α := α → TransState → ScopedM (Except VerifError Unit)

def translateAll (items : List α) (st : TransState) (k : TransCont (Except VerifError α)) :
    ScopedM (Except VerifError Unit) :=
  match items with
  | [] => ScopedM.ret (.ok ())
  | a :: rest =>
      .bracket (k (.ok a) st) (fun
        | .error e => ScopedM.ret (.error e)
        | .ok () => translateAll rest st k)

def translateAny (items : List α) (st : TransState) (k : TransCont (Except VerifError α)) :
    ScopedM (Except VerifError Unit) :=
  match items with
  | [] => k (.error (.failed "no alternative")) st
  | a :: rest =>
      .bracket (k (.ok a) st) (fun
        | .ok () => ScopedM.ret (.ok ())
        | .error (.failed _) => translateAny rest st k
        | .error (.fatal msg) => ScopedM.ret (.error (.fatal msg)))

def VerifM.translate :
  VerifM α → TransState → TransCont (Except VerifError α) →
  ScopedM (Except VerifError Unit)
  | .ret a, st, k => k (.ok a) st
  | .bind m f, st, k =>
      m.translate st fun
        | (.ok a), st' => (f a).translate st' k
        | (.error e), st' => k (.error e) st'
  | .decl hint t, st, k =>
      let c := st.freshConst hint t
      .declareConst c.name t (fun () =>
        k (.ok c) { st with decls := st.decls.addConst c })
  | .assume φ, st, k =>
      ScopedM.assert φ (fun () =>
        k (.ok ()) { st with asserts := φ :: st.asserts })
  | .check φ, st, k =>
      .bracket
        (ScopedM.assert (.not φ) (fun () =>
          .checkSat (fun
            | .unsat => .ret true
            | _ => .ret false)))
        (fun b => k (.ok b) st)
  | .fatal msg, st, k => k (.error (.fatal msg)) st
  | .failed msg, st, k => k (.error (.failed msg)) st
  | .all items, st, k => translateAll items st k
  | .any items, st, k => translateAny items st k
  | .ctx f, st, k =>
      k (.ok (f st.asserts)) st
  | .seq m m2, st, k =>
      .bracket
        (m.translate st (fun a _ => ScopedM.ret a))
        (fun
          | .ok () => m2.translate st k
          | .error e => k (.error e) st)

/-! ### Eval_rec: postcondition-based semantics (raw) -/

def VerifM.eval_rec : VerifM α → TransState → Env → (α → TransState → Env → Prop) → Prop
  | .ret a, st, ρ, P => P a st ρ
  | .bind m k, st, ρ, P => m.eval_rec st ρ (fun r st' ρ' => (k r).eval_rec st' ρ' P)
  | .decl hint t, st, ρ, P =>
      let c := st.freshConst hint t
      ∀ u, P c { st with decls := st.decls.addConst c } (ρ.updateConst t c.name u)
  | .assume φ, st, ρ, P => φ.wfIn st.decls → φ.eval ρ → P () { st with asserts := φ :: st.asserts } ρ
  | .check φ, st, ρ, P => φ.wfIn st.decls → ∃ b, (b = true → φ.eval ρ) ∧ P b st ρ
  | .fatal _, _, _, _ => False
  | .failed _, _, _, _ => False
  | .all items, st, ρ, P => ∀ a ∈ items, P a st ρ
  | .any items, st, ρ, P => ∃ a ∈ items, P a st ρ
  | .ctx f, st, ρ, P => P (f st.asserts) st ρ
  | .seq m m2, st, ρ, P =>
      m.eval_rec st ρ (fun () _ _ => True) ∧ m2.eval_rec st ρ P

theorem VerifM.eval_rec.mono' {m : VerifM α} (ρ : Env) (st : TransState) (h : m.eval_rec st ρ P)
    (hPQ : ∀ a st' ρ', st.decls.Subset st'.decls → Env.agreeOn st.decls ρ ρ' → P a st' ρ' → Q a st' ρ') :
    m.eval_rec st ρ Q := by
  induction m generalizing st ρ with
  | ret => exact hPQ _ _ _ (Signature.Subset.refl _) (Env.agreeOn_refl) h
  | bind m k ihm ihk =>
    exact ihm ρ st h fun r st' ρ' hsub hag hr =>
      ihk r ρ' st' hr fun a st'' ρ'' hsub' hag' hp =>
        hPQ a st'' ρ'' (hsub.trans hsub') (Env.agreeOn_trans hag (Env.agreeOn_mono hsub hag')) hp
  | decl hint t =>
    intro u
    refine hPQ _ _ _ (Signature.Subset.subset_addConst _ _) ?_ (h u)
    exact agreeOn_update_fresh_const
      (c := ⟨fresh (addNumbers (hint.getD "_v")) st.decls.allNames, t⟩)
      (fresh_not_mem (addNumbers (hint.getD "_v")) st.decls.allNames (addNumbers_injective _))
  | assume =>
    intro hwf hφ
    exact hPQ _ _ _ (Signature.Subset.refl _) (Env.agreeOn_refl) (h hwf hφ)
  | check =>
    intro hwf
    obtain ⟨b, hb, hp⟩ := h hwf
    exact ⟨b, hb, hPQ _ _ _ (Signature.Subset.refl _) (Env.agreeOn_refl) hp⟩
  | fatal => exact h.elim
  | failed => exact h.elim
  | all items =>
    intro a ha
    exact hPQ _ _ _ (Signature.Subset.refl _) (Env.agreeOn_refl) (h a ha)
  | any items =>
    obtain ⟨a, ha, hp⟩ := h
    exact ⟨a, ha, hPQ _ _ _ (Signature.Subset.refl _) (Env.agreeOn_refl) hp⟩
  | ctx =>
    exact hPQ _ _ _ (Signature.Subset.refl _) (Env.agreeOn_refl) h
  | seq m m2 ihm ihf =>
    exact ⟨ihm ρ st h.1 fun () _ _ _ _ ha => trivial,
           ihf ρ st h.2 hPQ⟩

theorem VerifM.eval_rec.mono {m : VerifM α} (h : m.eval_rec st ρ P) (hPQ : ∀ a st' ρ', P a st' ρ' → Q a st' ρ') :
    m.eval_rec st ρ Q :=
  h.mono' ρ st fun a st' ρ' _ _ => hPQ a st' ρ'

theorem VerifM.eval_rec.decls_grow {m : VerifM α} ρ (h : m.eval_rec st ρ P) :
    m.eval_rec st ρ (fun a st' ρ' => st.decls.Subset st'.decls ∧ Env.agreeOn st.decls ρ ρ' ∧ P a st' ρ') :=
  h.mono' ρ st fun _ _ _ hsub hag hp => ⟨hsub, hag, hp⟩

/-! ### Adequacy: translate success implies eval -/


theorem VerifM.eval_rec_preserves_wf (m : VerifM α) (st : TransState) (ρ: Env)
    (h : VerifM.eval_rec m st ρ P) (g : st.holdsFor ρ) (hwf : st.wf) :
    VerifM.eval_rec m st ρ (fun a st' ρ' => st'.holdsFor ρ' ∧ st'.wf ∧ P a st' ρ') := by
  induction m generalizing st ρ with
  | ret a => exact ⟨g, hwf, h⟩
  | bind m k ihm ihk =>
    have hm := ihm st ρ h g hwf
    simp only [VerifM.eval_rec]
    exact hm.mono fun r st' ρ' ⟨g', hwf', hr⟩ =>
      ihk r st' ρ' hr g' hwf'
  | decl hint t =>
    simp only [VerifM.eval_rec] at h
    simp only [VerifM.eval_rec]
    intro u
    specialize (h u)
    let w := fresh (addNumbers (hint.getD "_v")) st.decls.allNames
    have hfresh := fresh_not_mem (addNumbers (hint.getD "_v")) st.decls.allNames (addNumbers_injective _)
    have hagree : Env.agreeOn st.decls ρ (ρ.updateConst t w u) := by
      exact agreeOn_update_fresh_const (c := ⟨w, t⟩) hfresh
    constructor
    · intro φ hφ
      exact (Formula.eval_env_agree (hwf.assertsWf φ hφ) hagree).mp (g φ hφ)
    · exact ⟨TransState.freshConst.wf _ hwf, h⟩
  | assume φ =>
    simp only [VerifM.eval_rec] at h ⊢
    intro hwf' hφ
    refine ⟨?_, TransState.addAssert.wf _ hwf hwf', h hwf' hφ⟩
    intro ψ hψ
    cases hψ with
    | head => exact hφ
    | tail _ hψ => exact g ψ hψ
  | check φ =>
    simp only [VerifM.eval_rec] at h ⊢
    intro hwf'
    obtain ⟨b, hb, hp⟩ := h hwf'
    exact ⟨b, hb, g, hwf, hp⟩
  | fatal msg => exact h.elim
  | failed msg => exact h.elim
  | all items =>
    simp only [VerifM.eval_rec] at h ⊢
    intro a ha
    exact ⟨g, hwf, h a ha⟩
  | any items =>
    simp only [VerifM.eval_rec] at h ⊢
    obtain ⟨a, ha, hp⟩ := h
    exact ⟨a, ha, g, hwf, hp⟩
  | ctx =>
    simp only [VerifM.eval_rec] at h ⊢
    exact ⟨g, hwf, h⟩
  | seq m m2 ihm ihf =>
    simp only [VerifM.eval_rec] at h ⊢
    exact ⟨(ihm st ρ h.1 g hwf).mono fun () _ _ _ => trivial,
           ihf st ρ h.2 g hwf⟩

private theorem translateAll_eval (items : List α) (st : TransState)
    (f : TransCont (Except VerifError α))
    (_hf : ∀ e st', ¬∃ Δ, ScopedM.eval (f (.error e) st') st'.toFlatCtx (.ok ()) Δ)
    (Δ : FlatCtx)
    (h : ScopedM.eval (translateAll items st f) st.toFlatCtx (.ok ()) Δ) :
    ∀ a ∈ items, ∃ Δ', ScopedM.eval (f (.ok a) st) st.toFlatCtx (.ok ()) Δ' := by
  induction items with
  | nil => intro _ hmem; simp at hmem
  | cons x xs ih =>
    simp only [translateAll] at h
    obtain ⟨r1, _, hbody1, hk1⟩ := ScopedM.eval_bracket h
    match r1 with
    | .error _ =>
      simp only [ScopedM.eval_ret] at hk1
      exact absurd hk1.1 (by simp)
    | .ok () =>
      intro a ha
      cases ha with
      | head => exact ⟨_, hbody1⟩
      | tail _ ha => exact ih hk1 a ha

private theorem translateAny_eval (items : List α) (st : TransState)
    (f : TransCont (Except VerifError α))
    (hf : ∀ e st', ¬∃ Δ, ScopedM.eval (f (.error e) st') st'.toFlatCtx (.ok ()) Δ)
    (Δ : FlatCtx)
    (h : ScopedM.eval (translateAny items st f) st.toFlatCtx (.ok ()) Δ) :
    ∃ a ∈ items, ∃ Δ', ScopedM.eval (f (.ok a) st) st.toFlatCtx (.ok ()) Δ' := by
  induction items with
  | nil =>
    simp only [translateAny] at h
    exact absurd ⟨Δ, h⟩ (hf (.failed "no alternative") st)
  | cons x xs ih =>
    simp only [translateAny] at h
    obtain ⟨r1, _, hbody1, hk1⟩ := ScopedM.eval_bracket h
    match r1 with
    | .ok () =>
      simp only [ScopedM.eval_ret] at hk1
      exact ⟨x, .head _, _, hbody1⟩
    | .error (.failed _) =>
      obtain ⟨a, ha, Δ', heval⟩ := ih hk1
      exact ⟨a, .tail _ ha, Δ', heval⟩
    | .error (.fatal _) =>
      simp only [ScopedM.eval_ret] at hk1
      exact absurd hk1.1 (by simp)

theorem VerifM.translate_eval_rec (m : VerifM α) (st : TransState) (ρ: Env)
    (f : TransCont (Except VerifError α))
    (hf : ∀ e st', ¬∃ Δ, ScopedM.eval (f (.error e) st') st'.toFlatCtx (.ok ()) Δ)
    (Δ : FlatCtx)
    (h : ScopedM.eval (m.translate st f) st.toFlatCtx (.ok ()) Δ)
    (g : st.holdsFor ρ)
    (hwf : st.wf)
    :
    VerifM.eval_rec m st ρ (fun a st' _ => ∃ Δ', ScopedM.eval (f (.ok a) st') st'.toFlatCtx (.ok ()) Δ') := by
  induction m generalizing st Δ ρ with
  | ret a => exact ⟨Δ, h⟩
  | bind m k ihm ihk =>
    simp only [VerifM.translate] at h
    let f' : TransCont (Except VerifError _) := fun
      | .ok a, st' => (k a).translate st' f
      | .error e, st' => f (.error e) st'
    have hf' : ∀ e st', ¬∃ Δ, ScopedM.eval (f' (.error e) st') st'.toFlatCtx (.ok ()) Δ := hf
    have hm := ihm st ρ f' hf' Δ h g hwf
    exact (eval_rec_preserves_wf m st ρ hm g hwf).mono fun r st' ρ' ⟨g', hwf', Δ', hr⟩ =>
      ihk r st' ρ' f hf Δ' hr g' hwf'
  | decl hint t =>
    simp only [VerifM.translate] at h
    have h := ScopedM.eval_declareConst h
    simp only [VerifM.eval_rec]
    intro u
    exact ⟨_, h⟩
  | assume φ =>
    simp only [VerifM.translate] at h
    have h := ScopedM.eval_assert h
    intro hwf' hφ
    exact ⟨_, h⟩
  | check φ =>
    simp only [VerifM.translate] at h
    obtain ⟨b, _, hxx, hk⟩ := ScopedM.eval_bracket h
    intro hwf'
    refine ⟨b, ?_, ⟨_, hk⟩⟩
    intro hb
    subst hb
    apply ScopedM.eval_assert at hxx
    apply ScopedM.eval_checkSat at hxx
    simp at hxx
    rcases hxx with ⟨hunsat, _⟩ | hfalse
    · have hunsat' : ¬Smt.State.satisfiable st.decls (Formula.not φ :: st.asserts) := by
        simp only [FlatCtx.addAssert] at hunsat; exact hunsat
      exact Smt.State.satisfiable.to_impl' st.decls st.asserts hunsat' ρ g
    · simp [ScopedM.eval_ret] at hfalse
  | fatal msg =>
    simp only [VerifM.translate] at h
    exact absurd ⟨Δ, h⟩ (hf (.fatal msg) st)
  | failed msg =>
    simp only [VerifM.translate] at h
    exact absurd ⟨Δ, h⟩ (hf (.failed msg) st)
  | all items =>
    simp only [VerifM.translate] at h
    have hall := translateAll_eval items st f hf Δ h
    intro a ha
    exact hall a ha
  | any items =>
    simp only [VerifM.translate] at h
    obtain ⟨a, ha, Δ', heval⟩ := translateAny_eval items st f hf Δ h
    exact ⟨a, ha, _, heval⟩
  | ctx f =>
    simp only [VerifM.translate] at h
    exact ⟨_, h⟩
  | seq m m2 ihm ihk =>
    simp only [VerifM.translate] at h
    obtain ⟨r1, _, hbody, hk⟩ := ScopedM.eval_bracket h
    let seqCont : TransCont (Except VerifError Unit) := fun a _ => ScopedM.ret a
    have hf' : ∀ e st', ¬∃ Δ', ScopedM.eval (seqCont (.error e) st') st'.toFlatCtx (.ok ()) Δ' := by
      intro e' st' ⟨Δ', h'⟩
      simp only [seqCont, ScopedM.eval_ret] at h'
      exact absurd h'.1 (by cases e' <;> simp)
    match r1 with
    | .ok () =>
      have hm := ihm st ρ seqCont hf' _ hbody g hwf
      exact ⟨(eval_rec_preserves_wf m st ρ hm g hwf).mono fun () _ _ _ => trivial,
             ihk st ρ f hf _ hk g hwf⟩
    | .error e =>
      exact absurd ⟨_, hk⟩ (hf e st)



/-! ### Eval: wf/holdsFor-aware postcondition semantics -/

/-- The main verification predicate. Requires `st` to be well-formed and satisfy `ρ`,
    and guarantees the same for every reachable `st'`. -/
def VerifM.eval (m : VerifM α) (st : TransState) (ρ : Env) (Q : α → TransState → Env → Prop) : Prop :=
  st.wf ∧ st.holdsFor ρ ∧
  m.eval_rec st ρ (fun a st' ρ' => st'.wf ∧ st'.holdsFor ρ' ∧ Q a st' ρ')

/-! ### Structural properties -/

theorem VerifM.eval.wf {m : VerifM α} {st : TransState} {ρ : Env} {Q : α → TransState → Env → Prop}
    (h : m.eval st ρ Q) : st.wf := h.1

theorem VerifM.eval.holdsFor {m : VerifM α} {st : TransState} {ρ : Env} {Q : α → TransState → Env → Prop}
    (h : m.eval st ρ Q) : st.holdsFor ρ := h.2.1

theorem VerifM.eval.mono' {m : VerifM α} (ρ : Env) (st : TransState) (h : m.eval st ρ P)
    (hPQ : ∀ a st' ρ', st.decls.Subset st'.decls → Env.agreeOn st.decls ρ ρ' →
      st'.wf → st'.holdsFor ρ' → P a st' ρ' → Q a st' ρ') :
    m.eval st ρ Q :=
  ⟨h.1, h.2.1, h.2.2.mono' ρ st fun a st' ρ' hsub hag ⟨hwf', hg', hp⟩ =>
    ⟨hwf', hg', hPQ a st' ρ' hsub hag hwf' hg' hp⟩⟩

theorem VerifM.eval.mono {m : VerifM α} (h : m.eval st ρ P) (hPQ : ∀ a st' ρ', P a st' ρ' → Q a st' ρ') :
    m.eval st ρ Q :=
  h.mono' ρ st fun a st' ρ' _ _ _ _ => hPQ a st' ρ'

theorem VerifM.eval.decls_grow {m : VerifM α} ρ (h : m.eval st ρ P) :
    m.eval st ρ (fun a st' ρ' => st.decls.Subset st'.decls ∧ Env.agreeOn st.decls ρ ρ' ∧ P a st' ρ') :=
  h.mono' ρ st fun _ _ _ hsub hag _ _ hp => ⟨hsub, hag, hp⟩

/-! ### Inversion lemmas for VerifM.eval (forward direction) -/

theorem VerifM.eval_ret {a : α} {st : TransState} {ρ : Env} {Q : α → TransState → Env → Prop}
    (h : VerifM.eval (.ret a) st ρ Q) : Q a st ρ :=
  h.2.2.2.2

theorem VerifM.eval_bind (m : VerifM α) (k : α → VerifM β) st ρ :
  (m.bind k).eval st ρ P →
  m.eval st ρ (fun r st' ρ' => (k r).eval st' ρ' P) := by
  intros hev
  obtain ⟨hwf, hholds, hev⟩ := hev
  simp [VerifM.eval_rec] at hev
  refine ⟨hwf, hholds, ?_⟩
  apply VerifM.eval_rec_preserves_wf at hev
  apply (VerifM.eval_rec.mono (hev hholds hwf))
  intro a st' ρ' ⟨hholds', hwf', hev⟩
  refine ⟨hwf', hholds', ?_⟩
  refine ⟨hwf', hholds', ?_⟩
  trivial



theorem VerifM.eval_failed {st : TransState} {ρ : Env} {Q : α → TransState → Env → Prop}
    (h : VerifM.eval (.failed msg) st ρ Q) : False :=
  h.2.2

theorem VerifM.eval_fatal {st : TransState} {ρ : Env} {Q : α → TransState → Env → Prop}
    (h : VerifM.eval (.fatal msg) st ρ Q) : False :=
  h.2.2

theorem VerifM.eval_decl {hint : Option String} {t : Srt} {st : TransState} {ρ : Env}
    {Q : FOL.Const → TransState → Env → Prop}
    (h : VerifM.eval (.decl hint t) st ρ Q) :
    let c := st.freshConst hint t
    ∀ u, Q c { st with decls := st.decls.addConst c } (ρ.updateConst t c.name u) :=
  fun u => (h.2.2 u).2.2

theorem VerifM.eval_assume {φ : Formula} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop}
    (h : VerifM.eval (.assume φ) st ρ Q) :
    φ.wfIn st.decls → φ.eval ρ → Q () { st with asserts := φ :: st.asserts } ρ :=
  fun hwf hφ => (h.2.2 hwf hφ).2.2

theorem VerifM.eval_check {φ : Formula} {st : TransState} {ρ : Env}
    {Q : Bool → TransState → Env → Prop}
    (h : VerifM.eval (.check φ) st ρ Q) :
    φ.wfIn st.decls →
    ∃ b, (b = true → φ.eval ρ) ∧ Q b st ρ :=
  fun hwf =>
    let ⟨b, hb, _, _, hq⟩ := h.2.2 hwf
    ⟨b, hb, hq⟩

theorem VerifM.eval_assert {φ : Formula} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop}
    (h : VerifM.eval (VerifM.assert φ) st ρ Q) :
    φ.wfIn st.decls → φ.eval ρ ∧ Q () st ρ := by
  intro hwf
  simp only [VerifM.assert] at h
  have hb := VerifM.eval_bind _ _ _ _ h
  have ⟨b, hb_sound, hq⟩ := VerifM.eval_check hb hwf
  cases b with
  | true =>
    simp at hq
    exact ⟨hb_sound rfl, VerifM.eval_ret hq⟩
  | false =>
    simp at hq
    exact (VerifM.eval_failed hq).elim

theorem VerifM.eval_expectEq [DecidableEq α] [Repr α]
    {msg : String} {actual expected : α} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop}
    (h : VerifM.eval (VerifM.expectEq msg actual expected) st ρ Q) :
    actual = expected ∧ Q () st ρ := by
  unfold VerifM.expectEq at h
  by_cases heq : actual = expected
  · simp [heq] at h
    exact ⟨heq, VerifM.eval_ret h⟩
  · simp [heq] at h
    exact (VerifM.eval_fatal h).elim

theorem VerifM.eval_expectSome
    {msg : String} {x : Option α} {st : TransState} {ρ : Env}
    {Q : α → TransState → Env → Prop}
    (h : VerifM.eval (VerifM.expectSome msg x) st ρ Q) :
    ∃ y, x = some y ∧ Q y st ρ := by
  unfold VerifM.expectSome at h
  cases hx : x with
  | none =>
    simp [hx] at h
    exact (VerifM.eval_fatal h).elim
  | some y =>
    simp [hx] at h
    exact ⟨y, rfl, VerifM.eval_ret h⟩

theorem VerifM.eval_bind_expectEq [DecidableEq α] [Repr α]
    {msg : String} {actual expected : α} {β : Type _} {k : Unit → VerifM β}
    {st : TransState} {ρ : Env} {Q : β → TransState → Env → Prop}
    (h : VerifM.eval ((VerifM.expectEq msg actual expected).bind k) st ρ Q) :
    actual = expected ∧ VerifM.eval (k ()) st ρ Q := by
  have hb := VerifM.eval_bind _ _ _ _ h
  obtain ⟨heq, hk⟩ := VerifM.eval_expectEq hb
  exact ⟨heq, hk⟩

theorem VerifM.eval_bind_expectSome
    {msg : String} {x : Option α} {β : Type _} {k : α → VerifM β}
    {st : TransState} {ρ : Env} {Q : β → TransState → Env → Prop}
    (h : VerifM.eval ((VerifM.expectSome msg x).bind k) st ρ Q) :
    ∃ y, x = some y ∧ VerifM.eval (k y) st ρ Q := by
  have hb := VerifM.eval_bind _ _ _ _ h
  obtain ⟨y, hx, hk⟩ := VerifM.eval_expectSome hb
  exact ⟨y, hx, hk⟩

theorem VerifM.eval_all {items : List α} {st : TransState} {ρ : Env}
    {Q : α → TransState → Env → Prop}
    (h : VerifM.eval (.all items) st ρ Q) :
    ∀ a ∈ items, Q a st ρ :=
  fun a ha => (h.2.2 a ha).2.2

theorem VerifM.eval_any {items : List α} {st : TransState} {ρ : Env}
    {Q : α → TransState → Env → Prop}
    (h : VerifM.eval (.any items) st ρ Q) :
    ∃ a ∈ items, Q a st ρ :=
  let ⟨a, ha, _, _, hq⟩ := h.2.2; ⟨a, ha, hq⟩


theorem VerifM.eval_ctx {f : List Formula → α} {st : TransState} {ρ : Env}
    {Q : α → TransState → Env → Prop}
    (h : VerifM.eval (.ctx f) st ρ Q) :
    Q (f st.asserts) st ρ
    ∧ st.holdsFor ρ
    ∧ st.asserts.wfIn st.decls :=
  ⟨h.2.2.2.2, h.2.1, h.1.assertsWf⟩

theorem VerifM.eval_seq {m : VerifM Unit} {m2 : VerifM β} {st : TransState} {ρ : Env}
    {Q : β → TransState → Env → Prop}
    (h : VerifM.eval (.seq m m2) st ρ Q) :
    VerifM.eval m st ρ (fun () _ _ => True) ∧ VerifM.eval m2 st ρ Q := by
  obtain ⟨hwf, hholds, hm, hm2⟩ := h
  exact ⟨⟨hwf, hholds, (eval_rec_preserves_wf m st ρ hm hholds hwf).mono
    fun () _ _ ⟨hg', hwf', _⟩ => ⟨hwf', hg', trivial⟩⟩,
   ⟨hwf, hholds, hm2⟩⟩

theorem VerifM.eval_assumeAll {φs : List Formula}
    {st : TransState} {ρ : Env} {P : Unit → TransState → Env → Prop}
    (h : VerifM.eval (VerifM.assumeAll φs) st ρ P) :
    (∀ φ ∈ φs, φ.wfIn st.decls) →
    (∀ φ ∈ φs, φ.eval ρ) →
    ∃ st', st'.decls = st.decls ∧ P () st' ρ := by
  induction φs generalizing st with
  | nil =>
    intro _ _
    simp only [VerifM.assumeAll] at h
    exact ⟨st, rfl, VerifM.eval_ret h⟩
  | cons φ φs ih =>
    intro hwf heval
    simp only [VerifM.assumeAll] at h
    have hb := VerifM.eval_bind _ _ _ _ h
    have hassume := VerifM.eval_assume hb
    have hcont := hassume
      (hwf φ (List.mem_cons_self ..))
      (heval φ (List.mem_cons_self ..))
    obtain ⟨st', hst', hp⟩ := ih hcont
      (fun ψ hψ => hwf ψ (List.mem_cons_of_mem _ hψ))
      (fun ψ hψ => heval ψ (List.mem_cons_of_mem _ hψ))
    exact ⟨st', by rw [hst'], hp⟩


/-! ### Top-level corollary -/

def VerifM.topCont : TransCont (Except VerifError Unit) :=
  fun x _ => ScopedM.ret x

theorem VerifM.topCont_error_propagates :
    ∀ e st', ¬∃ Δ, ScopedM.eval (VerifM.topCont (.error e) st') st'.toFlatCtx (.ok ()) Δ := by
  intro e st' ⟨Δ, h⟩
  simp only [topCont, ScopedM.eval_ret] at h
  exact absurd h.1 (by cases e <;> simp)

theorem VerifM.translate_eval (m : VerifM α) (st : TransState) (ρ : Env)
    (f : TransCont (Except VerifError α))
    (hf : ∀ e st', ¬∃ Δ, ScopedM.eval (f (.error e) st') st'.toFlatCtx (.ok ()) Δ)
    (Δ : FlatCtx)
    (h : ScopedM.eval (m.translate st f) st.toFlatCtx (.ok ()) Δ)
    (g : st.holdsFor ρ) (hwf : st.wf) :
    VerifM.eval m st ρ (fun a st' _ => ∃ Δ', ScopedM.eval (f (.ok a) st') st'.toFlatCtx (.ok ()) Δ') :=
  ⟨hwf, g, (eval_rec_preserves_wf m st ρ (translate_eval_rec m st ρ f hf Δ h g hwf) g hwf).mono
    fun _ _ _ ⟨hg', hwf', hΔ'⟩ => ⟨hwf', hg', hΔ'⟩⟩

theorem VerifM.eval_of_translate (m : VerifM Unit) (st : TransState) (ρ : Env) (Δ : FlatCtx)
    (h : ScopedM.eval (m.translate st topCont) st.toFlatCtx (.ok ()) Δ)
    (g : st.holdsFor ρ) (hwf : st.wf) :
    VerifM.eval m st ρ (fun _ _ _ => True) :=
  (translate_eval m st ρ topCont topCont_error_propagates Δ h g hwf).mono fun _ _ _ _ => trivial

def VerifM.strategy (m : VerifM Unit) :=
  let verif := VerifM.translate m TransState.empty VerifM.topCont
  let verif' := ScopedM.bind verif fun
    | .ok () => ScopedM.ret (Except.ok ())
    | .error (.failed msg) => ScopedM.ret (Except.error msg)
    | .error (.fatal msg) => ScopedM.ret (Except.error msg)
  ScopedM.translate verif'
