-- SUMMARY: Verification monad with SMT operations, branching, and its operational and semantic correctness interfaces.
import Mica.Engine.Driver
import Mica.Verifier.Scoped
import Mica.Verifier.State
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
  /-- Declare a fresh unary relation symbol with the given hint and argument sort. -/
  | declUnaryRel : Option String → Srt → VerifM FOL.UnaryRel
  /-- Declare a fresh binary relation symbol with the given hint and argument sorts. -/
  | declBinaryRel : Option String → Srt → Srt → VerifM FOL.BinaryRel
  /-- Declare a fresh unary function symbol with the given hint, argument and result sorts. -/
  | declUnary : Option String → Srt → Srt → VerifM FOL.Unary
  /-- Declare a fresh binary function symbol with the given hint, argument and result sorts. -/
  | declBinary : Option String → Srt → Srt → Srt → VerifM FOL.Binary
  /-- Declare a fresh ternary function symbol with the given hint, arguments and result sort. -/
  | declTernary : Option String → Srt → Srt → Srt → Srt → VerifM FOL.Ternary
  /-- Add a context item to the verifier state (permanent, no check). -/
  | assume : CtxItem → VerifM Unit
  /-- Check whether φ is provable from the current context. Returns `true` if
      ¬ φ is unsat, `false` otherwise. Never fails. At `.low` effort guarded
      axioms are ignored; at `.high` effort they are enabled. -/
  | check : Effort → Formula → VerifM Bool
  /-- Abort with a fatal error. -/
  | fatal : String → VerifM α
  /-- Abort with a recoverable failure. -/
  | failed : String → VerifM α
  /-- Execute all branches; succeed only if every branch succeeds. -/
  | all : List α → VerifM α
  /-- Try branches in order; succeed if any branch succeeds (non-fatally). -/
  | any : List α → VerifM α
  /-- Inspect the full verifier state; may update the spatial context. -/
  | ctx : (TransState → α × SpatialContext) → VerifM α
  /-- Run a scoped computation: declarations and assertions from the body
      are discarded after it completes. Only the return value is kept. -/
  | seq : VerifM Unit → VerifM β → VerifM β

instance : Monad VerifM where
  pure := VerifM.ret
  bind := VerifM.bind


/-- Read the current pure assertion context (backwards-compatible wrapper around `ctx`). -/
def VerifM.ctxPure (f : List Formula → α) : VerifM α :=
  VerifM.ctx (fun st => (f st.asserts, st.owns))

/-- Drop the current spatial context, keeping only the persistent verifier state. -/
def VerifM.persist : VerifM Unit :=
  VerifM.ctx (fun st => ((), (TransState.persist st).owns))

/-- Assert-and-check: check φ is provable at high effort, fail if not. -/
def VerifM.assert (φ : Formula) : VerifM Unit := do
  if ← VerifM.check .high φ then pure ()
  else VerifM.failed s!"assertion failed"

/-- Quick provability test at low effort: guarded axioms are invisible, so a
`false` answer is fast and is normal control flow. -/
def VerifM.test (φ : Formula) : VerifM Bool :=
  VerifM.check .low φ

/-- Check that two elaboration-time values match exactly, otherwise abort fatally. -/
def VerifM.expectEq [DecidableEq α] [Repr α] (msg : String) (actual expected : α) : VerifM Unit := do
  if actual = expected then pure ()
  else VerifM.fatal s!"{msg}: expected {repr expected}, got {repr actual}"

/-- Unwrap an `Option`, otherwise abort fatally. -/
def VerifM.expectSome (msg : String) (x : Option α) : VerifM α := do
  match x with
  | some x => pure x
  | none => VerifM.fatal msg

/-- Declare a constant with a specific name, failing if a different name was assigned. -/
def VerifM.declConstExact (c : FOL.Const) : VerifM Unit := do
  let c' ← VerifM.decl (some c.name) c.sort
  VerifM.expectEq "declConstExact" c'.name c.name

/-- Declare a unary relation with a specific name, failing if a different name was assigned. -/
def VerifM.declUnaryRelExact (u : FOL.UnaryRel) : VerifM Unit := do
  let u' ← VerifM.declUnaryRel (some u.name) u.arg
  VerifM.expectEq "declUnaryRelExact" u'.name u.name

/-- Declare a binary relation with a specific name, failing if a different name was assigned. -/
def VerifM.declBinaryRelExact (b : FOL.BinaryRel) : VerifM Unit := do
  let b' ← VerifM.declBinaryRel (some b.name) b.arg1 b.arg2
  VerifM.expectEq "declBinaryRelExact" b'.name b.name

/-- Declare a unary function with a specific name, failing if a different name was assigned. -/
def VerifM.declUnaryExact (u : FOL.Unary) : VerifM Unit := do
  let u' ← VerifM.declUnary (some u.name) u.arg u.ret
  VerifM.expectEq "declUnaryExact" u'.name u.name

/-- Declare a binary function with a specific name, failing if a different name was assigned. -/
def VerifM.declBinaryExact (b : FOL.Binary) : VerifM Unit := do
  let b' ← VerifM.declBinary (some b.name) b.arg1 b.arg2 b.ret
  VerifM.expectEq "declBinaryExact" b'.name b.name

/-- Declare a ternary function with a specific name, failing if a different name was assigned. -/
def VerifM.declTernaryExact (t : FOL.Ternary) : VerifM Unit := do
  let t' ← VerifM.declTernary (some t.name) t.arg1 t.arg2 t.arg3 t.ret
  VerifM.expectEq "declTernaryExact" t'.name t.name

/-- Assume all formulas in a list via `VerifM.assume`. -/
def VerifM.assumeAll : List Formula → VerifM Unit
  | [] => pure ()
  | φ :: φs => do VerifM.assume (.pure φ); VerifM.assumeAll φs

/-- Assume a list of axioms, weakening high-effort axioms by the guard. -/
def VerifM.assumeAxioms (axs : List Axiom) : VerifM Unit :=
  VerifM.assumeAll (Axiom.asserts axs)

def TransCont α := α → TransState → ScopedM (Except VerifError Unit)

def VerifM.translateAll (items : List α) (st : TransState) (k : TransCont (Except VerifError α)) :
    ScopedM (Except VerifError Unit) :=
  match items with
  | [] => ScopedM.ret (.ok ())
  | a :: rest =>
      .bracket (k (.ok a) st) (fun
        | .error e => ScopedM.ret (.error e)
        | .ok () => VerifM.translateAll rest st k)

def VerifM.translateAny (items : List α) (st : TransState) (k : TransCont (Except VerifError α)) :
    ScopedM (Except VerifError Unit) :=
  match items with
  | [] => k (.error (.failed "no alternative")) st
  | a :: rest =>
      .bracket (k (.ok a) st) (fun
        | .ok () => ScopedM.ret (.ok ())
        | .error (.failed _) => VerifM.translateAny rest st k
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
  | .declUnaryRel hint τ, st, k =>
      let u := st.freshUnaryRel hint τ
      .declareUnaryRel u.name u.arg (fun () =>
        k (.ok u) { st with decls := st.decls.addUnaryRel u })
  | .declBinaryRel hint τ₁ τ₂, st, k =>
      let b := st.freshBinaryRel hint τ₁ τ₂
      .declareBinaryRel b.name b.arg1 b.arg2 (fun () =>
        k (.ok b) { st with decls := st.decls.addBinaryRel b })
  | .declUnary hint τ₁ τ₂, st, k =>
      let u := st.freshUnary hint τ₁ τ₂
      .declareUnary u.name u.arg u.ret (fun () =>
        k (.ok u) { st with decls := st.decls.addUnary u })
  | .declBinary hint τ₁ τ₂ τ₃, st, k =>
      let b := st.freshBinary hint τ₁ τ₂ τ₃
      .declareBinary b.name b.arg1 b.arg2 b.ret (fun () =>
        k (.ok b) { st with decls := st.decls.addBinary b })
  | .declTernary hint τ₁ τ₂ τ₃ τ₄, st, k =>
      let t := st.freshTernary hint τ₁ τ₂ τ₃ τ₄
      .declareTernary t.name t.arg1 t.arg2 t.arg3 t.ret (fun () =>
        k (.ok t) { st with decls := st.decls.addTernary t })
  | .assume item, st, k =>
      match item with
      | .pure φ =>
          ScopedM.assert φ (fun () =>
            k (.ok ()) { st with asserts := φ :: st.asserts })
      | .spatial a =>
          k (.ok ()) { st with owns := a :: st.owns }
  | .check e φ, st, k =>
      -- Low effort first probes `guard = false ∧ ¬φ`; if that is unsat, it
      -- reruns the normal `¬φ` check. High effort asserts the guard while
      -- checking `¬φ`, enabling guarded axioms for that check.
      let body := ScopedM.assert (.not φ) (fun () =>
        .checkSat (fun
          | .unsat => .ret true
          | _ => .ret false))
      .bracket
        (match e with
         | .low => ScopedM.probe (.and guardFalseFormula (.not φ)) (fun
            | .unsat => body
            | _ => .ret false)
         | .high => ScopedM.assert guardFormula (fun () => body))
        (fun b => k (.ok b) st)
  | .fatal msg, st, k => k (.error (.fatal msg)) st
  | .failed msg, st, k => k (.error (.failed msg)) st
  | .all items, st, k => VerifM.translateAll items st k
  | .any items, st, k => VerifM.translateAny items st k
  | .ctx f, st, k =>
      let (a, owns') := f st
      k (.ok a) { st with owns := owns' }
  | .seq m m2, st, k =>
      .bracket
        (m.translate st (fun a _ => ScopedM.ret a))
        (fun
          | .ok () => m2.translate st k
          | .error e => k (.error e) st)

/-! ### Eval_rec: postcondition-based semantics (raw) -/

private def VerifM.eval_rec : VerifM α → TransState → VerifM.Env → (α → TransState → VerifM.Env → Prop) → Prop
  | .ret a, st, ρ, P => P a st ρ
  | .bind m k, st, ρ, P => m.eval_rec st ρ (fun r st' ρ' => (k r).eval_rec st' ρ' P)
  | .decl hint t, st, ρ, P =>
      let c := st.freshConst hint t
      ∀ u, P c { st with decls := st.decls.addConst c } (ρ.updateConst t c.name u)
  | .declUnaryRel hint τ, st, ρ, P =>
      let u := st.freshUnaryRel hint τ
      ∀ f, P u { st with decls := st.decls.addUnaryRel u } (ρ.updateUnaryRel τ u.name f)
  | .declBinaryRel hint τ₁ τ₂, st, ρ, P =>
      let b := st.freshBinaryRel hint τ₁ τ₂
      ∀ f, P b { st with decls := st.decls.addBinaryRel b } (ρ.updateBinaryRel τ₁ τ₂ b.name f)
  | .declUnary hint τ₁ τ₂, st, ρ, P =>
      let u := st.freshUnary hint τ₁ τ₂
      ∀ f, P u { st with decls := st.decls.addUnary u } (ρ.updateUnary τ₁ τ₂ u.name f)
  | .declBinary hint τ₁ τ₂ τ₃, st, ρ, P =>
      let b := st.freshBinary hint τ₁ τ₂ τ₃
      ∀ f, P b { st with decls := st.decls.addBinary b } (ρ.updateBinary τ₁ τ₂ τ₃ b.name f)
  | .declTernary hint τ₁ τ₂ τ₃ τ₄, st, ρ, P =>
      let t := st.freshTernary hint τ₁ τ₂ τ₃ τ₄
      ∀ f, P t { st with decls := st.decls.addTernary t }
        (ρ.updateTernary τ₁ τ₂ τ₃ τ₄ t.name f)
  | .assume item, st, ρ, P =>
      match item with
      | .pure φ => φ.wfIn st.decls → φ.eval ρ.env → P () { st with asserts := φ :: st.asserts } ρ
      | .spatial a => a.wfIn st.decls → P () { st with owns := a :: st.owns } ρ
  | .check _ φ, st, ρ, P => φ.wfIn st.decls → ∃ b, (b = true → φ.eval ρ.env) ∧ P b st ρ
  | .fatal _, _, _, _ => False
  | .failed _, _, _, _ => False
  | .all items, st, ρ, P => ∀ a ∈ items, P a st ρ
  | .any items, st, ρ, P => ∃ a ∈ items, P a st ρ
  | .ctx f, st, ρ, P =>
      let (a, owns') := f st
      owns'.wfIn st.decls → P a { st with owns := owns' } ρ
  | .seq m m2, st, ρ, P =>
      m.eval_rec st ρ (fun () _ _ => True) ∧ m2.eval_rec st ρ P

private theorem VerifM.eval_rec.mono' {m : VerifM α} (ρ : VerifM.Env) (st : TransState) (h : m.eval_rec st ρ P)
    (hPQ : ∀ a st' (ρ' : VerifM.Env),
      st.decls.Subset st'.decls → VerifM.Env.agreeOn st.decls ρ ρ' → P a st' ρ' → Q a st' ρ') :
    m.eval_rec st ρ Q := by
  induction m generalizing st ρ with
  | ret => exact hPQ _ _ _ (Signature.Subset.refl _) (VerifM.Env.agreeOn_refl) h
  | bind m k ihm ihk =>
    exact ihm ρ st h fun r st' ρ' hsub hag hr =>
      ihk r ρ' st' hr fun a st'' ρ'' hsub' hag' hp =>
        hPQ a st'' ρ'' (hsub.trans hsub') (VerifM.Env.agreeOn_trans hag (VerifM.Env.agreeOn_mono hsub hag')) hp
  | decl hint t =>
    intro u
    refine hPQ _ _ _ (Signature.Subset.subset_addConst _ _) ?_ (h u)
    exact VerifM.Env.agreeOn_update_fresh
      (c := ⟨Fresh.freshNumbers (hint.getD "_v") st.decls.allNames, t⟩)
      (Fresh.freshNumbers_not_mem (hint.getD "_v") st.decls.allNames)
  | declUnaryRel hint τ =>
    simp only [VerifM.eval_rec] at h ⊢
    intro f
    refine hPQ _ _ _ (Signature.Subset.subset_addUnaryRel _ _) ?_ (h f)
    exact VerifM.Env.agreeOn_update_fresh_unaryRel
      (u := st.freshUnaryRel hint τ)
      (st.freshUnaryRel_fresh hint τ)
  | declBinaryRel hint τ₁ τ₂ =>
    simp only [VerifM.eval_rec] at h ⊢
    intro f
    refine hPQ _ _ _ (Signature.Subset.subset_addBinaryRel _ _) ?_ (h f)
    exact VerifM.Env.agreeOn_update_fresh_binaryRel
      (b := st.freshBinaryRel hint τ₁ τ₂)
      (st.freshBinaryRel_fresh hint τ₁ τ₂)
  | declUnary hint τ₁ τ₂ =>
    simp only [VerifM.eval_rec] at h ⊢
    intro f
    refine hPQ _ _ _ (Signature.Subset.subset_addUnary _ _) ?_ (h f)
    exact VerifM.Env.agreeOn_update_fresh_unary
      (u := st.freshUnary hint τ₁ τ₂)
      (st.freshUnary_fresh hint τ₁ τ₂)
  | declBinary hint τ₁ τ₂ τ₃ =>
    simp only [VerifM.eval_rec] at h ⊢
    intro f
    refine hPQ _ _ _ (Signature.Subset.subset_addBinary _ _) ?_ (h f)
    exact VerifM.Env.agreeOn_update_fresh_binary
      (b := st.freshBinary hint τ₁ τ₂ τ₃)
      (st.freshBinary_fresh hint τ₁ τ₂ τ₃)
  | declTernary hint τ₁ τ₂ τ₃ τ₄ =>
    simp only [VerifM.eval_rec] at h ⊢
    intro f
    refine hPQ _ _ _ (Signature.Subset.subset_addTernary _ _) ?_ (h f)
    exact VerifM.Env.agreeOn_update_fresh_ternary
      (t := st.freshTernary hint τ₁ τ₂ τ₃ τ₄)
      (st.freshTernary_fresh hint τ₁ τ₂ τ₃ τ₄)
  | assume item =>
    cases item with
    | pure φ =>
      intro hwf hφ
      exact hPQ _ _ _ (Signature.Subset.refl _) (VerifM.Env.agreeOn_refl) (h hwf hφ)
    | spatial a =>
      intro hwf
      exact hPQ _ _ _ (Signature.Subset.refl _) (VerifM.Env.agreeOn_refl) (h hwf)
  | check =>
    intro hwf
    obtain ⟨b, hb, hp⟩ := h hwf
    exact ⟨b, hb, hPQ _ _ _ (Signature.Subset.refl _) (VerifM.Env.agreeOn_refl) hp⟩
  | fatal => exact h.elim
  | failed => exact h.elim
  | all items =>
    intro a ha
    exact hPQ _ _ _ (Signature.Subset.refl _) (VerifM.Env.agreeOn_refl) (h a ha)
  | any items =>
    obtain ⟨a, ha, hp⟩ := h
    exact ⟨a, ha, hPQ _ _ _ (Signature.Subset.refl _) (VerifM.Env.agreeOn_refl) hp⟩
  | ctx f =>
    intro howns
    exact hPQ _ _ _ (Signature.Subset.refl _) VerifM.Env.agreeOn_refl (h howns)
  | seq m m2 ihm ihf =>
    exact ⟨ihm ρ st h.1 fun () _ _ _ _ ha => trivial,
           ihf ρ st h.2 hPQ⟩

private theorem VerifM.eval_rec.mono {m : VerifM α} (h : m.eval_rec st ρ P) (hPQ : ∀ a st' ρ', P a st' ρ' → Q a st' ρ') :
    m.eval_rec st ρ Q :=
  h.mono' ρ st fun a st' ρ' _ _ => hPQ a st' ρ'

private theorem VerifM.eval_rec.decls_grow {m : VerifM α} ρ (h : m.eval_rec st ρ P) :
    m.eval_rec st ρ (fun a st' ρ' => st.decls.Subset st'.decls ∧ VerifM.Env.agreeOn st.decls ρ ρ' ∧ P a st' ρ') :=
  h.mono' ρ st fun _ _ _ hsub hag hp => ⟨hsub, hag, hp⟩

/-! ### Adequacy: translate success implies eval -/


private theorem VerifM.eval_rec_preserves_wf (m : VerifM α) (st : TransState) (ρ: VerifM.Env)
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
    let w := Fresh.freshNumbers (hint.getD "_v") st.decls.allNames
    have hfresh := Fresh.freshNumbers_not_mem (hint.getD "_v") st.decls.allNames
    have hagree : VerifM.Env.agreeOn st.decls ρ (ρ.updateConst t w u) := by
      exact VerifM.Env.agreeOn_update_fresh (c := ⟨w, t⟩) hfresh
    refine ⟨⟨?_, g.builtins.agree hwf.builtins hagree⟩, TransState.freshConst.wf _ hwf, h⟩
    intro φ hφ
    exact (Formula.eval_env_agree (hwf.assertsWf φ hφ) hagree).mp (g.asserts φ hφ)
  | declUnaryRel hint τ =>
    simp only [VerifM.eval_rec] at h
    simp only [VerifM.eval_rec]
    intro f
    specialize h f
    let u := st.freshUnaryRel hint τ
    have hfresh := st.freshUnaryRel_fresh hint τ
    have hagree : VerifM.Env.agreeOn st.decls ρ (ρ.updateUnaryRel τ u.name f) := by
      exact VerifM.Env.agreeOn_update_fresh_unaryRel (u := u) hfresh
    refine ⟨⟨?_, g.builtins.agree hwf.builtins hagree⟩,
      TransState.addUnaryRel.wf st _ hwf hfresh, h⟩
    intro φ hφ
    exact (Formula.eval_env_agree (hwf.assertsWf φ hφ) hagree).mp (g.asserts φ hφ)
  | declBinaryRel hint τ₁ τ₂ =>
    simp only [VerifM.eval_rec] at h
    simp only [VerifM.eval_rec]
    intro f
    specialize h f
    let b := st.freshBinaryRel hint τ₁ τ₂
    have hfresh := st.freshBinaryRel_fresh hint τ₁ τ₂
    have hagree : VerifM.Env.agreeOn st.decls ρ (ρ.updateBinaryRel τ₁ τ₂ b.name f) := by
      exact VerifM.Env.agreeOn_update_fresh_binaryRel (b := b) hfresh
    refine ⟨⟨?_, g.builtins.agree hwf.builtins hagree⟩,
      TransState.addBinaryRel.wf st _ hwf hfresh, h⟩
    intro φ hφ
    exact (Formula.eval_env_agree (hwf.assertsWf φ hφ) hagree).mp (g.asserts φ hφ)
  | declUnary hint τ₁ τ₂ =>
    simp only [VerifM.eval_rec] at h
    simp only [VerifM.eval_rec]
    intro f
    specialize h f
    let u := st.freshUnary hint τ₁ τ₂
    have hfresh := st.freshUnary_fresh hint τ₁ τ₂
    have hagree : VerifM.Env.agreeOn st.decls ρ (ρ.updateUnary τ₁ τ₂ u.name f) := by
      exact VerifM.Env.agreeOn_update_fresh_unary (u := u) hfresh
    refine ⟨⟨?_, g.builtins.agree hwf.builtins hagree⟩,
      TransState.addUnary.wf st _ hwf hfresh, h⟩
    intro φ hφ
    exact (Formula.eval_env_agree (hwf.assertsWf φ hφ) hagree).mp (g.asserts φ hφ)
  | declBinary hint τ₁ τ₂ τ₃ =>
    simp only [VerifM.eval_rec] at h
    simp only [VerifM.eval_rec]
    intro f
    specialize h f
    let b := st.freshBinary hint τ₁ τ₂ τ₃
    have hfresh := st.freshBinary_fresh hint τ₁ τ₂ τ₃
    have hagree : VerifM.Env.agreeOn st.decls ρ (ρ.updateBinary τ₁ τ₂ τ₃ b.name f) := by
      exact VerifM.Env.agreeOn_update_fresh_binary (b := b) hfresh
    refine ⟨⟨?_, g.builtins.agree hwf.builtins hagree⟩,
      TransState.addBinary.wf st _ hwf hfresh, h⟩
    intro φ hφ
    exact (Formula.eval_env_agree (hwf.assertsWf φ hφ) hagree).mp (g.asserts φ hφ)
  | declTernary hint τ₁ τ₂ τ₃ τ₄ =>
    simp only [VerifM.eval_rec] at h
    simp only [VerifM.eval_rec]
    intro f
    specialize h f
    let t := st.freshTernary hint τ₁ τ₂ τ₃ τ₄
    have hfresh := st.freshTernary_fresh hint τ₁ τ₂ τ₃ τ₄
    have hagree : VerifM.Env.agreeOn st.decls ρ (ρ.updateTernary τ₁ τ₂ τ₃ τ₄ t.name f) := by
      exact VerifM.Env.agreeOn_update_fresh_ternary (t := t) hfresh
    refine ⟨⟨?_, g.builtins.agree hwf.builtins hagree⟩,
      TransState.addTernary.wf st _ hwf hfresh, h⟩
    intro φ hφ
    exact (Formula.eval_env_agree (hwf.assertsWf φ hφ) hagree).mp (g.asserts φ hφ)
  | assume item =>
    cases item with
    | pure φ =>
      simp only [VerifM.eval_rec] at h ⊢
      intro hwf' hφ
      refine ⟨⟨?_, g.builtins⟩, TransState.addAssert.wf _ hwf hwf', h hwf' hφ⟩
      intro ψ hψ
      cases hψ with
      | head => exact hφ
      | tail _ hψ => exact g.asserts ψ hψ
    | spatial a =>
      simp only [VerifM.eval_rec] at h ⊢
      intro hwf'
      exact ⟨⟨g.asserts, g.builtins⟩, TransState.addSpatial.wf _ hwf hwf', h hwf'⟩
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
  | ctx f =>
    simp only [VerifM.eval_rec] at h ⊢
    intro howns
    exact ⟨⟨g.asserts, g.builtins⟩,
      ⟨hwf.assertsWf, hwf.namesDisjoint, howns, hwf.builtins⟩, h howns⟩
  | seq m m2 ihm ihf =>
    simp only [VerifM.eval_rec] at h ⊢
    exact ⟨(ihm st ρ h.1 g hwf).mono fun () _ _ _ => trivial,
           ihf st ρ h.2 g hwf⟩

private theorem translateAll_eval (items : List α) (st : TransState)
    (f : TransCont (Except VerifError α))
    (_hf : ∀ e st', ¬∃ Δ, ScopedM.eval (f (.error e) st') st'.toFlatCtx (.ok ()) Δ)
    (Δ : FlatCtx)
    (h : ScopedM.eval (VerifM.translateAll items st f) st.toFlatCtx (.ok ()) Δ) :
    ∀ a ∈ items, ∃ Δ', ScopedM.eval (f (.ok a) st) st.toFlatCtx (.ok ()) Δ' := by
  induction items with
  | nil => intro _ hmem; simp at hmem
  | cons x xs ih =>
    simp only [VerifM.translateAll] at h
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
    (h : ScopedM.eval (VerifM.translateAny items st f) st.toFlatCtx (.ok ()) Δ) :
    ∃ a ∈ items, ∃ Δ', ScopedM.eval (f (.ok a) st) st.toFlatCtx (.ok ()) Δ' := by
  induction items with
  | nil =>
    simp only [VerifM.translateAny] at h
    exact absurd ⟨Δ, h⟩ (hf (.failed "no alternative") st)
  | cons x xs ih =>
    simp only [VerifM.translateAny] at h
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

private theorem VerifM.translate_eval_rec (m : VerifM α) (st : TransState) (ρ: VerifM.Env)
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
  | declUnaryRel hint τ =>
    simp only [VerifM.translate] at h
    have h := ScopedM.eval_declareUnaryRel h
    simp only [VerifM.eval_rec]
    intro _
    exact ⟨_, h⟩
  | declBinaryRel hint τ₁ τ₂ =>
    simp only [VerifM.translate] at h
    have h := ScopedM.eval_declareBinaryRel h
    simp only [VerifM.eval_rec]
    intro _
    exact ⟨_, h⟩
  | declUnary hint τ₁ τ₂ =>
    simp only [VerifM.translate] at h
    have h := ScopedM.eval_declareUnary h
    simp only [VerifM.eval_rec]
    intro _
    exact ⟨_, h⟩
  | declBinary hint τ₁ τ₂ τ₃ =>
    simp only [VerifM.translate] at h
    have h := ScopedM.eval_declareBinary h
    simp only [VerifM.eval_rec]
    intro _
    exact ⟨_, h⟩
  | declTernary hint τ₁ τ₂ τ₃ τ₄ =>
    simp only [VerifM.translate] at h
    have h := ScopedM.eval_declareTernary h
    simp only [VerifM.eval_rec]
    intro _
    exact ⟨_, h⟩
  | assume item =>
    cases item with
    | pure φ =>
      simp only [VerifM.translate] at h
      have h := ScopedM.eval_assert h
      intro hwf' hφ
      exact ⟨_, h⟩
    | spatial a =>
      simp only [VerifM.translate] at h
      intro hwf'
      exact ⟨_, h⟩
  | check e φ =>
    simp only [VerifM.translate] at h
    obtain ⟨b, _, hxx, hk⟩ := ScopedM.eval_bracket h
    intro hwf'
    refine ⟨b, ?_, ⟨_, hk⟩⟩
    intro hb
    subst hb
    cases e with
    | low =>
      obtain ⟨r, hproof⟩ := ScopedM.eval_probe hxx
      cases r with
      | sat =>
          simp [ScopedM.eval_ret] at hproof
      | unknown =>
          simp [ScopedM.eval_ret] at hproof
      | unsat =>
          apply ScopedM.eval_assert at hproof
          apply ScopedM.eval_checkSat at hproof
          simp at hproof
          rcases hproof with ⟨hunsat, _⟩ | hfalse
          · have hunsat' : ¬Smt.State.satisfiable st.decls (Formula.not φ :: st.asserts) := by
              simp only [FlatCtx.addAssert] at hunsat; exact hunsat
            exact Smt.State.satisfiable.to_impl' st.decls st.asserts hunsat' ρ.env g.asserts
          · simp [ScopedM.eval_ret] at hfalse
    | high =>
      apply ScopedM.eval_assert at hxx
      apply ScopedM.eval_assert at hxx
      apply ScopedM.eval_checkSat at hxx
      simp at hxx
      rcases hxx with ⟨hunsat, _⟩ | hfalse
      · have hunsat' : ¬Smt.State.satisfiable st.decls
            (Formula.not φ :: guardFormula :: st.asserts) := by
          simp only [FlatCtx.addAssert] at hunsat; exact hunsat
        refine Smt.State.satisfiable.to_impl' st.decls (guardFormula :: st.asserts)
          hunsat' ρ.env ?_
        intro ψ hψ
        cases hψ with
        | head => exact g.builtins.guard
        | tail _ hψ => exact g.asserts ψ hψ
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
    intro _
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
def VerifM.eval (m : VerifM α) (st : TransState) (ρ : VerifM.Env) (Q : α → TransState → VerifM.Env → Prop) : Prop :=
  st.wf ∧ st.holdsFor ρ ∧
  m.eval_rec st ρ (fun a st' ρ' => st'.wf ∧ st'.holdsFor ρ' ∧ Q a st' ρ')

/-! ### Structural properties -/

theorem VerifM.eval.wf {m : VerifM α} {st : TransState} {ρ : VerifM.Env} {Q : α → TransState → VerifM.Env → Prop}
    (h : m.eval st ρ Q) : st.wf := h.1

theorem VerifM.eval.holdsFor {m : VerifM α} {st : TransState} {ρ : VerifM.Env} {Q : α → TransState → VerifM.Env → Prop}
    (h : m.eval st ρ Q) : st.holdsFor ρ := h.2.1

theorem VerifM.eval.mono' {m : VerifM α} (ρ : VerifM.Env) (st : TransState) (h : m.eval st ρ P)
    (hPQ : ∀ a st' (ρ' : VerifM.Env), st.decls.Subset st'.decls → VerifM.Env.agreeOn st.decls ρ ρ' →
      st'.wf → st'.holdsFor ρ' → P a st' ρ' → Q a st' ρ') :
    m.eval st ρ Q :=
  ⟨h.1, h.2.1, h.2.2.mono' ρ st fun a st' ρ' hsub hag ⟨hwf', hg', hp⟩ =>
    ⟨hwf', hg', hPQ a st' ρ' hsub hag hwf' hg' hp⟩⟩

theorem VerifM.eval.mono {m : VerifM α} (h : m.eval st ρ P) (hPQ : ∀ a st' ρ', P a st' ρ' → Q a st' ρ') :
    m.eval st ρ Q :=
  h.mono' ρ st fun a st' ρ' _ _ _ _ => hPQ a st' ρ'

theorem VerifM.eval.decls_grow {m : VerifM α} ρ (h : m.eval st ρ P) :
    m.eval st ρ (fun a st' ρ' => st.decls.Subset st'.decls ∧ VerifM.Env.agreeOn st.decls ρ ρ' ∧ P a st' ρ') :=
  h.mono' ρ st fun _ _ _ hsub hag _ _ hp => ⟨hsub, hag, hp⟩

/-! ### Inversion lemmas for VerifM.eval (forward direction) -/

theorem VerifM.eval_ret {a : α} {st : TransState} {ρ : VerifM.Env} {Q : α → TransState → VerifM.Env → Prop}
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



theorem VerifM.eval_failed {st : TransState} {ρ : VerifM.Env} {Q : α → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.failed msg) st ρ Q) : False :=
  h.2.2

theorem VerifM.eval_fatal {st : TransState} {ρ : VerifM.Env} {Q : α → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.fatal msg) st ρ Q) : False :=
  h.2.2

theorem VerifM.eval_decl {hint : Option String} {t : Srt} {st : TransState} {ρ : VerifM.Env}
    {Q : FOL.Const → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.decl hint t) st ρ Q) :
    let c := st.freshConst hint t
    ∀ u, Q c { st with decls := st.decls.addConst c } (ρ.updateConst t c.name u) :=
  fun u => (h.2.2 u).2.2

theorem VerifM.eval_declUnaryRel {hint : Option String} {τ : Srt} {st : TransState} {ρ : VerifM.Env}
    {Q : FOL.UnaryRel → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.declUnaryRel hint τ) st ρ Q) :
    let u := st.freshUnaryRel hint τ
    u.name ∉ st.decls.allNames ∧
    ∀ f, Q u { st with decls := st.decls.addUnaryRel u } (ρ.updateUnaryRel τ u.name f) :=
  ⟨st.freshUnaryRel_fresh hint τ, fun f => (h.2.2 f).2.2⟩

theorem VerifM.eval_declBinaryRel {hint : Option String} {τ₁ τ₂ : Srt} {st : TransState}
    {ρ : VerifM.Env} {Q : FOL.BinaryRel → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.declBinaryRel hint τ₁ τ₂) st ρ Q) :
    let b := st.freshBinaryRel hint τ₁ τ₂
    b.name ∉ st.decls.allNames ∧
    ∀ f, Q b { st with decls := st.decls.addBinaryRel b } (ρ.updateBinaryRel τ₁ τ₂ b.name f) :=
  ⟨st.freshBinaryRel_fresh hint τ₁ τ₂, fun f => (h.2.2 f).2.2⟩

theorem VerifM.eval_declUnary {hint : Option String} {τ₁ τ₂ : Srt} {st : TransState}
    {ρ : VerifM.Env} {Q : FOL.Unary → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.declUnary hint τ₁ τ₂) st ρ Q) :
    let u := st.freshUnary hint τ₁ τ₂
    u.name ∉ st.decls.allNames ∧
    ∀ f, Q u { st with decls := st.decls.addUnary u } (ρ.updateUnary τ₁ τ₂ u.name f) :=
  ⟨st.freshUnary_fresh hint τ₁ τ₂, fun f => (h.2.2 f).2.2⟩

theorem VerifM.eval_declBinary {hint : Option String} {τ₁ τ₂ τ₃ : Srt} {st : TransState}
    {ρ : VerifM.Env} {Q : FOL.Binary → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.declBinary hint τ₁ τ₂ τ₃) st ρ Q) :
    let b := st.freshBinary hint τ₁ τ₂ τ₃
    b.name ∉ st.decls.allNames ∧
    ∀ f, Q b { st with decls := st.decls.addBinary b } (ρ.updateBinary τ₁ τ₂ τ₃ b.name f) :=
  ⟨st.freshBinary_fresh hint τ₁ τ₂ τ₃, fun f => (h.2.2 f).2.2⟩

theorem VerifM.eval_declTernary {hint : Option String} {τ₁ τ₂ τ₃ τ₄ : Srt}
    {st : TransState} {ρ : VerifM.Env}
    {Q : FOL.Ternary → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.declTernary hint τ₁ τ₂ τ₃ τ₄) st ρ Q) :
    let t := st.freshTernary hint τ₁ τ₂ τ₃ τ₄
    t.name ∉ st.decls.allNames ∧
    ∀ f, Q t { st with decls := st.decls.addTernary t }
      (ρ.updateTernary τ₁ τ₂ τ₃ τ₄ t.name f) :=
  ⟨st.freshTernary_fresh hint τ₁ τ₂ τ₃ τ₄, fun f => (h.2.2 f).2.2⟩

theorem VerifM.eval_assumePure {φ : Formula} {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.assume (.pure φ)) st ρ Q) :
    φ.wfIn st.decls → φ.eval ρ.env → Q () { st with asserts := φ :: st.asserts } ρ :=
  fun hwf hφ => (h.2.2 hwf hφ).2.2

theorem VerifM.eval_assumeSpatial {a : SpatialAtom} {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.assume (.spatial a)) st ρ Q) :
    a.wfIn st.decls → Q () { st with owns := a :: st.owns } ρ :=
  fun hwf => (h.2.2 hwf).2.2

theorem VerifM.eval_assume {item : CtxItem} {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.assume item) st ρ Q) :
    item.wfIn st.decls →
    (match item with | .pure φ => φ.eval ρ.env | .spatial _ => True) →
    Q () (st.addItem item) ρ :=
  by
    cases item with
    | pure φ =>
      simp [TransState.addItem]
      exact VerifM.eval_assumePure h
    | spatial a =>
      simp [TransState.addItem]
      exact VerifM.eval_assumeSpatial h

theorem VerifM.eval_check {e : Effort} {φ : Formula} {st : TransState} {ρ : VerifM.Env}
    {Q : Bool → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.check e φ) st ρ Q) :
    φ.wfIn st.decls →
    ∃ b, (b = true → φ.eval ρ.env) ∧ Q b st ρ :=
  fun hwf =>
    let ⟨b, hb, _, _, hq⟩ := h.2.2 hwf
    ⟨b, hb, hq⟩

theorem VerifM.eval_assert {φ : Formula} {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.assert φ) st ρ Q) :
    φ.wfIn st.decls → φ.eval ρ.env ∧ Q () st ρ := by
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
    {msg : String} {actual expected : α} {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.expectEq msg actual expected) st ρ Q) :
    actual = expected ∧ Q () st ρ := by
  unfold VerifM.expectEq at h
  by_cases heq : actual = expected
  · simp [heq] at h
    exact ⟨heq, VerifM.eval_ret h⟩
  · simp [heq] at h
    exact (VerifM.eval_fatal h).elim

theorem VerifM.eval_expectSome
    {msg : String} {x : Option α} {st : TransState} {ρ : VerifM.Env}
    {Q : α → TransState → VerifM.Env → Prop}
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

theorem VerifM.eval_declConstExact {c : FOL.Const} {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.declConstExact c) st ρ Q) :
    c.name ∉ st.decls.allNames ∧
    ∀ v, Q () { st with decls := st.decls.addConst c } (ρ.updateConst c.sort c.name v) := by
  simp only [VerifM.declConstExact] at h
  have hbind := VerifM.eval_decl (VerifM.eval_bind _ _ _ _ h)
  have hname : Fresh.freshNumbers c.name st.decls.allNames = c.name := by
    have hcont0 := hbind default
    obtain ⟨heq, _⟩ := VerifM.eval_expectEq hcont0
    simpa using heq
  refine ⟨?_, ?_⟩
  · have := st.freshConst_fresh (some c.name) c.sort
    simpa [TransState.freshConst, hname] using this
  · intro v
    obtain ⟨_, hq⟩ := VerifM.eval_expectEq (hbind v)
    have hceq : st.freshConst (some c.name) c.sort = c := by
      cases c; simp [TransState.freshConst, hname]
    rw [hceq] at hq
    exact hq

theorem VerifM.eval_declUnaryRelExact {u : FOL.UnaryRel} {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.declUnaryRelExact u) st ρ Q) :
    u.name ∉ st.decls.allNames ∧
    ∀ f, Q () { st with decls := st.decls.addUnaryRel u } (ρ.updateUnaryRel u.arg u.name f) := by
  simp only [VerifM.declUnaryRelExact] at h
  obtain ⟨hfresh, hcont⟩ := VerifM.eval_declUnaryRel (VerifM.eval_bind _ _ _ _ h)
  have hname : Fresh.freshNumbers u.name st.decls.allNames = u.name := by
    have hcont0 := hcont (fun _ => True)
    obtain ⟨heq, _⟩ := VerifM.eval_expectEq hcont0
    simpa using heq
  refine ⟨hname ▸ hfresh, ?_⟩
  intro f
  obtain ⟨_, hq⟩ := VerifM.eval_expectEq (hcont f)
  have hueq : st.freshUnaryRel (some u.name) u.arg = u := by
    cases u; simp [TransState.freshUnaryRel, hname]
  rw [hueq] at hq
  exact hq

theorem VerifM.eval_declBinaryRelExact {b : FOL.BinaryRel} {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.declBinaryRelExact b) st ρ Q) :
    b.name ∉ st.decls.allNames ∧
    ∀ f, Q () { st with decls := st.decls.addBinaryRel b } (ρ.updateBinaryRel b.arg1 b.arg2 b.name f) := by
  simp only [VerifM.declBinaryRelExact] at h
  obtain ⟨hfresh, hcont⟩ := VerifM.eval_declBinaryRel (VerifM.eval_bind _ _ _ _ h)
  have hname : Fresh.freshNumbers b.name st.decls.allNames = b.name := by
    have hcont0 := hcont (fun _ _ => True)
    obtain ⟨heq, _⟩ := VerifM.eval_expectEq hcont0
    simpa using heq
  refine ⟨hname ▸ hfresh, ?_⟩
  intro f
  obtain ⟨_, hq⟩ := VerifM.eval_expectEq (hcont f)
  have hbeq : st.freshBinaryRel (some b.name) b.arg1 b.arg2 = b := by
    cases b; simp [TransState.freshBinaryRel, hname]
  rw [hbeq] at hq
  exact hq

theorem VerifM.eval_declUnaryExact {u : FOL.Unary} {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.declUnaryExact u) st ρ Q) :
    u.name ∉ st.decls.allNames ∧
    ∀ f, Q () { st with decls := st.decls.addUnary u } (ρ.updateUnary u.arg u.ret u.name f) := by
  simp only [VerifM.declUnaryExact] at h
  obtain ⟨hfresh, hcont⟩ := VerifM.eval_declUnary (VerifM.eval_bind _ _ _ _ h)
  have hname : Fresh.freshNumbers u.name st.decls.allNames = u.name := by
    have hcont0 := hcont (fun _ => default)
    obtain ⟨heq, _⟩ := VerifM.eval_expectEq hcont0
    simpa using heq
  refine ⟨hname ▸ hfresh, ?_⟩
  intro f
  obtain ⟨_, hq⟩ := VerifM.eval_expectEq (hcont f)
  have hueq : st.freshUnary (some u.name) u.arg u.ret = u := by
    cases u; simp [TransState.freshUnary, hname]
  rw [hueq] at hq
  exact hq

theorem VerifM.eval_declBinaryExact {b : FOL.Binary} {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.declBinaryExact b) st ρ Q) :
    b.name ∉ st.decls.allNames ∧
    ∀ f, Q () { st with decls := st.decls.addBinary b } (ρ.updateBinary b.arg1 b.arg2 b.ret b.name f) := by
  simp only [VerifM.declBinaryExact] at h
  obtain ⟨hfresh, hcont⟩ := VerifM.eval_declBinary (VerifM.eval_bind _ _ _ _ h)
  have hname : Fresh.freshNumbers b.name st.decls.allNames = b.name := by
    have hcont0 := hcont (fun _ _ => default)
    obtain ⟨heq, _⟩ := VerifM.eval_expectEq hcont0
    simpa using heq
  refine ⟨hname ▸ hfresh, ?_⟩
  intro f
  obtain ⟨_, hq⟩ := VerifM.eval_expectEq (hcont f)
  have hbeq : st.freshBinary (some b.name) b.arg1 b.arg2 b.ret = b := by
    cases b; simp [TransState.freshBinary, hname]
  rw [hbeq] at hq
  exact hq

theorem VerifM.eval_declTernaryExact {t : FOL.Ternary} {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.declTernaryExact t) st ρ Q) :
    t.name ∉ st.decls.allNames ∧
    ∀ f, Q () { st with decls := st.decls.addTernary t }
      (ρ.updateTernary t.arg1 t.arg2 t.arg3 t.ret t.name f) := by
  simp only [VerifM.declTernaryExact] at h
  obtain ⟨hfresh, hcont⟩ := VerifM.eval_declTernary (VerifM.eval_bind _ _ _ _ h)
  have hname : Fresh.freshNumbers t.name st.decls.allNames = t.name := by
    have hcont0 := hcont (fun _ _ _ => default)
    obtain ⟨heq, _⟩ := VerifM.eval_expectEq hcont0
    simpa using heq
  refine ⟨hname ▸ hfresh, ?_⟩
  intro f
  obtain ⟨_, hq⟩ := VerifM.eval_expectEq (hcont f)
  have hteq : st.freshTernary (some t.name) t.arg1 t.arg2 t.arg3 t.ret = t := by
    cases t; simp [TransState.freshTernary, hname]
  rw [hteq] at hq
  exact hq

theorem VerifM.eval_bind_expectEq [DecidableEq α] [Repr α]
    {msg : String} {actual expected : α} {β : Type _} {k : Unit → VerifM β}
    {st : TransState} {ρ : VerifM.Env} {Q : β → TransState → VerifM.Env → Prop}
    (h : VerifM.eval ((VerifM.expectEq msg actual expected).bind k) st ρ Q) :
    actual = expected ∧ VerifM.eval (k ()) st ρ Q := by
  have hb := VerifM.eval_bind _ _ _ _ h
  obtain ⟨heq, hk⟩ := VerifM.eval_expectEq hb
  exact ⟨heq, hk⟩

theorem VerifM.eval_bind_expectSome
    {msg : String} {x : Option α} {β : Type _} {k : α → VerifM β}
    {st : TransState} {ρ : VerifM.Env} {Q : β → TransState → VerifM.Env → Prop}
    (h : VerifM.eval ((VerifM.expectSome msg x).bind k) st ρ Q) :
    ∃ y, x = some y ∧ VerifM.eval (k y) st ρ Q := by
  have hb := VerifM.eval_bind _ _ _ _ h
  obtain ⟨y, hx, hk⟩ := VerifM.eval_expectSome hb
  exact ⟨y, hx, hk⟩

theorem VerifM.eval_all {items : List α} {st : TransState} {ρ : VerifM.Env}
    {Q : α → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.all items) st ρ Q) :
    ∀ a ∈ items, Q a st ρ :=
  fun a ha => (h.2.2 a ha).2.2

theorem VerifM.eval_any {items : List α} {st : TransState} {ρ : VerifM.Env}
    {Q : α → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.any items) st ρ Q) :
    ∃ a ∈ items, Q a st ρ :=
  let ⟨a, ha, _, _, hq⟩ := h.2.2; ⟨a, ha, hq⟩


theorem VerifM.eval_ctx {f : TransState → α × SpatialContext}
    {st : TransState} {ρ : VerifM.Env} {Q : α → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.ctx f) st ρ Q) :
    let (a, owns') := f st
    (owns'.wfIn st.decls → Q a { st with owns := owns' } ρ)
    ∧ st.owns.wfIn st.decls
    ∧ st.holdsFor ρ
    ∧ st.asserts.wfIn st.decls :=
  ⟨fun howns => (h.2.2 howns).2.2, h.1.ownsWf, h.2.1, h.1.assertsWf⟩

theorem VerifM.eval_ctxPure {f : List Formula → α} {st : TransState} {ρ : VerifM.Env}
    {Q : α → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.ctx (fun st => (f st.asserts, st.owns))) st ρ Q) :
    Q (f st.asserts) st ρ
    ∧ st.holdsFor ρ
    ∧ st.asserts.wfIn st.decls :=
  let ⟨hq, howns, hg, hwf⟩ := VerifM.eval_ctx h
  ⟨hq howns, hg, hwf⟩

theorem VerifM.eval_persist {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval VerifM.persist st ρ Q) :
    Q () (TransState.persist st) ρ := by
  let ⟨hq, howns, _, _⟩ := VerifM.eval_ctx h
  apply hq
  simp [TransState.persist]

theorem VerifM.eval_seq {m : VerifM Unit} {m2 : VerifM β} {st : TransState} {ρ : VerifM.Env}
    {Q : β → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (.seq m m2) st ρ Q) :
    VerifM.eval m st ρ (fun () _ _ => True) ∧ VerifM.eval m2 st ρ Q := by
  obtain ⟨hwf, hholds, hm, hm2⟩ := h
  exact ⟨⟨hwf, hholds, (eval_rec_preserves_wf m st ρ hm hholds hwf).mono
    fun () _ _ ⟨hg', hwf', _⟩ => ⟨hwf', hg', trivial⟩⟩,
   ⟨hwf, hholds, hm2⟩⟩

theorem VerifM.eval_assumeAll {φs : List Formula}
    {st : TransState} {ρ : VerifM.Env} {P : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.assumeAll φs) st ρ P) :
    (∀ φ ∈ φs, φ.wfIn st.decls) →
    (∀ φ ∈ φs, φ.eval ρ.env) →
    ∃ st', st'.decls = st.decls ∧ st'.owns = st.owns ∧
           st'.asserts = φs.reverse ++ st.asserts ∧ P () st' ρ := by
  induction φs generalizing st with
  | nil =>
    intro _ _
    simp only [VerifM.assumeAll] at h
    exact ⟨st, rfl, rfl, by simp, VerifM.eval_ret h⟩
  | cons φ φs ih =>
    intro hwf heval
    simp only [VerifM.assumeAll] at h
    have hb := VerifM.eval_bind _ _ _ _ h
    have hassume := VerifM.eval_assumePure hb
    have hcont := hassume
      (hwf φ (List.mem_cons_self ..))
      (heval φ (List.mem_cons_self ..))
    obtain ⟨st', hst', howns, hass, hp⟩ := ih hcont
      (fun ψ hψ => hwf ψ (List.mem_cons_of_mem _ hψ))
      (fun ψ hψ => heval ψ (List.mem_cons_of_mem _ hψ))
    refine ⟨st', by rw [hst'], by rw [howns], ?_, hp⟩
    rw [hass]; simp [List.reverse_cons, List.append_assoc]

theorem VerifM.eval_assumeAxioms {axs : List Axiom}
    {st : TransState} {ρ : VerifM.Env} {P : Unit → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.assumeAxioms axs) st ρ P) :
    (∀ a ∈ axs, a.formula.wfIn st.decls) →
    (∀ a ∈ axs, a.formula.eval ρ.env) →
    ∃ st', st'.decls = st.decls ∧ st'.owns = st.owns ∧
           st'.asserts = (Axiom.asserts axs).reverse ++ st.asserts ∧ P () st' ρ := by
  intro hwf heval
  refine VerifM.eval_assumeAll h ?_ ?_
  · intro φ hφ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hφ
    exact Axiom.assert_wfIn h.1.namesDisjoint h.1.builtins.guard (hwf a ha)
  · intro φ hφ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hφ
    exact Axiom.assert_eval (heval a ha)


/-! ### Top-level corollary -/

def VerifM.topCont : TransCont (Except VerifError Unit) :=
  fun x _ => ScopedM.ret x

theorem VerifM.topCont_error_propagates :
    ∀ e st', ¬∃ Δ, ScopedM.eval (VerifM.topCont (.error e) st') st'.toFlatCtx (.ok ()) Δ := by
  intro e st' ⟨Δ, h⟩
  simp only [topCont, ScopedM.eval_ret] at h
  exact absurd h.1 (by cases e <;> simp)

theorem VerifM.translate_eval (m : VerifM α) (st : TransState) (ρ : VerifM.Env)
    (f : TransCont (Except VerifError α))
    (hf : ∀ e st', ¬∃ Δ, ScopedM.eval (f (.error e) st') st'.toFlatCtx (.ok ()) Δ)
    (Δ : FlatCtx)
    (h : ScopedM.eval (m.translate st f) st.toFlatCtx (.ok ()) Δ)
    (g : st.holdsFor ρ) (hwf : st.wf) :
    VerifM.eval m st ρ (fun a st' _ => ∃ Δ', ScopedM.eval (f (.ok a) st') st'.toFlatCtx (.ok ()) Δ') :=
  ⟨hwf, g, (eval_rec_preserves_wf m st ρ (translate_eval_rec m st ρ f hf Δ h g hwf) g hwf).mono
    fun _ _ _ ⟨hg', hwf', hΔ'⟩ => ⟨hwf', hg', hΔ'⟩⟩

theorem VerifM.eval_of_translate (m : VerifM Unit) (st : TransState) (ρ : VerifM.Env) (Δ : FlatCtx)
    (h : ScopedM.eval (m.translate st topCont) st.toFlatCtx (.ok ()) Δ)
    (g : st.holdsFor ρ) (hwf : st.wf) :
    VerifM.eval m st ρ (fun _ _ _ => True) :=
  (translate_eval m st ρ topCont topCont_error_propagates Δ h g hwf).mono fun _ _ _ _ => trivial

def VerifM.strategy (m : VerifM Unit) :=
  let verif := ScopedM.declareConst guardConst.name guardConst.sort fun () =>
    VerifM.translate m TransState.init VerifM.topCont
  let verif' := ScopedM.bind verif fun
    | .ok () => ScopedM.ret (Except.ok ())
    | .error (.failed msg) => ScopedM.ret (Except.error msg)
    | .error (.fatal msg) => ScopedM.ret (Except.error msg)
  ScopedM.translate verif'
