-- SUMMARY: The sequential verification monad: declarations, assumptions, and bracketed checks, composed without branching so that a run returns a value.
import Mica.Verifier.Monad

open Smt

/-!
# Sequential verification

`SeqM` declares symbols under their own names, assumes formulas, and runs
`VerifM` checks in brackets. It does not branch. So, unlike `VerifM`, a run of
`SeqM` returns a value to its caller: a `VerifM` value would have to be chosen
among the branches.

`SeqM` threads the `TransState` that `VerifM` threads. Its semantics `SeqM.eval`
has the shape of `VerifM.eval`: a declaration holds for every interpretation of
the new symbol, an assumption continues under the assumed formula, and a check
gives the `VerifM.eval` of the bracketed run.
-/

inductive SeqM : Type → Type 1 where
  | ret : α → SeqM α
  | bind : SeqM α → (α → SeqM β) → SeqM β
  /-- Declare a constant under its own name, which must be new. -/
  | declConst : Decl.Const → SeqM Unit
  | declUnary : Decl.Unary → SeqM Unit
  | declBinary : Decl.Binary → SeqM Unit
  | declTernary : Decl.Ternary → SeqM Unit
  | declUnaryRel : Decl.UnaryRel → SeqM Unit
  | declBinaryRel : Decl.BinaryRel → SeqM Unit
  | assume : Formula → SeqM Unit
  /-- Run a check in a bracket. Its declarations and assumptions do not stay. -/
  | check : VerifM Unit → SeqM Unit
  | fatal : String → SeqM α
  | decls : SeqM Signature

instance : Monad SeqM where
  pure := .ret
  bind := .bind

namespace SeqM

def ofExcept : Except String α → SeqM α
  | .ok a => .ret a
  | .error e => .fatal e

def assumeAll : List Formula → SeqM Unit
  | [] => .ret ()
  | φ :: φs => .bind (.assume φ) fun () => assumeAll φs

def assumeAxioms (axs : List Axiom) : SeqM Unit :=
  assumeAll (Axiom.asserts axs)

/-! ## Translation -/

private def declared (name : String) : ScopedM (Except String (Unit × TransState)) :=
  .ret (.error s!"symbol {name} is declared twice")

def translate : SeqM α → TransState → ScopedM (Except String (α × TransState))
  | .ret a, st => .ret (.ok (a, st))
  | .bind m f, st => ScopedM.bind (m.translate st) fun
      | .error e => .ret (.error e)
      | .ok (a, st') => (f a).translate st'
  | .declConst c, st =>
      if c.name ∈ st.decls.allNames then declared c.name
      else .declareConst c.name c.sort fun () =>
        .ret (.ok ((), { st with decls := st.decls.addConst c }))
  | .declUnary u, st =>
      if u.name ∈ st.decls.allNames then declared u.name
      else .declareUnary u.name u.arg u.ret fun () =>
        .ret (.ok ((), { st with decls := st.decls.addUnary u }))
  | .declBinary b, st =>
      if b.name ∈ st.decls.allNames then declared b.name
      else .declareBinary b.name b.arg1 b.arg2 b.ret fun () =>
        .ret (.ok ((), { st with decls := st.decls.addBinary b }))
  | .declTernary t, st =>
      if t.name ∈ st.decls.allNames then declared t.name
      else .declareTernary t.name t.arg1 t.arg2 t.arg3 t.ret fun () =>
        .ret (.ok ((), { st with decls := st.decls.addTernary t }))
  | .declUnaryRel u, st =>
      if u.name ∈ st.decls.allNames then declared u.name
      else .declareUnaryRel u.name u.arg fun () =>
        .ret (.ok ((), { st with decls := st.decls.addUnaryRel u }))
  | .declBinaryRel b, st =>
      if b.name ∈ st.decls.allNames then declared b.name
      else .declareBinaryRel b.name b.arg1 b.arg2 fun () =>
        .ret (.ok ((), { st with decls := st.decls.addBinaryRel b }))
  | .assume φ, st => .assert φ fun () =>
      .ret (.ok ((), { st with asserts := φ :: st.asserts }))
  | .check m, st => .bracket (m.translate st VerifM.topCont) fun
      | .ok () => .ret (.ok ((), st))
      | .error (.failed msg) | .error (.fatal msg) => .ret (.error msg)
  | .fatal msg, _ => .ret (.error msg)
  | .decls, st => .ret (.ok (st.decls, st))

theorem translate_bind_ok {m : SeqM α} {f : α → SeqM β}
    {st st' : TransState} {ctx ctx' : FlatCtx} {b : β}
    (h : ScopedM.eval ((m >>= f).translate st) ctx (.ok (b, st')) ctx') :
    ∃ a st₁ ctx₁, ScopedM.eval (m.translate st) ctx (.ok (a, st₁)) ctx₁ ∧
      ScopedM.eval ((f a).translate st₁) ctx₁ (.ok (b, st')) ctx' := by
  change ScopedM.eval (SeqM.translate (.bind m f) st) ctx (.ok (b, st')) ctx' at h
  simp only [SeqM.translate] at h
  obtain ⟨r, ctx₁, hm, hf⟩ := ScopedM.eval_bind h
  cases r with
  | error e => have he := (ScopedM.eval_ret.mp hf).1; cases he
  | ok r => exact ⟨r.1, r.2, ctx₁, hm, hf⟩

/-! ## Semantics -/

private def eval_rec : SeqM α → TransState → Env → (α → TransState → Env → Prop) → Prop
  | .ret a, st, ρ, P => P a st ρ
  | .bind m f, st, ρ, P => m.eval_rec st ρ fun a st' ρ' => (f a).eval_rec st' ρ' P
  | .declConst c, st, ρ, P => c.name ∉ st.decls.allNames ∧
      ∀ u, P () { st with decls := st.decls.addConst c } (ρ.updateConst c.sort c.name u)
  | .declUnary u, st, ρ, P => u.name ∉ st.decls.allNames ∧
      ∀ f, P () { st with decls := st.decls.addUnary u } (ρ.updateUnary u.arg u.ret u.name f)
  | .declBinary b, st, ρ, P => b.name ∉ st.decls.allNames ∧
      ∀ f, P () { st with decls := st.decls.addBinary b }
        (ρ.updateBinary b.arg1 b.arg2 b.ret b.name f)
  | .declTernary t, st, ρ, P => t.name ∉ st.decls.allNames ∧
      ∀ f, P () { st with decls := st.decls.addTernary t }
        (ρ.updateTernary t.arg1 t.arg2 t.arg3 t.ret t.name f)
  | .declUnaryRel u, st, ρ, P => u.name ∉ st.decls.allNames ∧
      ∀ f, P () { st with decls := st.decls.addUnaryRel u } (ρ.updateUnaryRel u.arg u.name f)
  | .declBinaryRel b, st, ρ, P => b.name ∉ st.decls.allNames ∧
      ∀ f, P () { st with decls := st.decls.addBinaryRel b }
        (ρ.updateBinaryRel b.arg1 b.arg2 b.name f)
  | .assume φ, st, ρ, P =>
      φ.wfIn st.decls → φ.eval ρ → P () { st with asserts := φ :: st.asserts } ρ
  | .check m, st, ρ, P => VerifM.eval m st ρ (fun _ _ _ => True) ∧ P () st ρ
  | .fatal _, _, _, _ => False
  | .decls, st, ρ, P => P st.decls st ρ

private theorem eval_rec_mono {m : SeqM α} {st : TransState} {ρ : Env}
    {P Q : α → TransState → Env → Prop} (h : m.eval_rec st ρ P)
    (hPQ : ∀ a st' ρ', P a st' ρ' → Q a st' ρ') : m.eval_rec st ρ Q := by
  induction m generalizing st ρ with
  | ret => exact hPQ _ _ _ h
  | bind m f ihm ihf => exact ihm h fun _ _ _ hr => ihf _ hr hPQ
  | declConst | declUnary | declBinary | declTernary | declUnaryRel | declBinaryRel =>
    exact ⟨h.1, fun u => hPQ _ _ _ (h.2 u)⟩
  | assume => exact fun hwf hφ => hPQ _ _ _ (h hwf hφ)
  | check => exact ⟨h.1, hPQ _ _ _ h.2⟩
  | fatal => exact h.elim
  | decls => exact hPQ _ _ _ h

private theorem holdsFor_of_agree {st : TransState} {Δ : Signature} {ρ ρ' : Env}
    (g : st.holdsFor ρ) (hwf : st.wf) (hagree : Env.agreeOn st.decls ρ ρ') :
    ({ st with decls := Δ } : TransState).holdsFor ρ' :=
  ⟨fun φ hφ => (Formula.eval_agreeOn (hwf.assertsWf φ hφ) hagree).mp (g.asserts φ hφ),
   g.builtins.agree hwf.builtins hagree⟩

private theorem eval_rec_preserves_wf (m : SeqM α) (st : TransState) (ρ : Env)
    (h : m.eval_rec st ρ P) (g : st.holdsFor ρ) (hwf : st.wf) :
    m.eval_rec st ρ (fun a st' ρ' => st'.holdsFor ρ' ∧ st'.wf ∧ P a st' ρ') := by
  induction m generalizing st ρ with
  | ret => exact ⟨g, hwf, h⟩
  | bind m f ihm ihf =>
    simp only [eval_rec] at h ⊢
    exact eval_rec_mono (ihm st ρ h g hwf) fun _ _ _ ⟨g', hwf', hr⟩ => ihf _ _ _ hr g' hwf'
  | declConst c =>
    exact ⟨h.1, fun u => ⟨holdsFor_of_agree g hwf (Env.agreeOn_update_fresh_const h.1),
      TransState.wf_addConst st c hwf h.1, h.2 u⟩⟩
  | declUnary u =>
    exact ⟨h.1, fun f => ⟨holdsFor_of_agree g hwf (Env.agreeOn_update_fresh_unary h.1),
      TransState.wf_addUnary st u hwf h.1, h.2 f⟩⟩
  | declBinary b =>
    exact ⟨h.1, fun f => ⟨holdsFor_of_agree g hwf (Env.agreeOn_update_fresh_binary h.1),
      TransState.wf_addBinary st b hwf h.1, h.2 f⟩⟩
  | declTernary t =>
    exact ⟨h.1, fun f => ⟨holdsFor_of_agree g hwf (Env.agreeOn_update_fresh_ternary h.1),
      TransState.wf_addTernary st t hwf h.1, h.2 f⟩⟩
  | declUnaryRel u =>
    exact ⟨h.1, fun f => ⟨holdsFor_of_agree g hwf (Env.agreeOn_update_fresh_unaryRel h.1),
      TransState.wf_addUnaryRel st u hwf h.1, h.2 f⟩⟩
  | declBinaryRel b =>
    exact ⟨h.1, fun f => ⟨holdsFor_of_agree g hwf (Env.agreeOn_update_fresh_binaryRel h.1),
      TransState.wf_addBinaryRel st b hwf h.1, h.2 f⟩⟩
  | assume φ =>
    intro hφwf hφ
    refine ⟨⟨fun ψ hψ => ?_, g.builtins⟩, TransState.wf_addAssert _ hwf hφwf, h hφwf hφ⟩
    cases hψ with
    | head => exact hφ
    | tail _ hψ => exact g.asserts ψ hψ
  | check => exact ⟨h.1, g, hwf, h.2⟩
  | fatal => exact h.elim
  | decls => exact ⟨g, hwf, h⟩

/-- `m` runs from `st` and its assumptions hold under `ρ`: every outcome
    satisfies `Q`, and the verifier state stays well-formed and true. -/
def eval (m : SeqM α) (st : TransState) (ρ : Env) (Q : α → TransState → Env → Prop) : Prop :=
  st.wf ∧ st.holdsFor ρ ∧ m.eval_rec st ρ fun a st' ρ' => st'.wf ∧ st'.holdsFor ρ' ∧ Q a st' ρ'

theorem eval_wf {m : SeqM α} {st : TransState} {ρ : Env} {Q : α → TransState → Env → Prop}
    (h : m.eval st ρ Q) : st.wf := h.1

theorem eval_holdsFor {m : SeqM α} {st : TransState} {ρ : Env}
    {Q : α → TransState → Env → Prop} (h : m.eval st ρ Q) : st.holdsFor ρ := h.2.1

theorem eval_mono {m : SeqM α} {st : TransState} {ρ : Env}
    {P Q : α → TransState → Env → Prop} (h : m.eval st ρ P)
    (hPQ : ∀ a st' ρ', P a st' ρ' → Q a st' ρ') : m.eval st ρ Q :=
  ⟨h.1, h.2.1, eval_rec_mono h.2.2 fun a st' ρ' ⟨hwf', g', hp⟩ => ⟨hwf', g', hPQ a st' ρ' hp⟩⟩

theorem eval_ret {a : α} {st : TransState} {ρ : Env} {Q : α → TransState → Env → Prop}
    (h : (SeqM.ret a).eval st ρ Q) : Q a st ρ :=
  h.2.2.2.2

theorem eval_bind {m : SeqM α} {k : α → SeqM β} {st : TransState} {ρ : Env}
    {Q : β → TransState → Env → Prop} (h : (m.bind k).eval st ρ Q) :
    m.eval st ρ fun a st' ρ' => (k a).eval st' ρ' Q := by
  obtain ⟨hwf, g, h⟩ := h
  refine ⟨hwf, g, eval_rec_mono (eval_rec_preserves_wf m st ρ h g hwf) ?_⟩
  intro a st' ρ' ⟨g', hwf', hk⟩
  exact ⟨hwf', g', hwf', g', hk⟩

theorem eval_fatal {st : TransState} {ρ : Env} {Q : α → TransState → Env → Prop}
    (h : (SeqM.fatal msg : SeqM α).eval st ρ Q) : False :=
  h.2.2

theorem eval_decls {st : TransState} {ρ : Env} {Q : Signature → TransState → Env → Prop}
    (h : SeqM.decls.eval st ρ Q) : Q st.decls st ρ :=
  h.2.2.2.2

theorem eval_ofExcept {e : Except String α} {st : TransState} {ρ : Env}
    {Q : α → TransState → Env → Prop} (h : (ofExcept e).eval st ρ Q) :
    ∃ a, e = .ok a ∧ Q a st ρ := by
  cases e with
  | error => exact (eval_fatal h).elim
  | ok a => exact ⟨a, rfl, eval_ret h⟩

theorem eval_declConst {c : Decl.Const} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop} (h : (SeqM.declConst c).eval st ρ Q) :
    c.name ∉ st.decls.allNames ∧
    ∀ u, Q () { st with decls := st.decls.addConst c } (ρ.updateConst c.sort c.name u) :=
  ⟨h.2.2.1, fun u => (h.2.2.2 u).2.2⟩

theorem eval_declUnary {u : Decl.Unary} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop} (h : (SeqM.declUnary u).eval st ρ Q) :
    u.name ∉ st.decls.allNames ∧
    ∀ f, Q () { st with decls := st.decls.addUnary u } (ρ.updateUnary u.arg u.ret u.name f) :=
  ⟨h.2.2.1, fun f => (h.2.2.2 f).2.2⟩

theorem eval_declBinary {b : Decl.Binary} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop} (h : (SeqM.declBinary b).eval st ρ Q) :
    b.name ∉ st.decls.allNames ∧
    ∀ f, Q () { st with decls := st.decls.addBinary b }
      (ρ.updateBinary b.arg1 b.arg2 b.ret b.name f) :=
  ⟨h.2.2.1, fun f => (h.2.2.2 f).2.2⟩

theorem eval_declTernary {t : Decl.Ternary} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop} (h : (SeqM.declTernary t).eval st ρ Q) :
    t.name ∉ st.decls.allNames ∧
    ∀ f, Q () { st with decls := st.decls.addTernary t }
      (ρ.updateTernary t.arg1 t.arg2 t.arg3 t.ret t.name f) :=
  ⟨h.2.2.1, fun f => (h.2.2.2 f).2.2⟩

theorem eval_declUnaryRel {u : Decl.UnaryRel} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop} (h : (SeqM.declUnaryRel u).eval st ρ Q) :
    u.name ∉ st.decls.allNames ∧
    ∀ f, Q () { st with decls := st.decls.addUnaryRel u } (ρ.updateUnaryRel u.arg u.name f) :=
  ⟨h.2.2.1, fun f => (h.2.2.2 f).2.2⟩

theorem eval_declBinaryRel {b : Decl.BinaryRel} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop} (h : (SeqM.declBinaryRel b).eval st ρ Q) :
    b.name ∉ st.decls.allNames ∧
    ∀ f, Q () { st with decls := st.decls.addBinaryRel b }
      (ρ.updateBinaryRel b.arg1 b.arg2 b.name f) :=
  ⟨h.2.2.1, fun f => (h.2.2.2 f).2.2⟩

theorem eval_assume {φ : Formula} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop} (h : (SeqM.assume φ).eval st ρ Q) :
    φ.wfIn st.decls → φ.eval ρ → Q () { st with asserts := φ :: st.asserts } ρ :=
  fun hwf hφ => (h.2.2 hwf hφ).2.2

theorem eval_check {m : VerifM Unit} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop} (h : (SeqM.check m).eval st ρ Q) :
    VerifM.eval m st ρ (fun _ _ _ => True) ∧ Q () st ρ :=
  ⟨h.2.2.1, h.2.2.2.2.2⟩

theorem eval_assumeAll {φs : List Formula} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop} (h : (assumeAll φs).eval st ρ Q) :
    (∀ φ ∈ φs, φ.wfIn st.decls) → (∀ φ ∈ φs, φ.eval ρ) →
    ∃ st', st'.decls = st.decls ∧ st'.owns = st.owns ∧
      st'.asserts = φs.reverse ++ st.asserts ∧ Q () st' ρ := by
  induction φs generalizing st with
  | nil => exact fun _ _ => ⟨st, rfl, rfl, by simp, eval_ret h⟩
  | cons φ φs ih =>
    intro hwf heval
    have hcont := eval_assume (eval_bind h) (hwf φ (.head _)) (heval φ (.head _))
    obtain ⟨st', hdecls, howns, hasserts, hq⟩ := ih hcont
      (fun ψ hψ => hwf ψ (.tail _ hψ)) (fun ψ hψ => heval ψ (.tail _ hψ))
    exact ⟨st', hdecls, howns, by rw [hasserts]; simp, hq⟩

theorem eval_assumeAxioms {axs : List Axiom} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop} (h : (assumeAxioms axs).eval st ρ Q) :
    (∀ a ∈ axs, a.formula.wfIn st.decls) → (∀ a ∈ axs, a.formula.eval ρ) →
    ∃ st', st'.decls = st.decls ∧ st'.owns = st.owns ∧
      st'.asserts = (Axiom.asserts axs).reverse ++ st.asserts ∧ Q () st' ρ := by
  intro hwf heval
  refine eval_assumeAll h ?_ ?_
  · intro φ hφ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hφ
    exact Axiom.assert_wfIn h.1.namesDisjoint h.1.builtins.guard (hwf a ha)
  · intro φ hφ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hφ
    exact Axiom.assert_eval (heval a ha)

/-! ## From a run to the semantics -/

private theorem translate_eval_rec (m : SeqM α) (st : TransState) (ρ : Env)
    {a : α} {st' : TransState} {ctx' : FlatCtx}
    (h : ScopedM.eval (m.translate st) st.toFlatCtx (.ok (a, st')) ctx')
    (g : st.holdsFor ρ) (hwf : st.wf) :
    m.eval_rec st ρ fun a' st'' _ => a' = a ∧ st'' = st' ∧ ctx' = st'.toFlatCtx := by
  induction m generalizing st ρ st' ctx' with
  | ret =>
    obtain ⟨hr, hctx⟩ := ScopedM.eval_ret.mp h
    cases hr
    exact ⟨rfl, rfl, hctx⟩
  | bind m f ihm ihf =>
    simp only [translate] at h
    obtain ⟨r, ctx_mid, hm, hk⟩ := ScopedM.eval_bind h
    rcases r with e | ⟨a₁, st₁⟩
    · obtain ⟨hr, _⟩ := ScopedM.eval_ret.mp hk
      cases hr
    have hm' := eval_rec_preserves_wf m st ρ (ihm st ρ hm g hwf) g hwf
    simp only [eval_rec]
    refine eval_rec_mono hm' ?_
    rintro a' st'' ρ' ⟨g', hwf', rfl, rfl, rfl⟩
    exact ihf a' st'' ρ' hk g' hwf'
  | declConst c | declUnary c | declBinary c | declTernary c | declUnaryRel c
  | declBinaryRel c =>
    simp only [translate] at h
    split at h
    · obtain ⟨hr, _⟩ := ScopedM.eval_ret.mp h
      cases hr
    · rename_i hfresh
      first
        | have h := ScopedM.eval_declareConst h
        | have h := ScopedM.eval_declareUnary h
        | have h := ScopedM.eval_declareBinary h
        | have h := ScopedM.eval_declareTernary h
        | have h := ScopedM.eval_declareUnaryRel h
        | have h := ScopedM.eval_declareBinaryRel h
      obtain ⟨hr, hctx⟩ := ScopedM.eval_ret.mp h
      cases hr
      exact ⟨hfresh, fun _ => ⟨rfl, rfl, by rw [hctx]; cases c; rfl⟩⟩
  | assume φ =>
    simp only [translate] at h
    have h := ScopedM.eval_assert h
    obtain ⟨hr, hctx⟩ := ScopedM.eval_ret.mp h
    cases hr
    exact fun _ _ => ⟨rfl, rfl, by rw [hctx]; rfl⟩
  | check m =>
    simp only [translate] at h
    obtain ⟨b, ctx_body, hbody, hk⟩ := ScopedM.eval_bracket h
    rcases b with e | ⟨⟩
    · rcases e with msg | msg <;>
      · obtain ⟨hr, _⟩ := ScopedM.eval_ret.mp hk
        cases hr
    obtain ⟨hr, hctx⟩ := ScopedM.eval_ret.mp hk
    cases hr
    exact ⟨VerifM.eval_of_translate m st ρ ctx_body hbody g hwf, rfl, rfl, hctx⟩
  | fatal =>
    obtain ⟨hr, _⟩ := ScopedM.eval_ret.mp h
    cases hr
  | decls =>
    obtain ⟨hr, hctx⟩ := ScopedM.eval_ret.mp h
    cases hr
    exact ⟨rfl, rfl, hctx⟩

/-- A run of `m` that ends in `a` and `st'` gives the semantics of `m`, with
    that outcome as its only outcome. -/
theorem eval_of_translate (m : SeqM α) (st : TransState) (ρ : Env)
    {a : α} {st' : TransState} {ctx' : FlatCtx}
    (h : ScopedM.eval (m.translate st) st.toFlatCtx (.ok (a, st')) ctx')
    (g : st.holdsFor ρ) (hwf : st.wf) :
    m.eval st ρ fun a' st'' _ => a' = a ∧ st'' = st' ∧ ctx' = st'.toFlatCtx :=
  ⟨hwf, g, eval_rec_mono (eval_rec_preserves_wf m st ρ (translate_eval_rec m st ρ h g hwf) g hwf)
    fun _ _ _ ⟨g', hwf', hq⟩ => ⟨hwf', g', hq⟩⟩

end SeqM

/-- Run `m` from the initial state, with the guard constant declared. -/
def SeqM.strategy (m : SeqM α) : Strategy (Except String α) :=
  ScopedM.translate <|
    .declareConst guardConst.name guardConst.sort fun () =>
      ScopedM.bind (m.translate TransState.init) fun
        | .error e => .ret (.error e)
        | .ok (a, _) => .ret (.ok a)

/-- A successful run of `SeqM.strategy` gives the semantics of `m` in every
    environment of the initial state, with the result of the run. -/
theorem SeqM.strategy_correct {m : SeqM α} {a : α} {s : Smt.State}
    (h : m.strategy.eval Smt.State.initial (.ok a) s)
    (ρ : Env) (hρ : TransState.init.holdsFor ρ) :
    m.eval TransState.init ρ fun a' _ _ => a' = a := by
  obtain ⟨_, h1⟩ := ScopedM.strategy_eval_initial_implies_ScopedM_eval h
  have h1 := ScopedM.eval_declareConst h1
  obtain ⟨r, _, hm, hcont⟩ := ScopedM.eval_bind h1
  rcases r with e | ⟨a', st⟩
  · obtain ⟨hr, _⟩ := ScopedM.eval_ret.mp hcont
    cases hr
  obtain ⟨hr, _⟩ := ScopedM.eval_ret.mp hcont
  cases hr
  exact SeqM.eval_mono (SeqM.eval_of_translate _ _ ρ hm hρ TransState.init_wf)
    fun _ _ _ ⟨ha, _⟩ => ha
