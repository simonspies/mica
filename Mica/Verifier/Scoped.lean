-- SUMMARY: Scoped SMT command language and its translation to solver strategies and flat contexts.
import Mica.Engine.Strategy

open Smt

/-! ## ScopedM: The SMT Monad

Continuation-based monad over SMT operations. No raw push/pop — scoping
is handled exclusively by `bracket`. Each constructor except `ret` and `bracket`
corresponds to a single SMT command with a continuation receiving the response. -/

inductive ScopedM : Type → Type 1 where
  | ret : α → ScopedM α
  | declareConst : String → Srt → (Unit → ScopedM α) → ScopedM α
  | declareUnary : String → Srt → Srt → (Unit → ScopedM α) → ScopedM α
  | declareBinary : String → Srt → Srt → Srt → (Unit → ScopedM α) → ScopedM α
  | declareTernary : String → Srt → Srt → Srt → Srt → (Unit → ScopedM α) → ScopedM α
  | declareUnaryRel : String → Srt → (Unit → ScopedM α) → ScopedM α
  | declareBinaryRel : String → Srt → Srt → (Unit → ScopedM α) → ScopedM α
  | assert : Formula → (Unit → ScopedM α) → ScopedM α
  | checkSat : (Result → ScopedM α) → ScopedM α
  | setOption : Smt.Options.Settable → (Unit → ScopedM α) → ScopedM α
  | getOption : Smt.Options.Gettable β → (β → ScopedM α) → ScopedM α
  | bracket : ScopedM β → (β → ScopedM α) → ScopedM α

/-! ## translate: ScopedM → Strategy -/

def ScopedM.translate : ScopedM α → Strategy α
  | .ret a => .done a
  | .declareConst n s k => .exec (.declareConst n s) (fun r => translate (k r))
  | .declareUnary n a r k => .exec (.declareUnary n a r) (fun resp => translate (k resp))
  | .declareBinary n a1 a2 r k => .exec (.declareBinary n a1 a2 r) (fun resp => translate (k resp))
  | .declareTernary n a1 a2 a3 r k =>
      .exec (.declareTernary n a1 a2 a3 r) (fun resp => translate (k resp))
  | .declareUnaryRel n a k => .exec (.declareUnaryRel n a) (fun resp => translate (k resp))
  | .declareBinaryRel n a1 a2 k => .exec (.declareBinaryRel n a1 a2) (fun resp => translate (k resp))
  | .assert e k => .exec (.assert e) (fun r => translate (k r))
  | .checkSat k => .exec .checkSat (fun r => translate (k r))
  | .setOption s k => .exec (.setOption s) (fun r => translate (k r))
  | .getOption g k => .exec (.getOption g) (fun r => translate (k r))
  | .bracket body k =>
      .exec .push (fun () =>
        (translate body).bind (fun x =>
          .exec .pop (fun () => translate (k x))))

/-! ## Flat Context

A flat (non-stacked) view of the SMT state: just declarations and assertions.
The stacked State is an implementation detail of the Strategy layer. -/

structure FlatCtx where
  decls : Signature
  asserts : Context

namespace FlatCtx

def empty : FlatCtx := ⟨Signature.empty, []⟩

def addConst (ctx : FlatCtx) (n : String) (sort : Srt) : FlatCtx :=
  ⟨ctx.decls.addConst ⟨n, sort⟩, ctx.asserts⟩

def addUnary (ctx : FlatCtx) (n : String) (arg ret : Srt) : FlatCtx :=
  ⟨ctx.decls.addUnary ⟨n, arg, ret⟩, ctx.asserts⟩

def addBinary (ctx : FlatCtx) (n : String) (arg1 arg2 ret : Srt) : FlatCtx :=
  ⟨ctx.decls.addBinary ⟨n, arg1, arg2, ret⟩, ctx.asserts⟩

def addTernary (ctx : FlatCtx) (n : String) (arg1 arg2 arg3 ret : Srt) : FlatCtx :=
  ⟨ctx.decls.addTernary ⟨n, arg1, arg2, arg3, ret⟩, ctx.asserts⟩

def addUnaryRel (ctx : FlatCtx) (n : String) (arg : Srt) : FlatCtx :=
  ⟨ctx.decls.addUnaryRel ⟨n, arg⟩, ctx.asserts⟩

def addBinaryRel (ctx : FlatCtx) (n : String) (arg1 arg2 : Srt) : FlatCtx :=
  ⟨ctx.decls.addBinaryRel ⟨n, arg1, arg2⟩, ctx.asserts⟩

def addAssert (ctx : FlatCtx) (φ : Formula) : FlatCtx :=
  ⟨ctx.decls, φ :: ctx.asserts⟩

end FlatCtx

namespace Smt.State

/-- The stack seen as one context. The error state has no such view. -/
def flatten : State → Option FlatCtx
  | .frames top rest => some ⟨Frame.allDecls (top :: rest), Frame.allAsserts (top :: rest)⟩
  | .error => none

theorem valid_of_flatten {s : State} {ctx : FlatCtx} (h : s.flatten = some ctx) : s.valid := by
  cases s with
  | frames _ _ => trivial
  | error => simp [flatten] at h

theorem flatten_of_valid {s : State} (hs : s.valid) : ∃ ctx, s.flatten = some ctx := by
  cases s with
  | frames top rest => exact ⟨_, rfl⟩
  | error => exact hs.elim

theorem flatten_addConst (s : State) (c : FOL.Const) :
    (s.addConst c).flatten = s.flatten.map (·.addConst c.name c.sort) := by
  cases s with
  | error => rfl
  | frames top rest =>
    cases top with
    | mk decls asserts =>
      cases decls
      simp [State.flatten, Frame.allDecls, Frame.allAsserts,
        State.modifyTop, State.modifyDecls, State.addConst, FlatCtx.addConst,
        Signature.addConst, List.flatMap, List.cons_append]

theorem flatten_addUnary (s : State) (u : FOL.Unary) :
    (s.addUnary u).flatten = s.flatten.map (·.addUnary u.name u.arg u.ret) := by
  cases s with
  | error => rfl
  | frames top rest =>
    cases top with
    | mk decls asserts =>
      cases decls
      simp [State.flatten, Frame.allDecls, Frame.allAsserts,
        State.modifyTop, State.modifyDecls, State.addUnary, FlatCtx.addUnary,
        Signature.addUnary, List.flatMap, List.cons_append]

theorem flatten_addBinary (s : State) (b : FOL.Binary) :
    (s.addBinary b).flatten = s.flatten.map (·.addBinary b.name b.arg1 b.arg2 b.ret) := by
  cases s with
  | error => rfl
  | frames top rest =>
    cases top with
    | mk decls asserts =>
      cases decls
      simp [State.flatten, Frame.allDecls, Frame.allAsserts,
        State.modifyTop, State.modifyDecls, State.addBinary, FlatCtx.addBinary,
        Signature.addBinary, List.flatMap, List.cons_append]

theorem flatten_addTernary (s : State) (t : FOL.Ternary) :
    (s.addTernary t).flatten = s.flatten.map (·.addTernary t.name t.arg1 t.arg2 t.arg3 t.ret) := by
  cases s with
  | error => rfl
  | frames top rest =>
    cases top with
    | mk decls asserts =>
      cases decls
      simp [State.flatten, Frame.allDecls, Frame.allAsserts,
        State.modifyTop, State.modifyDecls, State.addTernary, FlatCtx.addTernary,
        Signature.addTernary, List.flatMap, List.cons_append]

theorem flatten_addUnaryRel (s : State) (u : FOL.UnaryRel) :
    (s.addUnaryRel u).flatten = s.flatten.map (·.addUnaryRel u.name u.arg) := by
  cases s with
  | error => rfl
  | frames top rest =>
    cases top with
    | mk decls asserts =>
      cases decls
      simp [State.flatten, Frame.allDecls, Frame.allAsserts,
        State.modifyTop, State.modifyDecls, State.addUnaryRel, FlatCtx.addUnaryRel,
        Signature.addUnaryRel, List.flatMap, List.cons_append]

theorem flatten_addBinaryRel (s : State) (b : FOL.BinaryRel) :
    (s.addBinaryRel b).flatten = s.flatten.map (·.addBinaryRel b.name b.arg1 b.arg2) := by
  cases s with
  | error => rfl
  | frames top rest =>
    cases top with
    | mk decls asserts =>
      cases decls
      simp [State.flatten, Frame.allDecls, Frame.allAsserts,
        State.modifyTop, State.modifyDecls, State.addBinaryRel, FlatCtx.addBinaryRel,
        Signature.addBinaryRel, List.flatMap, List.cons_append]

theorem flatten_addAssert (s : State) (φ : Formula) :
    (s.addAssert φ).flatten = s.flatten.map (·.addAssert φ) := by
  cases s with
  | error => rfl
  | frames top rest =>
    cases top
    simp [State.flatten, Frame.allDecls, Frame.allAsserts,
      State.modifyTop, State.addAssert, FlatCtx.addAssert, List.flatMap]

end Smt.State

/-! ## Trace.PreservesFrames and translate_preservesFrames -/

/-- A trace preserves the stack tail and only extends the top frame. -/
def Smt.Trace.PreservesFrames (t : Trace α) (f : Frame) (fs : List Frame) : Prop :=
  ∃ f', f.Extends f' ∧ t.finalState (.frames f fs) = .frames f' fs

/-- Traces generated by `translate m` preserve the stack: they only extend
    the top frame and leave deeper frames unchanged. -/
theorem ScopedM.translate_preservesFrames {m : ScopedM α} {f : Frame} {fs : List Frame}
    {t : Trace α} (hgen : Strategy.generates (translate m) t) :
    t.PreservesFrames f fs := by
  induction m generalizing f fs with
  | ret a =>
    cases hgen
    exact ⟨f, Frame.Extends.refl f, rfl⟩
  | declareConst n s k ih =>
    cases hgen; rename_i rest resp hrest
    cases resp
    dsimp only at hrest
    have ⟨f', hext, hfin⟩ := ih () hrest
      (f := ⟨f.decls.addConst ⟨n, s⟩, f.asserts⟩) (fs := fs)
    refine ⟨f', (Frame.Extends.addConst f ⟨n, s⟩).trans hext, ?_⟩
    simp [Trace.finalState, State.step, State.addConst]; exact hfin
  | declareUnary n a r k ih =>
    cases hgen; rename_i rest resp hrest
    cases resp
    dsimp only at hrest
    have ⟨f', hext, hfin⟩ := ih () hrest
      (f := ⟨f.decls.addUnary ⟨n, a, r⟩, f.asserts⟩) (fs := fs)
    refine ⟨f', (Frame.Extends.addUnary f ⟨n, a, r⟩).trans hext, ?_⟩
    simp [Trace.finalState, State.step, State.addUnary]; exact hfin
  | declareBinary n a1 a2 r k ih =>
    cases hgen; rename_i rest resp hrest
    cases resp
    dsimp only at hrest
    have ⟨f', hext, hfin⟩ := ih () hrest
      (f := ⟨f.decls.addBinary ⟨n, a1, a2, r⟩, f.asserts⟩) (fs := fs)
    refine ⟨f', (Frame.Extends.addBinary f ⟨n, a1, a2, r⟩).trans hext, ?_⟩
    simp [Trace.finalState, State.step, State.addBinary]; exact hfin
  | declareTernary n a1 a2 a3 r k ih =>
    cases hgen; rename_i rest resp hrest
    cases resp
    dsimp only at hrest
    have ⟨f', hext, hfin⟩ := ih () hrest
      (f := ⟨f.decls.addTernary ⟨n, a1, a2, a3, r⟩, f.asserts⟩) (fs := fs)
    refine ⟨f', (Frame.Extends.addTernary f ⟨n, a1, a2, a3, r⟩).trans hext, ?_⟩
    simp [Trace.finalState, State.step, State.addTernary]; exact hfin
  | declareUnaryRel n a k ih =>
    cases hgen; rename_i rest resp hrest
    cases resp
    dsimp only at hrest
    have ⟨f', hext, hfin⟩ := ih () hrest
      (f := ⟨f.decls.addUnaryRel ⟨n, a⟩, f.asserts⟩) (fs := fs)
    refine ⟨f', (Frame.Extends.addUnaryRel f ⟨n, a⟩).trans hext, ?_⟩
    simp [Trace.finalState, State.step, State.addUnaryRel]; exact hfin
  | declareBinaryRel n a1 a2 k ih =>
    cases hgen; rename_i rest resp hrest
    cases resp
    dsimp only at hrest
    have ⟨f', hext, hfin⟩ := ih () hrest
      (f := ⟨f.decls.addBinaryRel ⟨n, a1, a2⟩, f.asserts⟩) (fs := fs)
    refine ⟨f', (Frame.Extends.addBinaryRel f ⟨n, a1, a2⟩).trans hext, ?_⟩
    simp [Trace.finalState, State.step, State.addBinaryRel]; exact hfin
  | assert e k ih =>
    cases hgen; rename_i rest resp hrest
    cases resp
    dsimp only at hrest
    have ⟨f', hext, hfin⟩ := ih () hrest
      (f := ⟨f.decls, e :: f.asserts⟩) (fs := fs)
    refine ⟨f', (Frame.Extends.addAssert f e).trans hext, ?_⟩
    simp [Trace.finalState, State.step, State.addAssert]; exact hfin
  | checkSat k ih =>
    cases hgen; rename_i rest resp hrest
    dsimp only at hrest
    have ⟨f', hext, hfin⟩ := ih resp hrest (f := f) (fs := fs)
    exact ⟨f', hext, by simp [Trace.finalState, State.step]; exact hfin⟩
  | setOption s k ih =>
    cases hgen; rename_i rest resp hrest
    cases resp
    dsimp only at hrest
    have ⟨f', hext, hfin⟩ := ih () hrest (f := f) (fs := fs)
    exact ⟨f', hext, by simp [Trace.finalState, State.step]; exact hfin⟩
  | getOption g k ih =>
    cases hgen; rename_i rest resp hrest
    dsimp only at hrest
    have ⟨f', hext, hfin⟩ := ih resp hrest (f := f) (fs := fs)
    exact ⟨f', hext, by simp [Trace.finalState, State.step]; exact hfin⟩
  | bracket body k ih_body ih_k =>
    simp only [translate] at hgen
    cases hgen; rename_i rest_outer hgen_outer
    dsimp only at hgen_outer
    obtain ⟨a, ts_body, tk_rest, hgen_body, hgen_cont, hres_body, hfin_bind, hres_bind⟩ :=
      Strategy.bind_generates_decompose hgen_outer
    cases hgen_cont; rename_i tk_k hgen_k
    dsimp only at hgen_k
    have hpf_body := @ih_body Frame.empty (f :: fs) ts_body hgen_body
    obtain ⟨fbody, _, hfin_body⟩ := hpf_body
    have hpf_k := ih_k a hgen_k (f := f) (fs := fs)
    obtain ⟨f', hext_k, hfin_k⟩ := hpf_k
    refine ⟨f', hext_k, ?_⟩
    simp only [Trace.finalState, State.step, State.push]
    rw [hfin_bind]
    simp only [hfin_body, Trace.finalState, State.step, State.pop]
    exact hfin_k

/-- A trace of `translate m` never leaves the stack: it starts and ends on a
    frame stack, never on `State.error`. -/
theorem ScopedM.translate_valid {m : ScopedM α} {st : State} {t : Trace α}
    (hgen : Strategy.generates (translate m) t) (hst : st.valid) :
    (t.finalState st).valid := by
  cases st with
  | error => exact hst.elim
  | frames top rest =>
    obtain ⟨_, _, hfin⟩ := translate_preservesFrames (f := top) (fs := rest) hgen
    rw [hfin]
    trivial

/-! ## ScopedM.eval: Extensional Semantics with Flat Contexts

`ScopedM.eval m ctx Φ` wraps Strategy.eval with flattening: the user works with
FlatCtx, and the stacked State is existentially hidden. -/

def ScopedM.eval (m : ScopedM α) (ctx : FlatCtx) (ret : α) (ctx' : FlatCtx) : Prop :=
  ∃ st st', st.flatten = some ctx ∧ st'.flatten = some ctx'
  ∧ Strategy.eval (translate m) st ret st'

/-! ## Correspondence -/

theorem ScopedM.strategy_eval_initial_implies_ScopedM_eval {m : ScopedM α} {ret : α}
    {st' : State} :
    Strategy.eval (translate m) State.initial ret st' →
    ∃ ctx', ScopedM.eval m .empty ret ctx' := by
  rintro ⟨t, hgen, hsound, rfl, hret⟩
  obtain ⟨ctx', hflat'⟩ :=
    State.flatten_of_valid (translate_valid (st := State.initial) hgen trivial)
  exact ⟨ctx', State.initial, _, rfl, hflat', t, hgen, hsound, rfl, hret⟩

/-! ## Inversion Lemmas -/

theorem ScopedM.eval_ret {a : α} {ctx : FlatCtx} {ret : α} {ctx' : FlatCtx} :
    ScopedM.eval (.ret a) ctx ret ctx' ↔ (ret = a ∧ ctx' = ctx) := by
  unfold ScopedM.eval translate
  constructor
  · rintro ⟨st, st', hflat, hflat', heval⟩
    rw [Strategy.eval_done] at heval
    exact ⟨heval.1, Option.some_inj.mp (by rw [← hflat, ← hflat', heval.2])⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨.frames ⟨ctx'.decls, ctx'.asserts⟩ [], .frames ⟨ctx'.decls, ctx'.asserts⟩ [],
      by simp [State.flatten, Frame.allDecls, Frame.allAsserts],
      by simp [State.flatten, Frame.allDecls, Frame.allAsserts],
      Strategy.eval_done.mpr ⟨rfl, rfl⟩⟩

theorem ScopedM.eval_declareConst {n : String} {s : Srt}
    {k : Unit → ScopedM α} {ctx : FlatCtx} {ret : α} {ctx' : FlatCtx} :
    ScopedM.eval (.declareConst n s k) ctx ret ctx' →
      ScopedM.eval (k ()) (ctx.addConst n s) ret ctx' := by
  simp only [ScopedM.eval, translate]
  rintro ⟨st, st', hflat, hflat', heval⟩
  obtain ⟨_, _, heval⟩ := Strategy.eval_exec.mp heval
  exact ⟨st.addConst ⟨n, s⟩, st', by rw [State.flatten_addConst, hflat]; rfl, hflat', heval⟩

theorem ScopedM.eval_declareUnary {n : String} {arg ret : Srt}
    {k : Unit → ScopedM α} {ctx : FlatCtx} {r : α} {ctx' : FlatCtx} :
    ScopedM.eval (.declareUnary n arg ret k) ctx r ctx' →
      ScopedM.eval (k ()) (ctx.addUnary n arg ret) r ctx' := by
  simp only [ScopedM.eval, translate]
  rintro ⟨st, st', hflat, hflat', heval⟩
  obtain ⟨_, _, heval⟩ := Strategy.eval_exec.mp heval
  exact ⟨st.addUnary ⟨n, arg, ret⟩, st', by rw [State.flatten_addUnary, hflat]; rfl, hflat', heval⟩

theorem ScopedM.eval_declareBinary {n : String} {arg1 arg2 ret : Srt}
    {k : Unit → ScopedM α} {ctx : FlatCtx} {r : α} {ctx' : FlatCtx} :
    ScopedM.eval (.declareBinary n arg1 arg2 ret k) ctx r ctx' →
      ScopedM.eval (k ()) (ctx.addBinary n arg1 arg2 ret) r ctx' := by
  simp only [ScopedM.eval, translate]
  rintro ⟨st, st', hflat, hflat', heval⟩
  obtain ⟨_, _, heval⟩ := Strategy.eval_exec.mp heval
  exact ⟨st.addBinary ⟨n, arg1, arg2, ret⟩, st', by rw [State.flatten_addBinary, hflat]; rfl, hflat', heval⟩

theorem ScopedM.eval_declareTernary {n : String} {arg1 arg2 arg3 ret : Srt}
    {k : Unit → ScopedM α} {ctx : FlatCtx} {r : α} {ctx' : FlatCtx} :
    ScopedM.eval (.declareTernary n arg1 arg2 arg3 ret k) ctx r ctx' →
      ScopedM.eval (k ()) (ctx.addTernary n arg1 arg2 arg3 ret) r ctx' := by
  simp only [ScopedM.eval, translate]
  rintro ⟨st, st', hflat, hflat', heval⟩
  obtain ⟨_, _, heval⟩ := Strategy.eval_exec.mp heval
  exact ⟨st.addTernary ⟨n, arg1, arg2, arg3, ret⟩, st', by rw [State.flatten_addTernary, hflat]; rfl, hflat', heval⟩

theorem ScopedM.eval_declareUnaryRel {n : String} {arg : Srt}
    {k : Unit → ScopedM α} {ctx : FlatCtx} {r : α} {ctx' : FlatCtx} :
    ScopedM.eval (.declareUnaryRel n arg k) ctx r ctx' →
      ScopedM.eval (k ()) (ctx.addUnaryRel n arg) r ctx' := by
  simp only [ScopedM.eval, translate]
  rintro ⟨st, st', hflat, hflat', heval⟩
  obtain ⟨_, _, heval⟩ := Strategy.eval_exec.mp heval
  exact ⟨st.addUnaryRel ⟨n, arg⟩, st', by rw [State.flatten_addUnaryRel, hflat]; rfl, hflat', heval⟩

theorem ScopedM.eval_declareBinaryRel {n : String} {arg1 arg2 : Srt}
    {k : Unit → ScopedM α} {ctx : FlatCtx} {r : α} {ctx' : FlatCtx} :
    ScopedM.eval (.declareBinaryRel n arg1 arg2 k) ctx r ctx' →
      ScopedM.eval (k ()) (ctx.addBinaryRel n arg1 arg2) r ctx' := by
  simp only [ScopedM.eval, translate]
  rintro ⟨st, st', hflat, hflat', heval⟩
  obtain ⟨_, _, heval⟩ := Strategy.eval_exec.mp heval
  exact ⟨st.addBinaryRel ⟨n, arg1, arg2⟩, st', by rw [State.flatten_addBinaryRel, hflat]; rfl, hflat', heval⟩

theorem ScopedM.eval_assert {e : Formula}
    {k : Unit → ScopedM α} {ctx : FlatCtx} {ret : α} {ctx' : FlatCtx} :
    ScopedM.eval (.assert e k) ctx ret ctx' →
      ScopedM.eval (k ()) (ctx.addAssert e) ret ctx' := by
  simp only [ScopedM.eval, translate]
  rintro ⟨st, st', hflat, hflat', heval⟩
  obtain ⟨_, _, heval⟩ := Strategy.eval_exec.mp heval
  exact ⟨st.addAssert e, st', by rw [State.flatten_addAssert, hflat]; rfl, hflat', heval⟩

theorem ScopedM.eval_checkSat {k : Result → ScopedM α} {ctx : FlatCtx} {ret : α} {ctx' : FlatCtx} :
    ScopedM.eval (.checkSat k) ctx ret ctx' →
      (¬ State.satisfiable ctx.decls ctx.asserts ∧ ScopedM.eval (k .unsat) ctx ret ctx')
      ∨ ScopedM.eval (k .sat) ctx ret ctx'
      ∨ ScopedM.eval (k .unknown) ctx ret ctx' := by
  simp only [ScopedM.eval, translate]
  rintro ⟨st, st', hflat, hflat', heval⟩
  obtain ⟨resp, hobl, heval⟩ := Strategy.eval_exec.mp heval
  cases resp with
  | sat => right; left; exact ⟨st, st', hflat, hflat', heval⟩
  | unsat =>
    left
    cases st with
    | error => exact (State.valid_of_flatten hflat).elim
    | frames top rest =>
      cases Option.some.inj hflat
      exact ⟨hobl, _, st', hflat, hflat', heval⟩
  | unknown => right; right; exact ⟨st, st', hflat, hflat', heval⟩

theorem ScopedM.eval_setOption {s : Smt.Options.Settable}
    {k : Unit → ScopedM α} {ctx : FlatCtx} {ret : α} {ctx' : FlatCtx} :
    ScopedM.eval (.setOption s k) ctx ret ctx' →
      ScopedM.eval (k ()) ctx ret ctx' := by
  simp only [ScopedM.eval, translate]
  rintro ⟨st, st', hflat, hflat', heval⟩
  obtain ⟨_, _, heval⟩ := Strategy.eval_exec.mp heval
  exact ⟨st, st', hflat, hflat', heval⟩

theorem ScopedM.eval_getOption {g : Smt.Options.Gettable β}
    {k : β → ScopedM α} {ctx : FlatCtx} {ret : α} {ctx' : FlatCtx} :
    ScopedM.eval (.getOption g k) ctx ret ctx' →
      ∃ x, ScopedM.eval (k x) ctx ret ctx' := by
  simp only [ScopedM.eval, translate]
  rintro ⟨st, st', hflat, hflat', heval⟩
  obtain ⟨resp, _, heval⟩ := Strategy.eval_exec.mp heval
  exact ⟨resp, st, st', hflat, hflat', heval⟩

theorem ScopedM.eval_bracket {body : ScopedM β} {k : β → ScopedM α}
    {ctx : FlatCtx} {ret : α} {ctx' : FlatCtx} :
    ScopedM.eval (.bracket body k) ctx ret ctx' →
      ∃ b ctx_body, ScopedM.eval body ctx b ctx_body ∧ ScopedM.eval (k b) ctx ret ctx' := by
  simp only [ScopedM.eval, translate, Strategy.eval]
  intro h
  obtain ⟨st, st', hflat, hflat', t, hgen, hsound, hst', hret⟩ := h
  cases st with
  | error => exact (State.valid_of_flatten hflat).elim
  | frames top rest =>
    -- t = .step .push () bind_trace where bind_trace is (translate body).bind (...)
    cases hgen; rename_i bind_trace _ hgen_bind
    dsimp only at hgen_bind
    have hsound_inner := hsound.step_rest
    -- Decompose the bind trace
    obtain ⟨a, ts_body, tk_rest, hgen_body, hgen_cont, hres_body, hsound_body, hsound_rest,
            hfin_bind, hres_bind⟩ :=
      Strategy.bind_isSound_decompose hgen_bind hsound_inner
    cases hgen_cont; rename_i tk_k _ hgen_k
    dsimp only at hgen_k
    -- Frame preservation: body only extends the pushed frame
    obtain ⟨fbody, _, hfin_body⟩ := @translate_preservesFrames _ body
      (f := Frame.empty) (fs := top :: rest) (t := ts_body) hgen_body
    obtain ⟨ctx_body, hflat_body⟩ :=
      State.flatten_of_valid (translate_valid (st := (State.frames top rest).push) hgen_body trivial)
    refine ⟨ts_body.result, ctx_body, ?_, ?_⟩
    · -- Witness for body: the pushed state, which flattens to ctx
      refine ⟨(State.frames top rest).push, ts_body.finalState (State.frames top rest).push,
        ?_, hflat_body, ts_body, hgen_body, hsound_body, rfl, rfl⟩
      rw [← hflat]
      rfl
    · -- After body: extract isSound for k from the pop step
      simp only [State.step, State.push] at hsound_rest
      rw [hfin_body] at hsound_rest
      simp only [Trace.isSound, State.step, State.pop] at hsound_rest
      -- Simplify hst' through the full trace
      simp only [Trace.finalState, State.step, State.push] at hst'
      rw [hfin_bind, hfin_body] at hst'
      simp only [Trace.finalState, State.step, State.pop] at hst'
      -- Simplify hret
      simp only [Trace.result] at hret
      rw [hres_bind] at hret
      simp only [Trace.result] at hret
      rw [← hres_body] at hgen_k
      exact ⟨.frames top rest, st', hflat, hflat', tk_k, hgen_k, hsound_rest.2, hst', hret⟩

/-! ## ScopedM.bind -/

/-- Bind for ScopedM, derived from the continuation structure. -/
def ScopedM.bind : ScopedM α → (α → ScopedM β) → ScopedM β
  | .ret a, k => k a
  | .declareConst n s cont, k => .declareConst n s (fun r => (cont r).bind k)
  | .declareUnary n a r cont, k => .declareUnary n a r (fun resp => (cont resp).bind k)
  | .declareBinary n a1 a2 r cont, k => .declareBinary n a1 a2 r (fun resp => (cont resp).bind k)
  | .declareTernary n a1 a2 a3 r cont, k => .declareTernary n a1 a2 a3 r (fun resp => (cont resp).bind k)
  | .declareUnaryRel n a cont, k => .declareUnaryRel n a (fun resp => (cont resp).bind k)
  | .declareBinaryRel n a1 a2 cont, k => .declareBinaryRel n a1 a2 (fun resp => (cont resp).bind k)
  | .assert e cont, k => .assert e (fun r => (cont r).bind k)
  | .checkSat cont, k => .checkSat (fun r => (cont r).bind k)
  | .setOption s cont, k => .setOption s (fun r => (cont r).bind k)
  | .getOption g cont, k => .getOption g (fun r => (cont r).bind k)
  | .bracket body cont, k => .bracket body (fun x => (cont x).bind k)

theorem ScopedM.translate_bind (m : ScopedM α) (k : α → ScopedM β) :
    translate (m.bind k) = (translate m).bind (fun a => translate (k a)) := by
  induction m with
  | ret a => simp [ScopedM.bind, translate, Strategy.bind]
  | declareConst n s cont ih =>
    simp only [ScopedM.bind, translate, Strategy.bind]; congr 1; funext r; exact ih r k
  | declareUnary n a r cont ih =>
    simp only [ScopedM.bind, translate, Strategy.bind]; congr 1; funext resp; exact ih resp k
  | declareBinary n a1 a2 r cont ih =>
    simp only [ScopedM.bind, translate, Strategy.bind]; congr 1; funext resp; exact ih resp k
  | declareTernary n a1 a2 a3 r cont ih =>
    simp only [ScopedM.bind, translate, Strategy.bind]; congr 1; funext resp; exact ih resp k
  | declareUnaryRel n a cont ih =>
    simp only [ScopedM.bind, translate, Strategy.bind]; congr 1; funext resp; exact ih resp k
  | declareBinaryRel n a1 a2 cont ih =>
    simp only [ScopedM.bind, translate, Strategy.bind]; congr 1; funext resp; exact ih resp k
  | assert e cont ih =>
    simp only [ScopedM.bind, translate, Strategy.bind]; congr 1; funext r; exact ih r k
  | checkSat cont ih =>
    simp only [ScopedM.bind, translate, Strategy.bind]; congr 1; funext r; exact ih r k
  | setOption s cont ih =>
    simp only [ScopedM.bind, translate, Strategy.bind]; congr 1; funext r; exact ih r k
  | getOption g cont ih =>
    simp only [ScopedM.bind, translate, Strategy.bind]; congr 1; funext r; exact ih r k
  | bracket body cont _ ih_cont =>
    simp only [ScopedM.bind, translate, Strategy.bind]
    congr 1; funext ⟨⟩
    rw [Strategy.bind_assoc]
    congr 1; funext x
    simp only [Strategy.bind]
    congr 1; funext ⟨⟩
    exact ih_cont x k

/-- Bind decomposes into two sequential evaluations. -/
theorem ScopedM.eval_bind {m : ScopedM α} {k : α → ScopedM β}
    {ctx : FlatCtx} {ret : β} {ctx' : FlatCtx} :
    ScopedM.eval (m.bind k) ctx ret ctx' →
      ∃ a ctx_mid, ScopedM.eval m ctx a ctx_mid ∧ ScopedM.eval (k a) ctx_mid ret ctx' := by
  intro h
  simp only [ScopedM.eval, Strategy.eval] at h ⊢
  obtain ⟨st, st', hflat, hflat', t, hgen, hsound, hst', hret⟩ := h
  rw [translate_bind] at hgen
  -- Decompose the bind trace
  obtain ⟨a, ts, tk, hgen_s, hgen_k, hres_s, hsound_s, hsound_k, hfin, hresult⟩ :=
    Strategy.bind_isSound_decompose hgen hsound
  obtain ⟨ctx_mid, hmid⟩ :=
    State.flatten_of_valid (translate_valid hgen_s (State.valid_of_flatten hflat))
  refine ⟨a, ctx_mid, ?_, ?_⟩
  · exact ⟨st, ts.finalState st, hflat, hmid, ts, hgen_s, hsound_s, rfl, hres_s.symm⟩
  · refine ⟨ts.finalState st, st', hmid, hflat', tk, ?_, hsound_k, ?_, ?_⟩
    · subst hres_s; exact hgen_k
    · rw [← hfin, hst']
    · rw [← hresult, hret]


/-! ## ScopedM.probe -/

/-- The solver time budget for heuristic probes. A timeout is reported as
    `unknown` and handled conservatively by the caller. -/
def ScopedM.probeTimeout : Nat := 100 /- 100ms -/

/-- A probe: a quick, scoped peek at whether `φ` is consistent with the current
    context. The answer only steers the verifier; it is never a soundness
    justification, which is reflected in `eval_probe` yielding an arbitrary
    result. Accordingly, the probe runs under a short solver timeout, restoring
    the ambient timeout afterwards. -/
def ScopedM.probe (φ : Formula) (k : Result → ScopedM α) : ScopedM α :=
  .getOption .timeout (fun ambient =>
    .setOption (.timeout probeTimeout) (fun () =>
      .bracket (.assert φ (fun () => .checkSat .ret)) (fun r =>
        .setOption (.timeout ambient) (fun () => k r))))

/-- A probe leaves the context unchanged and hands the continuation an
    arbitrary result: nothing about the solver's answer can be trusted. -/
theorem ScopedM.eval_probe {φ : Formula} {k : Result → ScopedM α}
    {ctx : FlatCtx} {ret : α} {ctx' : FlatCtx} :
    ScopedM.eval (.probe φ k) ctx ret ctx' →
      ∃ r, ScopedM.eval (k r) ctx ret ctx' := by
  intro h
  obtain ⟨n, h⟩ := eval_getOption h
  have h := eval_setOption h
  obtain ⟨r, _, _, h⟩ := eval_bracket h
  exact ⟨r, eval_setOption h⟩
