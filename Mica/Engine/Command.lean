import Mica.FOL.Printing
import Mica.FOL.Subst

/-! ## State

The solver state: a stack of frames, each recording declarations and assertions
added at that push level. -/

/-- A single scope frame: declarations and assertions added in this push level. -/
structure SmtFrame where
  decls : Signature
  asserts : List Formula

/-- The solver state: a stack of frames. -/
structure SmtState where
  frames : List SmtFrame

/-! ## Frame Extension -/

/-- One frame extends another: same fields with possible prepended elements. -/
def SmtFrame.Extends (f f' : SmtFrame) : Prop :=
  ∃ vs cs us bs as,
    f'.decls.vars   = vs ++ f.decls.vars ∧
    f'.decls.consts = cs ++ f.decls.consts ∧
    f'.decls.unary  = us ++ f.decls.unary ∧
    f'.decls.binary = bs ++ f.decls.binary ∧
    f'.asserts = as ++ f.asserts

theorem SmtFrame.Extends.refl (f : SmtFrame) : f.Extends f :=
  ⟨[], [], [], [], [], rfl, rfl, rfl, rfl, rfl⟩

theorem SmtFrame.Extends.addConst (f : SmtFrame) (c : FOL.Const) :
    f.Extends ⟨f.decls.addConst c, f.asserts⟩ :=
  ⟨[], [c], [], [], [], rfl, rfl, rfl, rfl, rfl⟩

theorem SmtFrame.Extends.addUnary (f : SmtFrame) (u : FOL.Unary) :
    f.Extends ⟨f.decls.addUnary u, f.asserts⟩ :=
  ⟨[], [], [u], [], [], rfl, rfl, rfl, rfl, rfl⟩

theorem SmtFrame.Extends.addBinary (f : SmtFrame) (b : FOL.Binary) :
    f.Extends ⟨f.decls.addBinary b, f.asserts⟩ :=
  ⟨[], [], [], [b], [], rfl, rfl, rfl, rfl, rfl⟩

theorem SmtFrame.Extends.addAssert (f : SmtFrame) (φ : Formula) :
    f.Extends ⟨f.decls, φ :: f.asserts⟩ :=
  ⟨[], [], [], [], [φ], rfl, rfl, rfl, rfl, rfl⟩

theorem SmtFrame.Extends.trans {f₁ f₂ f₃ : SmtFrame}
    (h₁₂ : f₁.Extends f₂) (h₂₃ : f₂.Extends f₃) : f₁.Extends f₃ := by
  obtain ⟨vs₁, cs₁, us₁, bs₁, as₁, hv₁, hc₁, hu₁, hb₁, ha₁⟩ := h₁₂
  obtain ⟨vs₂, cs₂, us₂, bs₂, as₂, hv₂, hc₂, hu₂, hb₂, ha₂⟩ := h₂₃
  exact ⟨vs₂ ++ vs₁, cs₂ ++ cs₁, us₂ ++ us₁, bs₂ ++ bs₁, as₂ ++ as₁,
    by simp [hv₂, hv₁, List.append_assoc],
    by simp [hc₂, hc₁, List.append_assoc],
    by simp [hu₂, hu₁, List.append_assoc],
    by simp [hb₂, hb₁, List.append_assoc],
    by simp [ha₂, ha₁, List.append_assoc]⟩

/-! ## SMT Results -/

inductive SmtResult where
  | sat
  | unsat
  | unknown
  deriving BEq, Repr

/-! ## Commands

An SMT command, indexed by its response type.
- push, pop: no meaningful response (Unit)
- declareConst, assert: Unit (Z3 errors abort execution in the driver)
- checkSat: returns sat/unsat/unknown — SmtResult -/

inductive Command : Type → Type where
  | push : Command Unit
  | pop : Command Unit
  | declareConst (name : String) (sort : Srt) : Command Unit
  | declareUnary (name : String) (arg ret : Srt) : Command Unit
  | declareBinary (name : String) (arg1 arg2 ret : Srt) : Command Unit
  | assert (expr : Formula) : Command Unit
  | checkSat : Command SmtResult

/-! ## Serialization -/

/-- Serialize a command to its SMT-LIB2 string. -/
def Command.query : Command α → String
  | .push => "(push)"
  | .pop => "(pop)"
  | .declareConst n s => s!"(declare-const {n} {s.toSMTLIB})"
  | .declareUnary n a r => s!"(declare-fun {n} ({a.toSMTLIB}) {r.toSMTLIB})"
  | .declareBinary n a1 a2 r => s!"(declare-fun {n} ({a1.toSMTLIB} {a2.toSMTLIB}) {r.toSMTLIB})"
  | .assert e => s!"(assert {e.toSMTLIB})"
  | .checkSat => "(check-sat)"

/-- Parse the solver's response string for a given command. Returns `none` on unexpected output. -/
def Command.parseResponse : (cmd : Command α) → String → Option α
  | .push, s => if s == "success" then some () else none
  | .pop, s => if s == "success" then some () else none
  | .declareConst _ _, s => if s == "success" then some () else none
  | .declareUnary _ _ _, s => if s == "success" then some () else none
  | .declareBinary _ _ _ _, s => if s == "success" then some () else none
  | .assert _, s => if s == "success" then some () else none
  | .checkSat, s =>
    if s == "sat" then some .sat
    else if s == "unsat" then some .unsat
    else if s == "unknown" then some .unknown
    else none

/-! ## State Operations -/

namespace SmtState

def initial : SmtState := ⟨[⟨Signature.empty, []⟩]⟩

/-- All declarations visible in the current state (from all frames). -/
def allDecls (s : SmtState) : Signature :=
  ⟨s.frames.flatMap (·.decls.vars),
   s.frames.flatMap (·.decls.consts),
   s.frames.flatMap (·.decls.unary),
   s.frames.flatMap (·.decls.binary)⟩

/-- All assertions active in the current state (from all frames). -/
def allAsserts (s : SmtState) : List Formula :=
  s.frames.flatMap (·.asserts)

def push (s : SmtState) : SmtState :=
  ⟨⟨Signature.empty, []⟩ :: s.frames⟩

def pop (s : SmtState) : SmtState :=
  match s.frames with
  | [] => s  -- underflow: no-op
  | _ :: rest => ⟨rest⟩

def modifyDecls (s : SmtState) (f : Signature → Signature) : SmtState :=
  match s.frames with
  | [] => ⟨[⟨f Signature.empty, []⟩]⟩
  | ⟨decls, asserts⟩ :: rest => ⟨⟨f decls, asserts⟩ :: rest⟩

def addConst (s : SmtState) (c : FOL.Const) : SmtState :=
  s.modifyDecls (·.addConst c)

def addUnary (s : SmtState) (u : FOL.Unary) : SmtState :=
  s.modifyDecls (·.addUnary u)

def addBinary (s : SmtState) (b : FOL.Binary) : SmtState :=
  s.modifyDecls (·.addBinary b)

def addAssert (s : SmtState) (φ : Formula) : SmtState :=
  match s.frames with
  | [] => ⟨[⟨Signature.empty, [φ]⟩]⟩
  | ⟨decls, asserts⟩ :: rest => ⟨⟨decls, φ :: asserts⟩ :: rest⟩

/-- Advance the state by one command (only on success). -/
def step : Command β → β → SmtState → SmtState
  | .push, (), s => s.push
  | .pop, (), s => s.pop
  | .declareConst n sort, (), s => s.addConst ⟨n, sort⟩
  | .declareUnary n arg ret, (), s => s.addUnary ⟨n, arg, ret⟩
  | .declareBinary n arg1 arg2 ret, (), s => s.addBinary ⟨n, arg1, arg2, ret⟩
  | .assert e, (), s => s.addAssert e
  | .checkSat, _, s => s

end SmtState

/-! ## Satisfiable -/

/-- The conjunction of `asserts` is satisfiable under the given declarations.
    That is, there exists an environment making all assertions true simultaneously. -/
def Satisfiable (_decls : Signature) (asserts : List Formula) : Prop :=
  ∃ ρ : Env, ∀ φ ∈ asserts, φ.eval ρ

theorem Satisfiable.to_impl decls asserts :
  ¬ Satisfiable decls (φ :: asserts) →
  ∀ ρ, (∀ ψ ∈ asserts, ψ.eval ρ) → (Formula.not φ).eval ρ :=
  by
    unfold Satisfiable
    intro hsat ρ hasserts
    by_contra hev
    apply hsat
    exists ρ
    intro ψ hψ
    cases hψ with
    | head =>
      simp only [Formula.eval] at hev
      simp at hev
      trivial
    | tail _ hψ =>
      exact (hasserts _ hψ)

theorem Satisfiable.to_impl' decls asserts :
  ¬ Satisfiable decls (Formula.not φ :: asserts) →
  ∀ ρ, (∀ ψ ∈ asserts, ψ.eval ρ) → φ.eval ρ := by
  intro hsat ρ hasserts
  obtain h := (Satisfiable.to_impl decls asserts hsat ρ hasserts)
  simp only [Formula.eval] at h
  simp at h
  trivial
