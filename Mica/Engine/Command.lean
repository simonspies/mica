import Mica.FOL.Printing
import Mica.FOL.Subst

/-! ## State

The solver state: a stack of frames, each recording declarations and assertions
added at that push level. -/

/-- A single scope frame: declarations and assertions added in this push level. -/
structure SmtFrame where
  decls : VarCtx
  asserts : List Formula

/-- The solver state: a stack of frames. -/
structure SmtState where
  frames : List SmtFrame

/-! ## Frame Extension -/

/-- One frame extends another: same fields with possible prepended elements. -/
def SmtFrame.Extends (f f' : SmtFrame) : Prop :=
  ∃ ds as, f'.decls = ds ++ f.decls ∧ f'.asserts = as ++ f.asserts

theorem SmtFrame.Extends.refl (f : SmtFrame) : f.Extends f :=
  ⟨[], [], rfl, rfl⟩

theorem SmtFrame.Extends.addDecl (f : SmtFrame) (v : Var) :
    f.Extends ⟨v :: f.decls, f.asserts⟩ :=
  ⟨[v], [], rfl, rfl⟩

theorem SmtFrame.Extends.addAssert (f : SmtFrame) (φ : Formula) :
    f.Extends ⟨f.decls, φ :: f.asserts⟩ :=
  ⟨[], [φ], rfl, rfl⟩

theorem SmtFrame.Extends.trans {f₁ f₂ f₃ : SmtFrame}
    (h₁₂ : f₁.Extends f₂) (h₂₃ : f₂.Extends f₃) : f₁.Extends f₃ := by
  obtain ⟨ds₁, as₁, hd₁, ha₁⟩ := h₁₂
  obtain ⟨ds₂, as₂, hd₂, ha₂⟩ := h₂₃
  exact ⟨ds₂ ++ ds₁, as₂ ++ as₁, by simp [hd₂, hd₁, List.append_assoc],
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
  | assert (expr : Formula) : Command Unit
  | checkSat : Command SmtResult

/-! ## Serialization -/

/-- Serialize a command to its SMT-LIB2 string. -/
def Command.query : Command α → String
  | .push => "(push)"
  | .pop => "(pop)"
  | .declareConst n s => s!"(declare-const {n} {s.toSMTLIB})"
  | .assert e => s!"(assert {e.toSMTLIB})"
  | .checkSat => "(check-sat)"

/-- Parse the solver's response string for a given command. Returns `none` on unexpected output. -/
def Command.parseResponse : (cmd : Command α) → String → Option α
  | .push, s => if s == "success" then some () else none
  | .pop, s => if s == "success" then some () else none
  | .declareConst _ _, s => if s == "success" then some () else none
  | .assert _, s => if s == "success" then some () else none
  | .checkSat, s =>
    if s == "sat" then some .sat
    else if s == "unsat" then some .unsat
    else if s == "unknown" then some .unknown
    else none

/-! ## State Operations -/

namespace SmtState

def initial : SmtState := ⟨[⟨[], []⟩]⟩

/-- All declarations visible in the current state (from all frames). -/
def allDecls (s : SmtState) : VarCtx :=
  s.frames.flatMap (·.decls)

/-- All assertions active in the current state (from all frames). -/
def allAsserts (s : SmtState) : List Formula :=
  s.frames.flatMap (·.asserts)

def push (s : SmtState) : SmtState :=
  ⟨⟨[], []⟩ :: s.frames⟩

def pop (s : SmtState) : SmtState :=
  match s.frames with
  | [] => s  -- underflow: no-op
  | _ :: rest => ⟨rest⟩

def addDecl (s : SmtState) (v : Var) : SmtState :=
  match s.frames with
  | [] => ⟨[⟨[v], []⟩]⟩
  | ⟨decls, asserts⟩ :: rest => ⟨⟨v :: decls, asserts⟩ :: rest⟩

def addAssert (s : SmtState) (φ : Formula) : SmtState :=
  match s.frames with
  | [] => ⟨[⟨[], [φ]⟩]⟩
  | ⟨decls, asserts⟩ :: rest => ⟨⟨decls, φ :: asserts⟩ :: rest⟩

/-- Advance the state by one command (only on success). -/
def step : Command β → β → SmtState → SmtState
  | .push, (), s => s.push
  | .pop, (), s => s.pop
  | .declareConst n sort, (), s => s.addDecl ⟨n, sort⟩
  | .assert e, (), s => s.addAssert e
  | .checkSat, _, s => s

end SmtState

/-! ## Satisfiable -/

/-- The conjunction of `asserts` is satisfiable under the given declarations.
    That is, there exists an environment making all assertions true simultaneously. -/
def Satisfiable (_decls : VarCtx) (asserts : List Formula) : Prop :=
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
