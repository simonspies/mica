-- SUMMARY: Abstract SMT states and the satisfiability notion used in the solver interface.
import Mica.FOL.Formulas

/-! ## Frame and State

The solver state: a stack of frames, each recording declarations and assertions.
The commands (push) and (pop) are used to add a new frame or remove it from the
state. -/

namespace Smt

structure Frame where
  decls : Signature
  asserts : List Formula

def Frame.empty : Frame := ⟨Signature.empty, []⟩

structure State where
  frames : List Frame

/-! ## Frame.Extends -/

/-- `f.Extends f'` means `f'` was reached from `f` by adding declarations and
    assertions: every component of `f` is a suffix of the matching one in `f'`. -/
def Frame.Extends (f f' : Frame) : Prop :=
  f.decls.vars <:+ f'.decls.vars ∧
  f.decls.consts <:+ f'.decls.consts ∧
  f.decls.unary <:+ f'.decls.unary ∧
  f.decls.binary <:+ f'.decls.binary ∧
  f.decls.ternary <:+ f'.decls.ternary ∧
  f.decls.unaryRel <:+ f'.decls.unaryRel ∧
  f.decls.binaryRel <:+ f'.decls.binaryRel ∧
  f.asserts <:+ f'.asserts

theorem Frame.Extends.refl (f : Frame) : f.Extends f :=
  ⟨List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _,
   List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _⟩

theorem Frame.Extends.addConst (f : Frame) (c : FOL.Const) :
    f.Extends ⟨f.decls.addConst c, f.asserts⟩ :=
  ⟨List.suffix_refl _, List.suffix_cons _ _, List.suffix_refl _, List.suffix_refl _,
   List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _⟩

theorem Frame.Extends.addUnary (f : Frame) (u : FOL.Unary) :
    f.Extends ⟨f.decls.addUnary u, f.asserts⟩ :=
  ⟨List.suffix_refl _, List.suffix_refl _, List.suffix_cons _ _, List.suffix_refl _,
   List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _⟩

theorem Frame.Extends.addBinary (f : Frame) (b : FOL.Binary) :
    f.Extends ⟨f.decls.addBinary b, f.asserts⟩ :=
  ⟨List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_cons _ _,
   List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _⟩

theorem Frame.Extends.addTernary (f : Frame) (t : FOL.Ternary) :
    f.Extends ⟨f.decls.addTernary t, f.asserts⟩ :=
  ⟨List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _,
   List.suffix_cons _ _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _⟩

theorem Frame.Extends.addUnaryRel (f : Frame) (u : FOL.UnaryRel) :
    f.Extends ⟨f.decls.addUnaryRel u, f.asserts⟩ :=
  ⟨List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _,
   List.suffix_refl _, List.suffix_cons _ _, List.suffix_refl _, List.suffix_refl _⟩

theorem Frame.Extends.addBinaryRel (f : Frame) (b : FOL.BinaryRel) :
    f.Extends ⟨f.decls.addBinaryRel b, f.asserts⟩ :=
  ⟨List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _,
   List.suffix_refl _, List.suffix_refl _, List.suffix_cons _ _, List.suffix_refl _⟩

theorem Frame.Extends.addAssert (f : Frame) (φ : Formula) :
    f.Extends ⟨f.decls, φ :: f.asserts⟩ :=
  ⟨List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _,
   List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_cons _ _⟩

theorem Frame.Extends.trans {f₁ f₂ f₃ : Frame}
    (h₁₂ : f₁.Extends f₂) (h₂₃ : f₂.Extends f₃) : f₁.Extends f₃ :=
  ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.1.trans h₂₃.2.1, h₁₂.2.2.1.trans h₂₃.2.2.1,
   h₁₂.2.2.2.1.trans h₂₃.2.2.2.1, h₁₂.2.2.2.2.1.trans h₂₃.2.2.2.2.1,
   h₁₂.2.2.2.2.2.1.trans h₂₃.2.2.2.2.2.1, h₁₂.2.2.2.2.2.2.1.trans h₂₃.2.2.2.2.2.2.1,
   h₁₂.2.2.2.2.2.2.2.trans h₂₃.2.2.2.2.2.2.2⟩

/-! ## Result -/

inductive Result where
  | sat
  | unsat
  | unknown

/-! ## State operations -/

namespace State

def initial : State := ⟨[Frame.empty]⟩

/-- All declarations visible in the current state. -/
def allDecls (s : State) : Signature :=
  ⟨s.frames.flatMap (·.decls.vars),
   s.frames.flatMap (·.decls.consts),
   s.frames.flatMap (·.decls.unary),
   s.frames.flatMap (·.decls.binary),
   s.frames.flatMap (·.decls.ternary),
   s.frames.flatMap (·.decls.unaryRel),
   s.frames.flatMap (·.decls.binaryRel)⟩

def allAsserts (s : State) : List Formula :=
  s.frames.flatMap (·.asserts)

def push (s : State) : State :=
  ⟨Frame.empty :: s.frames⟩

/-- Remove the top frame. `State.initial` has one frame, so the empty stack is
    reachable only through a `pop` with no matching `push`; that case is a no-op. -/
def pop (s : State) : State :=
  match s.frames with
  | [] => s
  | _ :: rest => ⟨rest⟩

/-- Apply `f` to the top frame. `State.initial` has one frame, so the empty stack
    is reachable only through a `pop` with no matching `push`; that case starts a
    fresh frame. -/
def modifyTop (s : State) (f : Frame → Frame) : State :=
  match s.frames with
  | [] => ⟨[f Frame.empty]⟩
  | fr :: rest => ⟨f fr :: rest⟩

def modifyDecls (s : State) (f : Signature → Signature) : State :=
  s.modifyTop (fun fr => ⟨f fr.decls, fr.asserts⟩)

def addConst (s : State) (c : FOL.Const) : State :=
  s.modifyDecls (·.addConst c)

def addUnary (s : State) (u : FOL.Unary) : State :=
  s.modifyDecls (·.addUnary u)

def addBinary (s : State) (b : FOL.Binary) : State :=
  s.modifyDecls (·.addBinary b)

def addTernary (s : State) (t : FOL.Ternary) : State :=
  s.modifyDecls (·.addTernary t)

def addUnaryRel (s : State) (u : FOL.UnaryRel) : State :=
  s.modifyDecls (·.addUnaryRel u)

def addBinaryRel (s : State) (b : FOL.BinaryRel) : State :=
  s.modifyDecls (·.addBinaryRel b)

def addAssert (s : State) (φ : Formula) : State :=
  s.modifyTop (fun fr => ⟨fr.decls, φ :: fr.asserts⟩)

end State

/-! ## State.satisfiable -/

/-- The assertions have a satisfying assignment over the declarations `decls`: an
    environment that makes every formula in `asserts` true. -/
def State.satisfiable (decls : Signature) (asserts : List Formula) : Prop :=
  -- Environments are total, so the declarations do not restrict the assignment.
  -- They would, if assignments were partial.
  let _ := decls
  ∃ ρ : Env, ∀ φ ∈ asserts, φ.eval ρ

/-- From the unsatisfiability of `φ :: asserts`: every environment satisfying
    `asserts` refutes `φ`. -/
theorem State.satisfiable.eval_of_unsat_cons {φ : Formula}
    (decls : Signature) (asserts : List Formula) :
  ¬ State.satisfiable decls (φ :: asserts) →
  ∀ ρ, (∀ ψ ∈ asserts, ψ.eval ρ) → (Formula.not φ).eval ρ :=
  by
    unfold State.satisfiable
    intro hsat ρ hasserts hev
    apply hsat
    exists ρ
    intro ψ hψ
    cases hψ with
    | head => exact hev
    | tail _ hψ => exact hasserts _ hψ

/-- From the unsatisfiability of `¬ φ :: asserts`: every environment satisfying
    `asserts` satisfies `φ`. -/
theorem State.satisfiable.eval_of_unsat_not_cons {φ : Formula}
    (decls : Signature) (asserts : List Formula) :
  ¬ State.satisfiable decls (Formula.not φ :: asserts) →
  ∀ ρ, (∀ ψ ∈ asserts, ψ.eval ρ) → φ.eval ρ := by
  intro hsat ρ hasserts
  obtain h := (State.satisfiable.eval_of_unsat_cons decls asserts hsat ρ hasserts)
  simp only [Formula.eval] at h
  simp at h
  trivial

end Smt
