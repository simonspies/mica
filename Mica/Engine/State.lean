-- SUMMARY: Abstract SMT states and the satisfiability notion used in the solver interface.
import Mica.FOL.Printing
import Mica.FOL.Subst

/-! ## Smt.Frame and Smt.State

The solver state: a stack of frames, each recording declarations and assertions.
The commands (push) and (pop) are used to add a new frame or remove it from the
state. -/

namespace Smt

structure Frame where
  decls : Signature
  asserts : List Formula

structure State where
  frames : List Frame

/-! ## Frame Extension -/

def Frame.Extends (f f' : Frame) : Prop :=
  ∃ vs cs us bs as,
    f'.decls.vars   = vs ++ f.decls.vars ∧
    f'.decls.consts = cs ++ f.decls.consts ∧
    f'.decls.unary  = us ++ f.decls.unary ∧
    f'.decls.binary = bs ++ f.decls.binary ∧
    f'.asserts = as ++ f.asserts

theorem Frame.Extends.refl (f : Frame) : f.Extends f :=
  ⟨[], [], [], [], [], rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.Extends.addConst (f : Frame) (c : FOL.Const) :
    f.Extends ⟨f.decls.addConst c, f.asserts⟩ :=
  ⟨[], [c], [], [], [], rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.Extends.addUnary (f : Frame) (u : FOL.Unary) :
    f.Extends ⟨f.decls.addUnary u, f.asserts⟩ :=
  ⟨[], [], [u], [], [], rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.Extends.addBinary (f : Frame) (b : FOL.Binary) :
    f.Extends ⟨f.decls.addBinary b, f.asserts⟩ :=
  ⟨[], [], [], [b], [], rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.Extends.addAssert (f : Frame) (φ : Formula) :
    f.Extends ⟨f.decls, φ :: f.asserts⟩ :=
  ⟨[], [], [], [], [φ], rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.Extends.trans {f₁ f₂ f₃ : Frame}
    (h₁₂ : f₁.Extends f₂) (h₂₃ : f₂.Extends f₃) : f₁.Extends f₃ := by
  obtain ⟨vs₁, cs₁, us₁, bs₁, as₁, hv₁, hc₁, hu₁, hb₁, ha₁⟩ := h₁₂
  obtain ⟨vs₂, cs₂, us₂, bs₂, as₂, hv₂, hc₂, hu₂, hb₂, ha₂⟩ := h₂₃
  exact ⟨vs₂ ++ vs₁, cs₂ ++ cs₁, us₂ ++ us₁, bs₂ ++ bs₁, as₂ ++ as₁,
    by simp [hv₂, hv₁, List.append_assoc],
    by simp [hc₂, hc₁, List.append_assoc],
    by simp [hu₂, hu₁, List.append_assoc],
    by simp [hb₂, hb₁, List.append_assoc],
    by simp [ha₂, ha₁, List.append_assoc]⟩

/-! ## Smt.Result -/

inductive Result where
  | sat
  | unsat
  | unknown
  deriving BEq, Repr

/-! ## Smt.State operations -/

namespace State

def initial : State := ⟨[⟨Signature.empty, []⟩]⟩

/-- All declarations visible in the current state. -/
def allDecls (s : State) : Signature :=
  ⟨s.frames.flatMap (·.decls.vars),
   s.frames.flatMap (·.decls.consts),
   s.frames.flatMap (·.decls.unary),
   s.frames.flatMap (·.decls.binary)⟩

/-- All assertions active in the current state. -/
def allAsserts (s : State) : List Formula :=
  s.frames.flatMap (·.asserts)

def push (s : State) : State :=
  ⟨⟨Signature.empty, []⟩ :: s.frames⟩

def pop (s : State) : State :=
  match s.frames with
  | [] => s  -- underflow: no-op
  | _ :: rest => ⟨rest⟩

def modifyDecls (s : State) (f : Signature → Signature) : State :=
  match s.frames with
  | [] => ⟨[⟨f Signature.empty, []⟩]⟩
  | ⟨decls, asserts⟩ :: rest => ⟨⟨f decls, asserts⟩ :: rest⟩

def addConst (s : State) (c : FOL.Const) : State :=
  s.modifyDecls (·.addConst c)

def addUnary (s : State) (u : FOL.Unary) : State :=
  s.modifyDecls (·.addUnary u)

def addBinary (s : State) (b : FOL.Binary) : State :=
  s.modifyDecls (·.addBinary b)

def addAssert (s : State) (φ : Formula) : State :=
  match s.frames with
  | [] => ⟨[⟨Signature.empty, [φ]⟩]⟩
  | ⟨decls, asserts⟩ :: rest => ⟨⟨decls, φ :: asserts⟩ :: rest⟩

end State

/-! ## Smt.State.satisfiable -/

/-- The conjunction of `asserts` is satisfiable under the given declarations.
    That is, there exists an environment making all assertions true simultaneously. -/
def State.satisfiable (_decls : Signature) (asserts : List Formula) : Prop :=
  ∃ ρ : Env, ∀ φ ∈ asserts, φ.eval ρ

theorem State.satisfiable.to_impl decls asserts :
  ¬ State.satisfiable decls (φ :: asserts) →
  ∀ ρ, (∀ ψ ∈ asserts, ψ.eval ρ) → (Formula.not φ).eval ρ :=
  by
    unfold State.satisfiable
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

theorem State.satisfiable.to_impl' decls asserts :
  ¬ State.satisfiable decls (Formula.not φ :: asserts) →
  ∀ ρ, (∀ ψ ∈ asserts, ψ.eval ρ) → φ.eval ρ := by
  intro hsat ρ hasserts
  obtain h := (State.satisfiable.to_impl decls asserts hsat ρ hasserts)
  simp only [Formula.eval] at h
  simp at h
  trivial

end Smt
