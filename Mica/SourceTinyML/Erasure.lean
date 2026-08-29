-- SUMMARY: Elaboration preserves runtime erasure, one theorem per elaboration rule.
import Mica.SourceTinyML.Typing

/-!
# Erasure

Elaboration does not affect the runtime semantics of the program.
`Program.elaborate_runtime` at the end is what the verifier uses to relate a
source program to the runtime program it is verified against.
-/

namespace Typed

open TinyML

namespace Infer


attribute [local simp] Except.instMonad Except.bind Except.map Except.pure

@[local simp] theorem except_pure (a : α) :
    (pure a : Except ε α) = .ok a := rfl
@[local simp] theorem except_map_ok (f : α → β) (a : α) :
    f <$> (Except.ok a : Except ε α) = .ok (f a) := rfl
@[local simp] theorem except_map_error (f : α → β) (e : ε) :
    f <$> (Except.error e : Except ε α) = .error e := rfl
@[local simp] theorem except_bind_ok (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
@[local simp] theorem except_bind_error (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

theorem Binder.close_runtime {st : Infer.State} {b : Binder} {b' : Typed.Binder}
    (h : Binder.close st b = .ok b') : b'.runtime = b.runtime := by
  cases b with
  | mk name ty =>
    cases hc : Infer.State.close st ty <;> simp [Binder.close, hc] at h
    case ok ty' =>
      cases h
      cases name <;> rfl

theorem Binder.closeList_runtime {st : Infer.State} {bs : List Binder}
    {bs' : List Typed.Binder} (h : bs.mapM (Binder.close st) = .ok bs') :
    bs'.map Typed.Binder.WithTypeVars.runtime =
      bs.map Typed.Binder.WithTypeVars.runtime := by
  induction bs generalizing bs' with
  | nil =>
      change Except.ok [] = .ok bs' at h
      cases h
      rfl
  | cons b bs ih =>
      cases hb : Binder.close st b with
      | error e => simp [List.mapM_cons, hb] at h
      | ok b' =>
        cases hrest : bs.mapM (Binder.close st) with
        | error e => simp [List.mapM_cons, hb, hrest] at h
        | ok rest =>
          simp [List.mapM_cons, hb, hrest] at h
          subst bs'
          simp [Binder.close_runtime hb, ih hrest]

mutual


theorem Expr.close_runtime {st : Infer.State} {e : Expr} {e' : Typed.Expr}
    (h : Expr.close st e = .ok e') : e'.runtime = e.runtime := by
  cases e with
  | const c =>
      simpa [Expr.close, Typed.Expr.WithTypeVars.runtime] using
        congrArg Typed.Expr.WithTypeVars.runtime (Except.ok.inj h.symm)
  | var n inst ty =>
      cases hi : inst.mapM (fun p => do pure (p.1, ← Infer.State.close st p.2)) <;> simp at hi
      all_goals cases ht : Infer.State.close st ty <;> simp [Expr.close, hi, ht] at h
      case ok.ok => subst e'; simp [Typed.Expr.WithTypeVars.runtime]
  | prim n inst ty =>
      cases hi : inst.mapM (fun p => do pure (p.1, ← Infer.State.close st p.2)) <;> simp at hi
      all_goals cases ht : Infer.State.close st ty <;> simp [Expr.close, hi, ht] at h
      case ok.ok => subst e'; simp [Typed.Expr.WithTypeVars.runtime]
  | unop op e ty =>
      cases he : Expr.close st e <;> cases ht : Infer.State.close st ty <;>
        simp [Expr.close, he, ht] at h
      case ok.ok e1 t =>
        subst e'; simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime he]
  | binop op l r ty =>
      cases hl : Expr.close st l <;> cases hr : Expr.close st r <;>
        cases ht : Infer.State.close st ty <;> simp [Expr.close, hl, hr, ht] at h
      case ok.ok.ok l' r' t =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime hl, Expr.close_runtime hr]
  | fix self args ret spec body =>
      cases hs : Binder.close st self <;> cases ha : args.mapM (Binder.close st) <;>
        cases hr : Infer.State.close st ret <;>
        cases hspec : TinyML.Typ.substSpecM? (Infer.State.closeVar st) spec <;>
        cases hb : Expr.close st body <;>
        simp [Expr.close, hs, ha, hr, hspec, hb] at h
      case ok.ok.ok.ok.ok self' args' ret' spec' body' =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Binder.close_runtime hs,
          Binder.closeList_runtime ha, Expr.close_runtime hb]
  | app fn args ty =>
      cases hf : Expr.close st fn <;> cases ha : Expr.closeList st args <;>
        cases ht : Infer.State.close st ty <;> simp [Expr.close, hf, ha, ht] at h
      case ok.ok.ok fn' args' t =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime hf,
          Expr.closeList_runtime ha]
  | ifThenElse c t e ty =>
      cases hc : Expr.close st c <;> cases ht : Expr.close st t <;>
        cases he : Expr.close st e <;> cases hty : Infer.State.close st ty <;>
        simp [Expr.close, hc, ht, he, hty] at h
      case ok.ok.ok.ok c' t' e1 ty' =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime hc,
          Expr.close_runtime ht, Expr.close_runtime he]
  | letIn b x body =>
      cases hb : Binder.close st b <;> cases hx : Expr.close st x <;>
        cases hbody : Expr.close st body <;> simp [Expr.close, hb, hx, hbody] at h
      case ok.ok.ok b' x' body' =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Binder.close_runtime hb,
          Expr.close_runtime hx, Expr.close_runtime hbody]
  | letProd bs x body =>
      cases hbs : bs.mapM (Binder.close st) <;> cases hx : Expr.close st x <;>
        cases hbody : Expr.close st body <;> simp [Expr.close, hbs, hx, hbody] at h
      case ok.ok.ok bs' x' body' =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Binder.closeList_runtime hbs,
          Expr.close_runtime hx, Expr.close_runtime hbody]
  | ref o e =>
      cases he : Expr.close st e <;> simp [Expr.close, he] at h
      case ok e1 =>
        subst e'; simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime he]
  | deref e ty =>
      cases he : Expr.close st e <;> cases ht : Infer.State.close st ty <;>
        simp [Expr.close, he, ht] at h
      case ok.ok e1 t =>
        subst e'; simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime he]
  | store l v =>
      cases hl : Expr.close st l <;> cases hv : Expr.close st v <;>
        simp [Expr.close, hl, hv] at h
      case ok.ok l' v' =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime hl, Expr.close_runtime hv]
  | arrayMake o n v =>
      cases hn : Expr.close st n <;> cases hv : Expr.close st v <;>
        simp [Expr.close, hn, hv] at h
      case ok.ok n' v' =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime hn, Expr.close_runtime hv]
  | arrayLen a =>
      cases ha : Expr.close st a <;> simp [Expr.close, ha] at h
      case ok a' =>
        subst e'; simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime ha]
  | arrayGet a i ty =>
      cases ha : Expr.close st a <;> cases hi : Expr.close st i <;>
        cases ht : Infer.State.close st ty <;> simp [Expr.close, ha, hi, ht] at h
      case ok.ok.ok a' i' t =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime ha, Expr.close_runtime hi]
  | arraySet a i v =>
      cases ha : Expr.close st a <;> cases hi : Expr.close st i <;>
        cases hv : Expr.close st v <;> simp [Expr.close, ha, hi, hv] at h
      case ok.ok.ok a' i' v' =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime ha,
          Expr.close_runtime hi, Expr.close_runtime hv]
  | assert e =>
      cases he : Expr.close st e <;> simp [Expr.close, he] at h
      case ok e1 =>
        subst e'; simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime he]
  | tuple es =>
      cases hes : Expr.closeList st es <;> simp [Expr.close, hes] at h
      case ok es' =>
        subst e'; simp [Typed.Expr.WithTypeVars.runtime, Expr.closeList_runtime hes]
  | inj tag arity payload ty =>
      cases hp : Expr.close st payload <;> cases ht : Infer.State.close st ty <;>
        simp [Expr.close, hp, ht] at h
      case ok.ok p' t =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime hp]
  | match_ e branches ty =>
      cases hb : Expr.closeBranches st branches <;> cases he : Expr.close st e <;>
        cases ht : Infer.State.close st ty <;> simp [Expr.close, hb, he, ht] at h
      case ok.ok.ok bs' e1 t =>
        subst e'
        simp [Typed.Expr.WithTypeVars.runtime, Expr.close_runtime he,
          Expr.closeBranches_runtime hb]
termination_by sizeOf e

theorem Expr.closeList_runtime {st : Infer.State} {es : List Expr} {es' : List Typed.Expr}
    (h : Expr.closeList st es = .ok es') :
    es'.map Typed.Expr.WithTypeVars.runtime =
      es.map Typed.Expr.WithTypeVars.runtime := by
  cases es with
  | nil =>
      simp [Expr.closeList] at h
      subst es'; rfl
  | cons e es =>
      cases he : Expr.close st e <;> cases hes : Expr.closeList st es <;>
        simp [Expr.closeList, he, hes] at h
      case ok.ok e' es' =>
        cases h
        simp [Expr.close_runtime he, Expr.closeList_runtime hes]
termination_by sizeOf es

theorem Expr.closeBranches_runtime {st : Infer.State} {bs : List (Binder × Expr)}
    {bs' : List (Typed.Binder × Typed.Expr)} (h : Expr.closeBranches st bs = .ok bs') :
    Typed.Expr.WithTypeVars.branchListRuntime bs' =
      Typed.Expr.WithTypeVars.branchListRuntime bs := by
  cases bs with
  | nil =>
      simp [Expr.closeBranches] at h
      subst bs'; simp [Typed.Expr.WithTypeVars.branchListRuntime]
  | cons head bs =>
      cases head with
      | mk binder body =>
        cases hb : Binder.close st binder <;> cases he : Expr.close st body <;>
          cases hbs : Expr.closeBranches st bs <;> simp [Expr.closeBranches, hb, he, hbs] at h
        case ok.ok.ok binder' body' bs' =>
          cases h
          simp [Typed.Expr.WithTypeVars.branchListRuntime, Binder.close_runtime hb,
            Expr.close_runtime he, Expr.closeBranches_runtime hbs]
termination_by sizeOf bs

end


end Infer

theorem Binder.ofUntyped_runtime (b : Untyped.Binder) (ty : Typ) :
    (Typed.Binder.ofUntyped b ty).runtime = b.runtime := by
  cases b <;> rfl

/-! ## Erasure

Elaboration during inference does not affect the runtime semantics of the program.

Each proof follows the recursion of the function it is about. Phrasing them as
`∀ result, elaborate … = .ok result → …` and unpacking the equality afterwards
would hide the recursive calls from Lean's termination checker, so instead every
proof matches on its syntax argument immediately, recurses only on the pieces
that match exposes, and returns the implication from inside the branch. -/

theorem Infer.Binder.elaborate_runtime (env : SpecEnv σ) (Θ : TypeEnv) (b : Untyped.Binder) :
    ∀ (st st' : Infer.State) (s s' : σ) (b' : Infer.Binder),
      Infer.Binder.elaborate env Θ b st s = .ok ((b', st'), s') → b'.runtime = b.runtime := by
  intro st st' s s' b' h
  cases b with
  | none =>
      simp only [Infer.Binder.elaborate] at h
      have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      rfl
  | named x ann =>
      cases ann <;>
        · simp only [Infer.Binder.elaborate] at h
          have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
          rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          rfl

theorem Infer.Binder.elaborateAt_runtime (env : SpecEnv σ) (Θ : TypeEnv) (b : Untyped.Binder)
    (expected : Infer.Typ) :
    ∀ (st st' : Infer.State) (s s' : σ) (b' : Infer.Binder),
      Infer.Binder.elaborateAt env Θ b expected st s = .ok ((b', st'), s') →
      b'.runtime = b.runtime := by
  intro st st' s s' b' h
  simp only [Infer.Binder.elaborateAt] at h
  have ⟨b₀, t₁, u₁, hb, hcont⟩ := StateT.bind_ok₂ h
  have ⟨_, t₂, u₂, _, hcont⟩ := StateT.bind_ok₂ hcont
  rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
  exact Infer.Binder.elaborate_runtime env Θ b _ _ _ _ _ hb

theorem Infer.Binder.elaborateList_runtime (env : SpecEnv σ) (Θ : TypeEnv) :
    (bs : List Untyped.Binder) → ∀ (st st' : Infer.State) (s s' : σ)
      (bs' : List Infer.Binder),
      Infer.Binder.elaborateList env Θ bs st s = .ok ((bs', st'), s') →
      bs'.map Typed.Binder.WithTypeVars.runtime = bs.map Untyped.Binder.runtime
  | [] => by
      intro st st' s s' bs' h
      rcases (by simpa [Infer.Binder.elaborateList] using h) with ⟨⟨rfl, rfl⟩, rfl⟩
      rfl
  | b :: bs => by
      intro st st' s s' bs' h
      simp only [Infer.Binder.elaborateList] at h
      have ⟨b₀, t₁, u₁, hb, hcont⟩ := StateT.bind_ok₂ h
      have ⟨rest, t₂, u₂, hrest, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Infer.Binder.elaborate_runtime env Θ b _ _ _ _ _ hb,
        Infer.Binder.elaborateList_runtime env Θ bs _ _ _ _ _ hrest]

theorem Infer.Binder.elaborateListAt_runtime (env : SpecEnv σ) (Θ : TypeEnv) :
    (bs : List Untyped.Binder) → ∀ (tys : List Infer.Typ) (st st' : Infer.State) (s s' : σ)
      (bs' : List Infer.Binder),
      Infer.Binder.elaborateListAt env Θ bs tys st s = .ok ((bs', st'), s') →
      bs'.map Typed.Binder.WithTypeVars.runtime = bs.map Untyped.Binder.runtime
  | [] => by
      intro tys st st' s s' bs' h
      cases tys with
      | nil =>
          rcases (by simpa [Infer.Binder.elaborateListAt] using h) with ⟨⟨rfl, rfl⟩, rfl⟩
          rfl
      | cons ty tys => simp [Infer.Binder.elaborateListAt] at h
  | b :: bs => by
      intro tys st st' s s' bs' h
      cases tys with
      | nil => simp [Infer.Binder.elaborateListAt] at h
      | cons ty tys =>
          simp only [Infer.Binder.elaborateListAt] at h
          have ⟨b₀, t₁, u₁, hb, hcont⟩ := StateT.bind_ok₂ h
          have ⟨rest, t₂, u₂, hrest, hcont⟩ := StateT.bind_ok₂ hcont
          rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Infer.Binder.elaborateAt_runtime env Θ b ty _ _ _ _ _ hb,
            Infer.Binder.elaborateListAt_runtime env Θ bs tys _ _ _ _ _ hrest]

theorem Infer.fixSignature_runtime (env : SpecEnv σ) (Θ : TypeEnv)
    (args : List Untyped.Binder) (retTy : Option Infer.Typ) (exp : Infer.Typ) :
    ∀ (st st' : Infer.State) (s s' : σ)
      (r : List Infer.Binder × Infer.Typ × Option (Spec Infer.Typ)),
      Infer.fixSignature env Θ args retTy exp st s = .ok ((r, st'), s') →
      r.1.map Typed.Binder.WithTypeVars.runtime = args.map Untyped.Binder.runtime := by
  intro st st' s s' r h
  unfold Infer.fixSignature at h
  have ⟨sig, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
  obtain ⟨doms, ret, spec⟩ := sig
  have ⟨args', t₂, u₂, hb, hcont⟩ := StateT.bind_ok₂ hcont
  cases retTy <;>
    · have ⟨_, t₃, u₃, _, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      exact Infer.Binder.elaborateListAt_runtime env Θ args _ _ _ _ _ _ hb

mutual

theorem Infer.Expr.elaborate_runtime (env : SpecEnv σ) (Θ : TypeEnv) :
    (e : Untyped.Expr) → ∀ (Γ : Infer.Ctx) (ty : Infer.Typ) (st st' : Infer.State) (s s' : σ)
      (p : Infer.Expr),
      Infer.Expr.elaborate env Θ Γ e ty st s = .ok ((p, st'), s') → p.runtime = e.runtime
  | .const c => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime]
  | .var x => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      cases hΓ : Γ x with
      | none => simp [hΓ] at h
      | some entry =>
          obtain ⟨tparams, tx⟩ := entry
          simp only [hΓ] at h
          have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
          have ⟨_, t₂, u₂, _, hcont⟩ := StateT.bind_ok₂ hcont
          rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime]
  | .prim n => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      cases hp : env.primitive n with
      | none => simp [hp] at h
      | some scheme =>
          simp only [hp] at h
          have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
          have ⟨_, t₂, u₂, _, hcont⟩ := StateT.bind_ok₂ hcont
          rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime]
  | .unop op e => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      cases op with
      | neg | not =>
          have ⟨e', t₁, u₁, he, hcont⟩ := StateT.bind_ok₂ h
          have ⟨_, t₂, u₂, _, hcont⟩ := StateT.bind_ok₂ hcont
          rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
            Infer.Expr.elaborate_runtime env Θ e _ _ _ _ _ _ _ he]
      | proj k =>
          have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
          have ⟨e', t₂, u₂, he, hcont⟩ := StateT.bind_ok₂ hcont
          have ⟨_, t₃, u₃, _, hcont⟩ := StateT.bind_ok₂ hcont
          have ⟨_, t₄, u₄, _, hcont⟩ := StateT.bind_ok₂ hcont
          rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
            Infer.Expr.elaborate_runtime env Θ e _ _ _ _ _ _ _ he]
  | .binop op lhs rhs => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨l', t₁, u₁, hl, hcont⟩ := StateT.bind_ok₂ h
      have ⟨r', t₂, u₂, hr, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₃, u₃, _, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ lhs _ _ _ _ _ _ _ hl,
        Infer.Expr.elaborate_runtime env Θ rhs _ _ _ _ _ _ _ hr]
  | .fix self args retAnn body => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨retTy, t₂, u₂, _, hcont⟩ := StateT.bind_ok₂ h
      have ⟨sig, t₃, u₃, hsig, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨self', t₄, u₄, hself, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨body', t₅, u₅, hbody, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.fixSignature_runtime env Θ args _ _ _ _ _ _ _ hsig,
        Infer.Binder.elaborateAt_runtime env Θ self _ _ _ _ _ _ hself,
        Infer.Expr.elaborate_runtime env Θ body _ _ _ _ _ _ _ hbody]
  | .app fn args => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      have ⟨fn', t₂, u₂, hfn, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₃, u₃, _, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨args', t₄, u₄, hargs, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₅, u₅, _, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ fn _ _ _ _ _ _ _ hfn,
        Infer.Expr.elaborateList_runtime env Θ args _ _ _ _ _ _ _ hargs]
  | .ifThenElse cond thn els => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨c', t₁, u₁, hc, hcont⟩ := StateT.bind_ok₂ h
      have ⟨t', t₂, u₂, ht, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨e', t₃, u₃, he, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ cond _ _ _ _ _ _ _ hc,
        Infer.Expr.elaborate_runtime env Θ thn _ _ _ _ _ _ _ ht,
        Infer.Expr.elaborate_runtime env Θ els _ _ _ _ _ _ _ he]
  | .letIn name bound body => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨name', t₁, u₁, hname, hcont⟩ := StateT.bind_ok₂ h
      have ⟨bound', t₂, u₂, hbound, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨body', t₃, u₃, hbody, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Binder.elaborate_runtime env Θ name _ _ _ _ _ hname,
        Infer.Expr.elaborate_runtime env Θ bound _ _ _ _ _ _ _ hbound,
        Infer.Expr.elaborate_runtime env Θ body _ _ _ _ _ _ _ hbody]
  | .letProd names bound body => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨names', t₁, u₁, hnames, hcont⟩ := StateT.bind_ok₂ h
      have ⟨bound', t₂, u₂, hbound, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨body', t₃, u₃, hbody, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Binder.elaborateList_runtime env Θ names _ _ _ _ _ hnames,
        Infer.Expr.elaborate_runtime env Θ bound _ _ _ _ _ _ _ hbound,
        Infer.Expr.elaborate_runtime env Θ body _ _ _ _ _ _ _ hbody]
  | .ref ownership e => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      have ⟨e', t₂, u₂, he, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₃, u₃, _, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ e _ _ _ _ _ _ _ he]
  | .deref e => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      have ⟨e', t₂, u₂, he, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₃, u₃, _, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₄, u₄, _, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ e _ _ _ _ _ _ _ he]
  | .store loc val => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      have ⟨loc', t₂, u₂, hloc, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₃, u₃, _, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨val', t₄, u₄, hval, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₅, u₅, _, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ loc _ _ _ _ _ _ _ hloc,
        Infer.Expr.elaborate_runtime env Θ val _ _ _ _ _ _ _ hval]
  | .arrayMake ownership len init => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨len', t₁, u₁, hlen, hcont⟩ := StateT.bind_ok₂ h
      have ⟨_, t₂, u₂, _, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨init', t₃, u₃, hinit, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₄, u₄, _, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ len _ _ _ _ _ _ _ hlen,
        Infer.Expr.elaborate_runtime env Θ init _ _ _ _ _ _ _ hinit]
  | .arrayLen arr => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      have ⟨arr', t₂, u₂, harr, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₃, u₃, _, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₄, u₄, _, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ arr _ _ _ _ _ _ _ harr]
  | .arrayGet arr idx => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      have ⟨arr', t₂, u₂, harr, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨idx', t₃, u₃, hidx, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₄, u₄, _, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₅, u₅, _, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ arr _ _ _ _ _ _ _ harr,
        Infer.Expr.elaborate_runtime env Θ idx _ _ _ _ _ _ _ hidx]
  | .arraySet arr idx val => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      have ⟨arr', t₂, u₂, harr, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨idx', t₃, u₃, hidx, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₄, u₄, _, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨val', t₅, u₅, hval, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨_, t₆, u₆, _, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ arr _ _ _ _ _ _ _ harr,
        Infer.Expr.elaborate_runtime env Θ idx _ _ _ _ _ _ _ hidx,
        Infer.Expr.elaborate_runtime env Θ val _ _ _ _ _ _ _ hval]
  | .assert e => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨e', t₁, u₁, he, hcont⟩ := StateT.bind_ok₂ h
      have ⟨_, t₂, u₂, _, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ e _ _ _ _ _ _ _ he]
  | .tuple es => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨resolved, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      split at hcont
      · have ⟨es', t₂, u₂, hes, hcont⟩ := StateT.bind_ok₂ hcont
        rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
        simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
          Infer.Expr.elaborateList_runtime env Θ es _ _ _ _ _ _ _ hes]
      · have ⟨_, t₂, u₂, _, hcont⟩ := StateT.bind_ok₂ hcont
        have ⟨es', t₃, u₃, hes, hcont⟩ := StateT.bind_ok₂ hcont
        have ⟨_, t₄, u₄, _, hcont⟩ := StateT.bind_ok₂ hcont
        rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
        simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
          Infer.Expr.elaborateList_runtime env Θ es _ _ _ _ _ _ _ hes]
  | .inj tag arity payload T => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      have ⟨_, t₂, u₂, _, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨payload', t₃, u₃, hpayload, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ payload _ _ _ _ _ _ _ hpayload]
  | .match_ scrut branches => by
      intro Γ ty st st' s s' p h
      unfold Infer.Expr.elaborate at h
      have ⟨_, t₁, u₁, _, hcont⟩ := StateT.bind_ok₂ h
      have ⟨scrut', t₂, u₂, hscrut, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨r, t₃, u₃, hr, hcont⟩ := StateT.bind_ok₂ hcont
      have ⟨branches', t₄, u₄, hbranches, hcont⟩ := StateT.bind_ok₂ hcont
      rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Typed.Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        Infer.Expr.elaborate_runtime env Θ scrut _ _ _ _ _ _ _ hscrut,
        Infer.Expr.elaborateBranches_runtime env Θ branches _ _ _ _ _ _ _ _ hbranches]

theorem Infer.Expr.elaborateList_runtime (env : SpecEnv σ) (Θ : TypeEnv) :
    (es : List Untyped.Expr) → ∀ (Γ : Infer.Ctx) (tys : List Infer.Typ) (st st' : Infer.State)
      (s s' : σ) (ps : List Infer.Expr),
      Infer.Expr.elaborateList env Θ Γ es tys st s = .ok ((ps, st'), s') →
      ps.map Typed.Expr.WithTypeVars.runtime = es.map Untyped.Expr.runtime
  | [] => by
      intro Γ tys st st' s s' ps h
      cases tys with
      | nil =>
          rcases (by simpa [Infer.Expr.elaborateList] using h) with ⟨⟨rfl, rfl⟩, rfl⟩
          rfl
      | cons ty tys => simp [Infer.Expr.elaborateList] at h
  | e :: es => by
      intro Γ tys st st' s s' ps h
      cases tys with
      | nil => simp [Infer.Expr.elaborateList] at h
      | cons ty tys =>
          unfold Infer.Expr.elaborateList at h
          have ⟨e', t₁, u₁, he, hcont⟩ := StateT.bind_ok₂ h
          have ⟨rest, t₂, u₂, hrest, hcont⟩ := StateT.bind_ok₂ hcont
          rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Infer.Expr.elaborate_runtime env Θ e _ _ _ _ _ _ _ he,
            Infer.Expr.elaborateList_runtime env Θ es _ _ _ _ _ _ _ hrest]

theorem Infer.Expr.elaborateBranches_runtime (env : SpecEnv σ) (Θ : TypeEnv) :
    (bs : List (Untyped.Binder × Untyped.Expr)) → ∀ (Γ : Infer.Ctx) (tys : List Infer.Typ)
      (exp : Infer.Typ) (st st' : Infer.State) (s s' : σ)
      (bs' : List (Infer.Binder × Infer.Expr)),
      Infer.Expr.elaborateBranches env Θ Γ tys bs exp st s = .ok ((bs', st'), s') →
      Typed.Expr.WithTypeVars.branchListRuntime bs' =
        Untyped.Expr.runtime.branchListRuntime bs
  | [] => by
      intro Γ tys exp st st' s s' bs' h
      cases tys with
      | nil =>
          rcases (by simpa [Infer.Expr.elaborateBranches] using h) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Typed.Expr.WithTypeVars.branchListRuntime,
            Untyped.Expr.runtime.branchListRuntime]
      | cons ty tys => simp [Infer.Expr.elaborateBranches] at h
  | (b, body) :: bs => by
      intro Γ tys exp st st' s s' bs' h
      cases tys with
      | nil => simp [Infer.Expr.elaborateBranches] at h
      | cons ty tys =>
          unfold Infer.Expr.elaborateBranches at h
          have ⟨b', t₁, u₁, hb, hcont⟩ := StateT.bind_ok₂ h
          have ⟨body', t₂, u₂, hbody, hcont⟩ := StateT.bind_ok₂ hcont
          have ⟨rest, t₃, u₃, hrest, hcont⟩ := StateT.bind_ok₂ hcont
          rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Typed.Expr.WithTypeVars.branchListRuntime,
            Untyped.Expr.runtime.branchListRuntime,
            Infer.Binder.elaborateAt_runtime env Θ b _ _ _ _ _ _ hb,
            Infer.Expr.elaborate_runtime env Θ body _ _ _ _ _ _ _ hbody,
            Infer.Expr.elaborateBranches_runtime env Θ bs _ _ _ _ _ _ _ _ hrest]

end

theorem Expr.elaborate_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TyCtx)
    (e : Untyped.Expr) (expected : Option Typ) :
    ∀ {s s' : σ} {e' : Typed.Expr},
      Expr.elaborate env Θ Γ e expected s = .ok (e', s') → e'.runtime = e.runtime := by
  intro s s' e' h
  unfold Expr.elaborate at h
  obtain ⟨ty, st, st', pending, helab, hclose⟩ := Infer.run_ok h
  exact (Infer.Expr.close_runtime hclose).trans
    (Infer.Expr.elaborate_runtime env Θ e (Infer.Ctx.ofTyCtx Γ) _ _ _ _ _ _ helab)

theorem ValDecl.elaborateSpecified_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (self : Option TinyML.Var) (rb : Untyped.SpecBody) (e : Untyped.Expr) :
    ∀ {s : σ} {r : Spec Typ × Typed.Expr} {s' : σ},
      Typed.ValDecl.elaborateSpecified env Θ Γ self rb e s = .ok (r, s') →
      r.2.runtime = e.runtime := by
  intro s r s' h
  cases e
  case fix self args retTy body =>
    cases retTy with
    | none => simp [ValDecl.elaborateSpecified, TypeM.error] at h
    | some retAnn =>
      simp only [ValDecl.elaborateSpecified] at h
      split at h
      · simp [TypeM.error] at h
      · -- The signature and the spec's own elaboration stay opaque:
        -- `StateT.bind_ok` recovers them without naming their values.
        have ⟨_retTy, s₀, _hret, hcont⟩ := StateT.bind_ok h
        have ⟨_typedArgs, s₁, _hargs, hcont⟩ := StateT.bind_ok hcont
        have ⟨_spec, s₂, _hspec, hcont⟩ := StateT.bind_ok hcont
        have ⟨body', s₃, hbody, hcont⟩ := StateT.bind_ok hcont
        rcases hcont with ⟨rfl, rfl⟩
        exact Expr.elaborate_runtime env Θ Γ _ _ hbody
  all_goals simp [ValDecl.elaborateSpecified, TypeM.error] at h

theorem ValDecl.elaborate_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (d : Untyped.ValDecl Untyped.SpecBody) :
    ∀ {s : σ} {d' : Typed.ValDecl} {s' : σ},
      Typed.ValDecl.elaborate env Θ Γ d s = .ok (d', s') →
      d'.runtime = d.runtime := by
  intro s d' s' helab
  -- Split on whether there is a specification, and then — in its absence — only
  -- on whether there is an annotation; the unannotated cases are identical.
  match hspec : d.spec with
  | some rb =>
    simp only [ValDecl.elaborate, hspec] at helab
    have ⟨_, sg, _, helab'⟩ := StateT.bind_ok helab
    have ⟨r, s₀, hfix, hcont⟩ := StateT.bind_ok helab'
    have ⟨_, s₁, _, hcont⟩ := StateT.bind_ok hcont
    rcases hcont with ⟨rfl, rfl⟩
    simp [Typed.ValDecl.runtime, Untyped.ValDecl.runtime, Binder.ofUntyped_runtime,
      ValDecl.elaborateSpecified_runtime env Θ Γ _ rb d.body hfix]
  | none =>
    simp only [ValDecl.elaborate, hspec] at helab
    have ⟨_expected, s₀, _hexp, hcont⟩ := StateT.bind_ok helab
    have ⟨body', s₁, hbody, hcont⟩ := StateT.bind_ok hcont
    rcases hcont with ⟨rfl, rfl⟩
    simp [Typed.ValDecl.runtime, Untyped.ValDecl.runtime, Binder.ofUntyped_runtime,
      Expr.elaborate_runtime env Θ Γ d.body _ hbody]

theorem Program.elaborate_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (prog : Untyped.Program Untyped.SpecBody) :
    ∀ {s : σ} {Θ' : TypeEnv} {prog' : Typed.Program} {s' : σ},
      Typed.Program.elaborate env Θ Γ prog s = .ok ((Θ', prog'), s') →
      prog'.runtime = prog.runtime := by
  induction prog generalizing Θ Γ with
  | nil =>
    intro s Θ' prog' s' h
    simp [Typed.Program.elaborate] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    simp [Typed.Program.runtime, Untyped.Program.runtime]
  | cons d ds ih =>
    intro s Θ' prog' s' h
    cases d with
    | type_ dty =>
      unfold Typed.Program.elaborate at h
      -- The payloads' own elaboration stays opaque; a type declaration
      -- contributes nothing to the runtime program either way.
      have ⟨body, s₀, _hbody, hcont⟩ := StateT.bind_ok h
      cases hext : extendTypeEnv Θ dty.name body with
      | error err =>
        simp [hext] at hcont
      | ok Θ1 =>
        simp [hext] at hcont
        exact ih Θ1 Γ hcont
    | val_ dval =>
      unfold Typed.Program.elaborate at h
      have ⟨dval', s₀, hdecl, hcont⟩ := StateT.bind_ok h
      have ⟨_, s₀', _, hcont⟩ := StateT.bind_ok hcont
      let Γ' := match dval'.name.name with
        | some x => Γ.extendScheme x (Scheme.gen dval'.name.ty)
        | none => Γ
      have ⟨tail, s₁, htail, hcont⟩ := StateT.bind_ok hcont
      rcases tail with ⟨Θ'', ds'⟩
      simp at hcont
      rcases hcont with ⟨⟨rfl, rfl⟩, rfl⟩
      have hdecl_rt : dval'.runtime = dval.runtime :=
        ValDecl.elaborate_runtime _ Θ Γ dval hdecl
      simp [Typed.Program.runtime, Untyped.Program.runtime, hdecl_rt]
      exact congrArg (List.cons dval.runtime) (ih Θ Γ' htail)

end Typed
