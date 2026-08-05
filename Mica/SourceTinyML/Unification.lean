-- SUMMARY: Unification variables, the state that solves them, the IR they annotate, and the monad elaboration runs in.
import Mica.SourceTinyML.Types
import Mica.SourceTinyML.Typed
import Mica.SourceTinyML.Printer
import Mica.Base.Except

/-!
# Unification

Elaboration checks an expression against the type expected of it, so every rule
ends in an equation between two types. Collected here is the unification
machinery that records those equations and solves them: the variables a type may
mention while inference runs, the state mapping them to solutions, the typed IR
at those types, and the monad threading the state.
-/

namespace Typed

open TinyML

namespace Infer

/-! ## Inference types

Inference reuses the type syntax at a third instantiation of
`TinyML.Typ.WithTypeVars`, one whose variables are either rigid — coming from a source
annotation, and standing for a type the inferred program may not choose — or
flexible metavariables the unifier owns. A metavariable never reaches the typed
IR: it is solved, or rejected at an elaboration boundary. -/

abbrev MetaVar := Nat

/-- An inference variable. A rigid one is a variable the enclosing declaration
binds — it stands for a type the declaration's *caller* chooses, so the body may
not choose it. A flexible one is the unifier's own. Which of the two a source
`'a` becomes is decided by `Typ.ofSource` from the declaration's signature. -/
inductive Var where
  | rigid (v : TyVar)
  | flex (v : MetaVar)
  deriving Repr, DecidableEq

def Var.print : Var → String
  | .rigid v => s!"'{v}"
  | .flex v => s!"?{v}"

abbrev Typ := TinyML.Typ.WithTypeVars Var

def Typ.print : Typ → String := TinyML.Typ.printWith Var.print

/-- Embed a verifier-facing type into the inference language. Its variables are
the ones the enclosing declaration quantifies over, so they embed as rigid: no
solution the body finds may choose them. -/
def Typ.ofTyp : TinyML.Typ → Typ := TinyML.Typ.subst (fun v => .tvar (.rigid v))

end Infer

/-! ## Type errors -/

inductive TypeError where
  | undefinedVar (name : TinyML.Var)
  | duplicateType (name : TypeName)
  | arityMismatch (expected actual : Nat)
  | typeMismatch (expected actual : Typ)
  | spec (msg : String)
  | unknownPrimitive (name : String)
  /-- A type variable written where nothing binds it: a data declaration's
  payload may name only that declaration's own parameters. -/
  | unboundTypeVar (name : TyVar)
  /-- Two types the program requires to be equal are not. -/
  | mismatch (left right : Infer.Typ)
  /-- Solving a metavariable would make its solution mention it. -/
  | occurs (var : Infer.MetaVar) (inType : Infer.Typ)
  /-- A type the expression leaves undetermined. -/
  | unresolved (var : Infer.MetaVar)
  /-- An expression's syntax demands a shape its type does not have. -/
  | notA (shape : String) (ty : Infer.Typ)
  deriving Repr, Inhabited

instance : ToString TypeError where
  toString
    | .undefinedVar name => s!"undefined variable: {name}"
    | .duplicateType name => s!"duplicate type: {name}"
    | .arityMismatch expected actual =>
        s!"arity mismatch: expected {expected}, got {actual}"
    | .typeMismatch expected actual =>
        s!"type mismatch: expected {expected.print}, got {actual.print}"
    | .spec msg => s!"specification error: {msg}"
    | .unknownPrimitive name => s!"unknown primitive: {name}"
    | .unboundTypeVar name => s!"unbound type variable '{name}"
    | .mismatch a b => s!"cannot unify {a.print} with {b.print}"
    | .occurs v t => s!"?{v} occurs in {t.print}"
    | .unresolved v => s!"unresolved type metavariable ?{v}"
    | .notA shape ty => s!"not {shape}: {ty.print}"

/-! ## The typing monad

Typing has exactly one effect of its own — failure. The state is there only to
carry whatever effect the ambient environment's callbacks need, and typing never
reads or writes it: it merely threads it through. -/

abbrev TypeM (σ : Type) := StateT σ (Except TypeError)

/-- Fail with a type error, discarding the state. -/
def TypeM.error (e : TypeError) : TypeM σ α := fun _ => .error e

@[simp] theorem TypeM.error_apply (e : TypeError) (s : σ) :
    (TypeM.error e : TypeM σ α) s = .error e := rfl

@[simp] theorem TypeM.pure_apply (a : α) (s : σ) :
    (pure a : TypeM σ α) s = .ok (a, s) := rfl

@[simp] theorem TypeM.error_bind (e : TypeError) (g : α → TypeM σ β) :
    (TypeM.error e >>= g : TypeM σ β) = TypeM.error e := by
  funext s; rfl

/-- Run a pure `Except` computation in `TypeM`, leaving the state untouched. -/
def TypeM.ofExcept : Except TypeError α → TypeM σ α
  | .ok a => fun s => .ok (a, s)
  | .error e => fun _ => .error e

@[simp] theorem TypeM.ofExcept_pure (a : α) :
    (TypeM.ofExcept (.ok a) : TypeM σ α) = pure a := rfl

@[simp] theorem TypeM.ofExcept_error (e : TypeError) :
    (TypeM.ofExcept (.error e) : TypeM σ α) = TypeM.error e := rfl

@[simp] theorem TypeM.ofExcept_ok {r : Except TypeError α} {s s' : σ} {a : α} :
    (TypeM.ofExcept r : TypeM σ α) s = .ok (a, s') ↔ r = .ok a ∧ s' = s := by
  cases r <;> simp [TypeM.ofExcept, eq_comm]

namespace Infer

/-! ## Unification state -/

/-- The mutable part of inference: the next unused metavariable, and the
solutions found so far.

The substitution is idempotent — `bind` applies a new solution to the ones
already stored, so every type in `subst` mentions only variables that are still
unsolved. That is what lets `resolve` be a single lookup, and `occurs` and
`close` be one pass of the ordinary substitution. -/
structure State where
  next : MetaVar := 0
  subst : List (MetaVar × Typ) := []
  deriving Repr, Inhabited

namespace State

/-- Allocate one fresh flexible metavariable. -/
def fresh (st : State) : Typ × State :=
  (.tvar (.flex st.next), { st with next := st.next + 1 })

/-- The solution of a metavariable, if it has one. -/
def lookup (st : State) (v : MetaVar) : Option Typ :=
  (st.subst.find? fun p => p.1 = v).map Prod.snd

/-- Replace every solved variable in a type by its solution. One pass suffices,
because the solutions are themselves solved. -/
def apply (st : State) : Typ → Typ :=
  TinyML.Typ.subst fun v => match v with
    | .flex w => (st.lookup w).getD (.tvar v)
    | .rigid _ => .tvar v

/-- Solve an unsolved metavariable, keeping the substitution idempotent.
`unify` runs the occurs check before calling this. -/
def bind (st : State) (v : MetaVar) (t : Typ) : State :=
  let sol := st.apply t
  let elim : Typ → Typ := TinyML.Typ.subst fun w => if w = .flex v then sol else .tvar w
  { st with subst := (v, sol) :: st.subst.map fun p => (p.1, elim p.2) }

/-- Follow a solved metavariable to the type it stands for. -/
def resolve (st : State) : Typ → Typ
  | t@(.tvar (.flex v)) => (st.lookup v).getD t
  | t => t

/-- Whether a metavariable occurs in a type once that type is solved. -/
def occurs (st : State) (needle : MetaVar) (t : Typ) : Bool :=
  (TinyML.Typ.vars (st.apply t)).any (· == .flex needle)

private def mismatch (a b : Typ) : Except TypeError State := .error (.mismatch a b)

mutual

partial def unifyList (st : State) (Θ : TypeEnv) :
    List Typ → List Typ → Except TypeError State
  | [], [] => .ok st
  | a :: as, b :: bs => do unifyList (← unify st Θ a b) Θ as bs
  | as, bs => .error (.arityMismatch as.length bs.length)

/-- Unify two types by equality.

A name is opaque except against a sum, which is the one structural type it can
equal — the sum of the payloads its declaration gives it. Unfolding there is a
definitional equality. -/
partial def unify (st : State) (Θ : TypeEnv) (a b : Typ) :
    Except TypeError State :=
  let a := st.resolve a
  let b := st.resolve b
  match a, b with
    | .tvar (.flex v), .tvar (.flex w) =>
        if v = w then .ok st else .ok (st.bind v (.tvar (.flex w)))
    | .tvar (.flex v), t | t, .tvar (.flex v) =>
        if st.occurs v t then .error (.occurs v t) else .ok (st.bind v t)
    | .prim p, .prim q => if p = q then .ok st else mismatch a b
    | .empty, .empty | .value, .value => .ok st
    | .tvar (.rigid v), .tvar (.rigid w) => if v = w then .ok st else mismatch a b
    | .sum as, .sum bs | .tuple as, .tuple bs => unifyList st Θ as bs
    | .arrow as ar spec, .arrow bs br spec' =>
        if spec = spec' then do unify (← unifyList st Θ as bs) Θ ar br
        else mismatch a b
    | .ref x, .ref y | .array x, .array y | .ownedArray x, .ownedArray y
    | .vec x, .vec y | .owned x, .owned y => unify st Θ x y
    | .named n as, .named m bs => if n = m then unifyList st Θ as bs else mismatch a b
    | .named n as, .sum _ => match TypeName.unfold Θ n as with
        | some a' => unify st Θ a' b
        | none => mismatch a b
    | .sum _, .named m bs => match TypeName.unfold Θ m bs with
        | some b' => unify st Θ a b'
        | none => mismatch a b
    | _, _ => mismatch a b

end

/-! ### Closing an inference type

Closing is the boundary operation: it replaces every solved metavariable by its
solution and rejects every metavariable still open, so no inference-only type
can reach the typed IR. A rigid variable is not inference-only — it is the
declaration's own type variable, and it closes to itself. -/

/-- Reject a metavariable that survived solving. -/
private def rejectUnsolved : Var → Except TypeError TinyML.Typ
  | .rigid v => .ok (.tvar v)
  | .flex v => .error (.unresolved v)

/-- Close one inference variable: its solution mentions only unsolved
variables, so closing it either succeeds outright or names what is open. -/
def closeVar (st : State) : Var → Except TypeError TinyML.Typ
  | .rigid v => .ok (.tvar v)
  | .flex v =>
      match st.lookup v with
      | none => .error (.unresolved v)
      | some t => TinyML.Typ.substM rejectUnsolved t

/-- Close an inference type into the verifier-facing `TinyML.Typ`. -/
def close (st : State) (t : Typ) : Except TypeError TinyML.Typ :=
  TinyML.Typ.substM (closeVar st) t

/-- One fresh metavariable per name. -/
private def freshVars : List TyVar → State → List (TyVar × Typ) × State
  | [], st => ([], st)
  | v :: vs, st =>
      let (m, st) := st.fresh
      let (rest, st) := freshVars vs st
      ((v, m) :: rest, st)

/-- Instantiate a type at fresh metavariables for the given variables,
returning the assignment alongside so a use site can record what it chose.
Rigid variables outside `tparams` are left alone: they belong to the
declaration being elaborated, not to the scheme being used. -/
def instantiateAt (tparams : List TyVar) (ty : Typ) (st : State) :
    Typ × List (TyVar × Typ) × State :=
  let (vars, st) := freshVars tparams st
  let σ : Var → Typ
    | .rigid a => (vars.lookup a).getD (.tvar (.rigid a))
    | .flex m => .tvar (.flex m)
  (TinyML.Typ.subst σ ty, vars, st)

/-- Instantiate a schema at fresh metavariables. A schema quantifies every
variable it mentions, which is what a primitive's registry entry is. -/
def instantiate (s : SchemaTyp) (st : State) :
    Typ × List (TyVar × Typ) × State :=
  instantiateAt (TinyML.Typ.vars s).eraseDups (Typ.ofTyp s) st

end State

/-! ## Expressions under inference

The typed syntax at inference types. An elaboration boundary maps it to the
ordinary typed IR in one step, or fails on what it left open. -/


abbrev Binder := Typed.Binder.WithTypeVars Var
abbrev Expr := Typed.Expr.WithTypeVars Var

def Binder.close (st : State) (b : Binder) : Except TypeError Typed.Binder :=
  match State.close st b.ty with
  | .ok ty => .ok { name := b.name, ty }
  | .error e => .error e

mutual

/-- Close a pending expression, rejecting any type it has left open. -/
def Expr.close (st : State) : Expr → Except TypeError Typed.Expr
  | .const c => pure (.const c)
  | .var n inst ty => do
      let inst ← inst.mapM fun p => do pure (p.1, ← State.close st p.2)
      pure (.var n inst (← State.close st ty))
  | .prim n inst ty => do
      let inst ← inst.mapM fun p => do pure (p.1, ← State.close st p.2)
      pure (.prim n inst (← State.close st ty))
  | .unop op e ty => do
      pure (.unop op (← Expr.close st e) (← State.close st ty))
  | .binop op l r ty => do
      pure (.binop op (← Expr.close st l) (← Expr.close st r) (← State.close st ty))
  | .fix self args ret spec body => do
      pure (.fix (← Binder.close st self) (← args.mapM (Binder.close st))
        (← State.close st ret)
        (← TinyML.Typ.substSpecM? (State.closeVar st) spec)
        (← Expr.close st body))
  | .app fn args ty => do
      pure (.app (← Expr.close st fn) (← Expr.closeList st args) (← State.close st ty))
  | .ifThenElse c t e ty => do
      pure (.ifThenElse (← Expr.close st c) (← Expr.close st t) (← Expr.close st e)
        (← State.close st ty))
  | .letIn b x body => do
      pure (.letIn (← Binder.close st b) (← Expr.close st x) (← Expr.close st body))
  | .letProd bs x body => do
      pure (.letProd (← bs.mapM (Binder.close st)) (← Expr.close st x) (← Expr.close st body))
  | .ref o e => do pure (.ref o (← Expr.close st e))
  | .deref e ty => do pure (.deref (← Expr.close st e) (← State.close st ty))
  | .store l v => do pure (.store (← Expr.close st l) (← Expr.close st v))
  | .arrayMake o n v => do pure (.arrayMake o (← Expr.close st n) (← Expr.close st v))
  | .arrayLen a => do pure (.arrayLen (← Expr.close st a))
  | .arrayGet a i ty => do
      pure (.arrayGet (← Expr.close st a) (← Expr.close st i) (← State.close st ty))
  | .arraySet a i v => do
      pure (.arraySet (← Expr.close st a) (← Expr.close st i) (← Expr.close st v))
  | .assert e => do pure (.assert (← Expr.close st e))
  | .tuple es => do pure (.tuple (← Expr.closeList st es))
  | .inj tag arity payload ty => do
      pure (.inj tag arity (← Expr.close st payload) (← State.close st ty))
  | .match_ e branches ty => do
      let branches ← Expr.closeBranches st branches
      pure (.match_ (← Expr.close st e) branches (← State.close st ty))
termination_by structural e => e

def Expr.closeList (st : State) :
    List Expr → Except TypeError (List Typed.Expr)
  | [] => pure []
  | e :: es => do pure ((← Expr.close st e) :: (← Expr.closeList st es))
termination_by structural es => es

def Expr.closeBranches (st : State) :
    List (Binder × Expr) → Except TypeError (List (Typed.Binder × Typed.Expr))
  | [] => pure []
  | (b, e) :: branches => do
      pure ((← Binder.close st b, ← Expr.close st e) :: (← Expr.closeBranches st branches))
termination_by structural branches => branches

end

/-- Typing context during inference: what each name is bound at, with the
variables its uses may instantiate and a type that may still mention
metavariables. -/
abbrev Ctx := TinyML.Var → Option (List TyVar × Typ)

def Ctx.ofTyCtx (Γ : TinyML.TyCtx) : Ctx :=
  fun x => (Γ x).map fun s => (s.tparams, Typ.ofTyp s.ty)

def Ctx.extend (Γ : Ctx) (x : TinyML.Var) (ty : Typ) : Ctx :=
  fun y => if y == x then some ([], ty) else Γ y

def Ctx.extendBinder (Γ : Ctx) (b : Binder) : Ctx :=
  match b.name with | none => Γ | some x => Γ.extend x b.ty

def Ctx.extendList (Γ : Ctx) (bs : List Binder) : Ctx :=
  bs.foldl Ctx.extendBinder Γ


/-! ## The inference monad

An expression is elaborated against the type expected of it, accumulating
equality constraints as it goes. Where the syntax expects nothing the caller
supplies a fresh metavariable.

The state is threaded under the monad elaboration already runs in, so a rule can
both solve types and use whatever effect `σ` carries. -/

abbrev M (σ : Type) := StateT State (TypeM σ)

def error (e : TypeError) : M σ α := StateT.lift (TypeM.error e)

@[simp] theorem error_apply (e : TypeError) (st : State) (s : σ) :
    (error e : M σ α) st s = .error e := rfl

def fresh : M σ Typ := fun st => pure st.fresh

def freshList : Nat → M σ (List Typ)
  | 0 => pure []
  | n + 1 => do pure ((← fresh) :: (← freshList n))

/-- Require two types to be equal, solving metavariables to make them so. -/
def unify (Θ : TypeEnv) (a b : Typ) : M σ Unit := fun st =>
  match st.unify Θ a b with
  | .ok st' => pure ((), st')
  | .error e => TypeM.error e

def resolve (ty : Typ) : M σ Typ := do
  pure ((← get).resolve ty)

/-- Instantiate a primitive's scheme at fresh metavariables. -/
def instantiate (s : SchemaTyp) : M σ (Typ × List (TyVar × Typ)) := fun st =>
  let (ty, inst, st') := st.instantiate s
  pure ((ty, inst), st')

/-- Instantiate a context entry at fresh metavariables for the variables it
quantifies. -/
def instantiateAt (tparams : List TyVar) (ty : Typ) : M σ (Typ × List (TyVar × Typ)) :=
  fun st =>
  let (ty', inst, st') := st.instantiateAt tparams ty
  pure ((ty', inst), st')

/-- Require a list to have the length the syntax around it demands. -/
def checkLength (actual expected : Nat) : M σ Unit :=
  if actual == expected then pure () else error (.arityMismatch actual expected)

/-! ## Constraints

Each of these says what the syntax around a subexpression demands of its type:
`?t = C ?a₁ … ?aₙ`, solved against the type and handing back the components.

Two of them pick something the syntax does not determine. `ref` and `array` pick
shared over owned, since a metavariable carries no ownership; a program that
meant owned has to say so. `arrow` picks the unspecified arrow — see the comment
there. -/

namespace Constraint

/-- `?t = array ?a`, or the owned array if the type already says so. An unsolved
type is solved to a shared array. -/
def array (Θ : TypeEnv) (ty : Typ) : M σ Typ := do
  match ← resolve ty with
  | .array inner | .ownedArray inner => pure inner
  | t@(.tvar (.flex _)) => do
      let inner ← fresh
      unify Θ t (.array inner)
      pure inner
  | other => error (.notA "an array" other)

/-- `?t = ref ?a`, or the owned reference if the type already says so. An
unsolved type is solved to a shared reference. -/
def ref (Θ : TypeEnv) (ty : Typ) : M σ Typ := do
  match ← resolve ty with
  | .owned inner | .ref inner => pure inner
  | t@(.tvar (.flex _)) => do
      let inner ← fresh
      unify Θ t (.ref inner)
      pure inner
  | other => error (.notA "a reference" other)

/-- The `n`-th component of a tuple. Not a constraint: a projection says only
that the tuple has at least `n + 1` components, and solving an open type to
exactly that many would be wrong for every wider tuple. -/
def tuple (_Θ : TypeEnv) (ty : Typ) (n : Nat) : M σ Typ := do
  let elems ← match ← resolve ty with
    | .tuple elems => pure elems
    | other => error (.notA "a tuple" other)
  match elems[n]? with
  | some ty => pure ty
  | none => error (.arityMismatch (n + 1) elems.length)

/-- `?t = ?d₁ → … → ?dₙ → ?r`, with whatever specification the arrow carries. -/
def arrow (Θ : TypeEnv) (ty : Typ) (n : Nat) : M σ (List Typ × Typ × Option (Spec Typ)) := do
  match ← resolve ty with
  | .arrow doms ret spec => do
      checkLength doms.length n
      pure (doms, ret, spec)
  | t@(.tvar (.flex _)) => do
      let doms ← freshList n
      let ret ← fresh
      -- `spec := none` is a default, not something the syntax decided: a
      -- metavariable cannot carry a specification, so a function whose type is
      -- still open is assumed unspecified. A unification variable for the
      -- specification slot would be the honest fix, and would also let a
      -- specified arrow reach a literal stored in a `ref`.
      unify Θ t (.arrow doms ret none)
      pure (doms, ret, none)
  | other => error (.notA "a function" other)

/-! ### Named types and the sums they abbreviate

A value of a named type is built at the name and destructured at the sum. An
injection carries the name, so the declaration need only give it the payload's
type; a `match` resolves its scrutinee's type and unfolds it. The verifier
unfolds the name again where it compiles either one, so neither has to record
the unfolding on the term. Either way the declaration is unfolded once, never
recursively. -/

/-- The payloads a name's declaration gives it, if the name has a declaration. -/
def unfoldSum (Θ : TypeEnv) (T : TypeName) (args : List Typ) : Option (List Typ) :=
  match TypeName.unfold Θ T args with
  | some (.sum payloads) => some payloads
  | _ => none

/-- `?t = T ?a₁ … ?aₖ`, at as many fresh arguments as `T`'s declaration takes.
This is what types a constructor at the name it was declared under: the use site
decides the arguments, so `[]` needs no annotation. -/
def named (Θ : TypeEnv) (T : TypeName) (ty : Typ) : M σ (List Typ) :=
  match TypeName.params Θ T with
  | none => error (.notA "a declared type" (.named T []))
  | some k => do
      let args ← freshList k
      unify Θ (.named T args) ty
      pure args

/-- The `tag`-th payload the declaration of `T` gives at `args`. Reading it off
the declaration is what keeps an injection's own type folded. -/
def payloadOf (Θ : TypeEnv) (T : TypeName) (args : List Typ) (tag arity : Nat) : M σ Typ :=
  match unfoldSum Θ T args with
  | none => error (.notA "a sum" (.named T args))
  | some payloads => do
      checkLength payloads.length arity
      match payloads[tag]? with
      | some ty => pure ty
      | none => error (.arityMismatch (tag + 1) arity)

/-- `?t = sum ?a₁ … ?aₙ`, the payloads a `match` destructures its scrutinee at.
A named type is unfolded to the sum it abbreviates. -/
def sum (Θ : TypeEnv) (ty : Typ) (branches : Nat) : M σ (List Typ) := do
  match ← resolve ty with
  | .sum payloads => do
      checkLength payloads.length branches
      pure payloads
  | .named T args =>
      match unfoldSum Θ T args with
      | some payloads => do
          checkLength payloads.length branches
          pure payloads
      | none => error (.notA "a sum" (.named T args))
  | .tvar (.flex v) => do
      let payloads ← freshList branches
      unify Θ (.tvar (.flex v)) (.sum payloads)
      pure payloads
  | other => error (.notA "a sum" other)

end Constraint

/-- Run inference with unification: from a fresh state, at the type expected of
the expression when there is one and at a fresh metavariable otherwise, closing
whatever the pass produced.  -/
def run  (k : Typ → M σ Expr) : Option TinyML.Typ → TypeM σ Typed.Expr :=
  fun expected => do
  let start : Typ × State := match expected with
    | some t => (Typ.ofTyp t, {})
    | none => State.fresh {}
  let (pending, st) ← k start.1 start.2
  TypeM.ofExcept (Expr.close st pending)

/-- Inversion for `run`: the pass ran at some type and state, and what it
produced was closed. Every fact about a boundary is proved through this. -/
theorem run_ok {expected : Option TinyML.Typ} {k : Typ → M σ Expr} {s s' : σ}
    {e' : Typed.Expr} (h : run k expected s = .ok (e', s')) :
    ∃ ty st st' p, k ty st s = .ok ((p, st'), s') ∧ Expr.close st' p = .ok e' := by
  unfold run at h
  have ⟨q, s₀, hk, hclose⟩ := StateT.bind_ok h
  obtain ⟨p, st'⟩ := q
  obtain ⟨hcl, rfl⟩ := TypeM.ofExcept_ok.mp hclose
  exact ⟨_, _, st', p, hk, hcl⟩

end Infer

end Typed
