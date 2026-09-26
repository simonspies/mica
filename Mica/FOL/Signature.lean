-- SUMMARY: Signatures: the variables and symbols in scope, with their sorts.
import Mica.FOL.Sorts
import Mathlib.Data.List.Nodup

/-!
# Signatures

A signature lists the names that a term or a formula can use: variables,
constants, functions, and relations, each with its sorts. A signature is
well-formed when each name occurs only once.
-/

/-! ## Variables -/

structure Var where
  name : String
  sort : Srt
  deriving DecidableEq, Repr

/-! ## Symbol declarations -/

namespace Decl

structure Const where
  name : String
  sort : Srt
  deriving DecidableEq, Repr

structure Unary where
  name : String
  arg  : Srt
  ret  : Srt
  deriving DecidableEq, Repr

structure Binary where
  name : String
  arg1 : Srt
  arg2 : Srt
  ret  : Srt
  deriving DecidableEq, Repr

structure Ternary where
  name : String
  arg1 : Srt
  arg2 : Srt
  arg3 : Srt
  ret  : Srt
  deriving DecidableEq, Repr

structure UnaryRel where
  name : String
  arg  : Srt
  deriving DecidableEq, Repr

structure BinaryRel where
  name : String
  arg1 : Srt
  arg2 : Srt
  deriving DecidableEq, Repr

end Decl

/-! ## Signatures -/

structure Signature where
  vars   : List Var
  consts : List Decl.Const
  unary  : List Decl.Unary
  binary : List Decl.Binary
  ternary : List Decl.Ternary
  unaryRel  : List Decl.UnaryRel
  binaryRel : List Decl.BinaryRel

namespace Signature

def empty : Signature := ⟨[], [], [], [], [], [], []⟩

@[simp] theorem empty_vars    : (empty : Signature).vars   = [] := rfl
@[simp] theorem empty_consts  : (empty : Signature).consts = [] := rfl
@[simp] theorem empty_unary   : (empty : Signature).unary  = [] := rfl
@[simp] theorem empty_binary  : (empty : Signature).binary = [] := rfl
@[simp] theorem empty_ternary : (empty : Signature).ternary = [] := rfl
@[simp] theorem empty_unaryRel : (empty : Signature).unaryRel = [] := rfl
@[simp] theorem empty_binaryRel : (empty : Signature).binaryRel = [] := rfl

def addVar (Δ : Signature) (v : Var) : Signature := { Δ with vars := v :: Δ.vars }

def addConst (Δ : Signature) (c : Decl.Const) : Signature := { Δ with consts := c :: Δ.consts }
def addUnary (Δ : Signature) (u : Decl.Unary) : Signature := { Δ with unary := u :: Δ.unary }
def addBinary (Δ : Signature) (b : Decl.Binary) : Signature := { Δ with binary := b :: Δ.binary }
def addTernary (Δ : Signature) (t : Decl.Ternary) : Signature := { Δ with ternary := t :: Δ.ternary }
def addUnaryRel (Δ : Signature) (u : Decl.UnaryRel) : Signature := { Δ with unaryRel := u :: Δ.unaryRel }
def addBinaryRel (Δ : Signature) (b : Decl.BinaryRel) : Signature := { Δ with binaryRel := b :: Δ.binaryRel }
def remove (Δ : Signature) (x : String) : Signature :=
  { vars := Δ.vars.filter (·.name != x)
    consts := Δ.consts.filter (·.name != x)
    unary := Δ.unary.filter (·.name != x)
    binary := Δ.binary.filter (·.name != x)
    ternary := Δ.ternary.filter (·.name != x)
    unaryRel := Δ.unaryRel.filter (·.name != x)
    binaryRel := Δ.binaryRel.filter (·.name != x) }

/-- Add a variable and remove all other declarations of its name, as a binder
hides the outer uses of its name. -/
def declVar (Δ : Signature) (v : Var) : Signature := (Δ.remove v.name).addVar v

def declVars (Δ : Signature) (vs : List Var) : Signature := vs.foldl declVar Δ

def allNames (Δ : Signature) : List String :=
  Δ.vars.map Var.name ++ Δ.consts.map Decl.Const.name ++
  Δ.unary.map Decl.Unary.name ++ Δ.binary.map Decl.Binary.name ++
  Δ.ternary.map Decl.Ternary.name ++
  Δ.unaryRel.map Decl.UnaryRel.name ++ Δ.binaryRel.map Decl.BinaryRel.name

/-- No name is declared twice. -/
def wf (Δ : Signature) : Prop := Δ.allNames.Nodup

def ofConsts (consts : List Decl.Const) : Signature := ⟨[], consts, [], [], [], [], []⟩

@[simp] theorem ofConsts_consts (consts : List Decl.Const) : (ofConsts consts).consts = consts := rfl

/-! ### Membership -/

@[simp] theorem mem_remove_vars {Δ : Signature} {v : Var} {x : String} :
    v ∈ (Δ.remove x).vars ↔ v ∈ Δ.vars ∧ v.name ≠ x := by
  simp [remove]

@[simp] theorem mem_remove_consts {Δ : Signature} {c : Decl.Const} {x : String} :
    c ∈ (Δ.remove x).consts ↔ c ∈ Δ.consts ∧ c.name ≠ x := by
  simp [remove]

@[simp] theorem mem_remove_unary {Δ : Signature} {u : Decl.Unary} {x : String} :
    u ∈ (Δ.remove x).unary ↔ u ∈ Δ.unary ∧ u.name ≠ x := by
  simp [remove]

@[simp] theorem mem_remove_binary {Δ : Signature} {b : Decl.Binary} {x : String} :
    b ∈ (Δ.remove x).binary ↔ b ∈ Δ.binary ∧ b.name ≠ x := by
  simp [remove]

@[simp] theorem mem_remove_ternary {Δ : Signature} {t : Decl.Ternary} {x : String} :
    t ∈ (Δ.remove x).ternary ↔ t ∈ Δ.ternary ∧ t.name ≠ x := by
  simp [remove]

@[simp] theorem mem_remove_unaryRel {Δ : Signature} {u : Decl.UnaryRel} {x : String} :
    u ∈ (Δ.remove x).unaryRel ↔ u ∈ Δ.unaryRel ∧ u.name ≠ x := by
  simp [remove]

@[simp] theorem mem_remove_binaryRel {Δ : Signature} {b : Decl.BinaryRel} {x : String} :
    b ∈ (Δ.remove x).binaryRel ↔ b ∈ Δ.binaryRel ∧ b.name ≠ x := by
  simp [remove]

@[simp] theorem mem_declVar_vars {Δ : Signature} {v w : Var} :
    w ∈ (Δ.declVar v).vars ↔ w = v ∨ (w ∈ Δ.vars ∧ w.name ≠ v.name) := by
  simp [declVar, addVar]

@[simp] theorem mem_declVar_consts {Δ : Signature} {v : Var} {c : Decl.Const} :
    c ∈ (Δ.declVar v).consts ↔ c ∈ Δ.consts ∧ c.name ≠ v.name := mem_remove_consts

@[simp] theorem mem_declVar_unary {Δ : Signature} {v : Var} {u : Decl.Unary} :
    u ∈ (Δ.declVar v).unary ↔ u ∈ Δ.unary ∧ u.name ≠ v.name := mem_remove_unary

@[simp] theorem mem_declVar_binary {Δ : Signature} {v : Var} {b : Decl.Binary} :
    b ∈ (Δ.declVar v).binary ↔ b ∈ Δ.binary ∧ b.name ≠ v.name := mem_remove_binary

@[simp] theorem mem_declVar_ternary {Δ : Signature} {v : Var} {t : Decl.Ternary} :
    t ∈ (Δ.declVar v).ternary ↔ t ∈ Δ.ternary ∧ t.name ≠ v.name := mem_remove_ternary

@[simp] theorem mem_declVar_unaryRel {Δ : Signature} {v : Var} {u : Decl.UnaryRel} :
    u ∈ (Δ.declVar v).unaryRel ↔ u ∈ Δ.unaryRel ∧ u.name ≠ v.name := mem_remove_unaryRel

@[simp] theorem mem_declVar_binaryRel {Δ : Signature} {v : Var} {b : Decl.BinaryRel} :
    b ∈ (Δ.declVar v).binaryRel ↔ b ∈ Δ.binaryRel ∧ b.name ≠ v.name := mem_remove_binaryRel

theorem var_mem_declVar (Δ : Signature) (v : Var) : v ∈ (Δ.declVar v).vars :=
  List.Mem.head _

theorem remove_eq_of_not_in {Δ : Signature} {x : String} (h : x ∉ Δ.allNames) :
    Δ.remove x = Δ := by
  cases Δ
  simp_all [allNames, remove, List.filter_eq_self]

theorem vars_declVar_of_not_in {Δ : Signature} {v : Var}
    (h : v.name ∉ Δ.allNames) : (Δ.declVar v).vars = v :: Δ.vars := by
  rw [declVar, remove_eq_of_not_in h]
  rfl

/-! ### Inclusion -/

structure Subset (Δ₁ Δ₂ : Signature) : Prop where
  vars   : ∀ x ∈ Δ₁.vars, x ∈ Δ₂.vars
  consts : ∀ c ∈ Δ₁.consts, c ∈ Δ₂.consts
  unary  : ∀ u ∈ Δ₁.unary, u ∈ Δ₂.unary
  binary : ∀ b ∈ Δ₁.binary, b ∈ Δ₂.binary
  ternary : ∀ t ∈ Δ₁.ternary, t ∈ Δ₂.ternary
  unaryRel : ∀ u ∈ Δ₁.unaryRel, u ∈ Δ₂.unaryRel
  binaryRel : ∀ b ∈ Δ₁.binaryRel, b ∈ Δ₂.binaryRel

theorem Subset.refl (Δ : Signature) : Δ.Subset Δ :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.trans {Δ₁ Δ₂ Δ₃ : Signature} (h₁₂ : Δ₁.Subset Δ₂) (h₂₃ : Δ₂.Subset Δ₃) :
    Δ₁.Subset Δ₃ :=
  ⟨fun x hx => h₂₃.vars x (h₁₂.vars x hx),
   fun c hc => h₂₃.consts c (h₁₂.consts c hc),
   fun u hu => h₂₃.unary u (h₁₂.unary u hu),
   fun b hb => h₂₃.binary b (h₁₂.binary b hb),
   fun t ht => h₂₃.ternary t (h₁₂.ternary t ht),
   fun u hu => h₂₃.unaryRel u (h₁₂.unaryRel u hu),
   fun b hb => h₂₃.binaryRel b (h₁₂.binaryRel b hb)⟩

theorem empty_subset (Δ : Signature) : Signature.empty.Subset Δ :=
  ⟨fun _ h => by simp [Signature.empty] at h,
   fun _ h => by simp [Signature.empty] at h,
   fun _ h => by simp [Signature.empty] at h,
   fun _ h => by simp [Signature.empty] at h,
   fun _ h => by simp [Signature.empty] at h,
   fun _ h => by simp [Signature.empty] at h,
   fun _ h => by simp [Signature.empty] at h⟩

theorem Subset.subset_addVar (Δ : Signature) (v : Var) :
    Δ.Subset (Δ.addVar v) :=
  ⟨fun _ hx => List.mem_cons_of_mem _ hx, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.subset_addConst (Δ : Signature) (c : Decl.Const) :
    Δ.Subset (Δ.addConst c) :=
  ⟨fun _ h => h, fun _ hc => List.mem_cons_of_mem _ hc, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.subset_addUnary (Δ : Signature) (u : Decl.Unary) :
    Δ.Subset (Δ.addUnary u) :=
  ⟨fun _ h => h, fun _ h => h, fun _ hu => List.mem_cons_of_mem _ hu, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.subset_addBinary (Δ : Signature) (b : Decl.Binary) :
    Δ.Subset (Δ.addBinary b) :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ hb => List.mem_cons_of_mem _ hb, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.subset_addTernary (Δ : Signature) (t : Decl.Ternary) :
    Δ.Subset (Δ.addTernary t) :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
   fun _ ht => List.mem_cons_of_mem _ ht, fun _ h => h, fun _ h => h⟩

theorem Subset.subset_addUnaryRel (Δ : Signature) (u : Decl.UnaryRel) :
    Δ.Subset (Δ.addUnaryRel u) :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ hu => List.mem_cons_of_mem _ hu, fun _ h => h⟩

theorem Subset.subset_addBinaryRel (Δ : Signature) (b : Decl.BinaryRel) :
    Δ.Subset (Δ.addBinaryRel b) :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ hb => List.mem_cons_of_mem _ hb⟩

theorem Subset.addVar {Δ Δ' : Signature} (h : Δ.Subset Δ') (v : Var) :
    (Δ.addVar v).Subset (Δ'.addVar v) :=
  ⟨fun x hx => by cases hx with | head => left | tail _ hmem => right; exact h.vars x hmem,
   h.consts,
   h.unary,
   h.binary,
   h.ternary,
   h.unaryRel,
   h.binaryRel⟩

theorem Subset.addConst {Δ Δ' : Signature} (h : Δ.Subset Δ') (s : Decl.Const) :
    (Δ.addConst s).Subset (Δ'.addConst s) :=
  ⟨h.vars,
   fun x hx => by cases hx with | head => left | tail _ hmem => right; exact h.consts x hmem,
   h.unary,
   h.binary,
   h.ternary,
   h.unaryRel,
   h.binaryRel⟩

theorem Subset.addUnary {Δ Δ' : Signature} (h : Δ.Subset Δ') (s : Decl.Unary) :
    (Δ.addUnary s).Subset (Δ'.addUnary s) :=
  ⟨h.vars,
   h.consts,
   fun x hx => by cases hx with | head => left | tail _ hmem => right; exact h.unary x hmem,
   h.binary,
   h.ternary,
   h.unaryRel,
   h.binaryRel⟩

theorem Subset.addBinary {Δ Δ' : Signature} (h : Δ.Subset Δ') (s : Decl.Binary) :
    (Δ.addBinary s).Subset (Δ'.addBinary s) :=
  ⟨h.vars,
   h.consts,
   h.unary,
   fun x hx => by cases hx with | head => left | tail _ hmem => right; exact h.binary x hmem,
   h.ternary,
   h.unaryRel,
   h.binaryRel⟩

theorem Subset.addTernary {Δ Δ' : Signature} (h : Δ.Subset Δ') (s : Decl.Ternary) :
    (Δ.addTernary s).Subset (Δ'.addTernary s) :=
  ⟨h.vars,
   h.consts,
   h.unary,
   h.binary,
   fun x hx => by cases hx with | head => left | tail _ hmem => right; exact h.ternary x hmem,
   h.unaryRel,
   h.binaryRel⟩

theorem Subset.addUnaryRel {Δ Δ' : Signature} (h : Δ.Subset Δ') (s : Decl.UnaryRel) :
    (Δ.addUnaryRel s).Subset (Δ'.addUnaryRel s) :=
  ⟨h.vars,
   h.consts,
   h.unary,
   h.binary,
   h.ternary,
   fun x hx => by cases hx with | head => left | tail _ hmem => right; exact h.unaryRel x hmem,
   h.binaryRel⟩

theorem Subset.addBinaryRel {Δ Δ' : Signature} (h : Δ.Subset Δ') (s : Decl.BinaryRel) :
    (Δ.addBinaryRel s).Subset (Δ'.addBinaryRel s) :=
  ⟨h.vars,
   h.consts,
   h.unary,
   h.binary,
   h.ternary,
   h.unaryRel,
   fun x hx => by cases hx with | head => left | tail _ hmem => right; exact h.binaryRel x hmem⟩

theorem remove_subset (Δ : Signature) (x : String) : (Δ.remove x).Subset Δ :=
  ⟨fun _ h => (mem_remove_vars.mp h).1,
   fun _ h => (mem_remove_consts.mp h).1,
   fun _ h => (mem_remove_unary.mp h).1,
   fun _ h => (mem_remove_binary.mp h).1,
   fun _ h => (mem_remove_ternary.mp h).1,
   fun _ h => (mem_remove_unaryRel.mp h).1,
   fun _ h => (mem_remove_binaryRel.mp h).1⟩

theorem Subset.remove {Δ Δ' : Signature} (h : Δ.Subset Δ') (x : String) :
    (Δ.remove x).Subset (Δ'.remove x) :=
  ⟨fun _ h' => mem_remove_vars.mpr ((mem_remove_vars.mp h').imp_left (h.vars _)),
   fun _ h' => mem_remove_consts.mpr ((mem_remove_consts.mp h').imp_left (h.consts _)),
   fun _ h' => mem_remove_unary.mpr ((mem_remove_unary.mp h').imp_left (h.unary _)),
   fun _ h' => mem_remove_binary.mpr ((mem_remove_binary.mp h').imp_left (h.binary _)),
   fun _ h' => mem_remove_ternary.mpr ((mem_remove_ternary.mp h').imp_left (h.ternary _)),
   fun _ h' => mem_remove_unaryRel.mpr ((mem_remove_unaryRel.mp h').imp_left (h.unaryRel _)),
   fun _ h' => mem_remove_binaryRel.mpr ((mem_remove_binaryRel.mp h').imp_left (h.binaryRel _))⟩

theorem Subset.declVar {Δ Δ' : Signature} (h : Δ.Subset Δ') (v : Var) :
    (Δ.declVar v).Subset (Δ'.declVar v) := by
  simpa [declVar] using (Subset.addVar (Subset.remove h v.name) v)

theorem Subset.declVars {Δ Δ' : Signature} (h : Δ.Subset Δ') (vs : List Var) :
    (Δ.declVars vs).Subset (Δ'.declVars vs) := by
  induction vs generalizing Δ Δ' with
  | nil => simpa [declVars] using h
  | cons v vs ih =>
    simpa [declVars] using ih (Subset.declVar h v)

theorem subset_declVar_of_fresh {Δ : Signature} {v : Var}
    (hfresh : v.name ∉ Δ.allNames) : Δ.Subset (Δ.declVar v) := by
  have heq : Δ.declVar v = Δ.addVar v := by
    show (Δ.remove v.name).addVar v = Δ.addVar v
    rw [Signature.remove_eq_of_not_in hfresh]
  rw [heq]
  exact Signature.Subset.subset_addVar Δ v

theorem allNames_subset {Δ Δ' : Signature} (h : Δ.Subset Δ') :
    ∀ n ∈ Δ.allNames, n ∈ Δ'.allNames := by
  intro n hn
  simp only [allNames, List.mem_append, List.mem_map] at hn ⊢
  rcases hn with ⟨⟨⟨⟨⟨⟨v, hv, rfl⟩ | ⟨c, hc, rfl⟩⟩ | ⟨u, hu, rfl⟩⟩ | ⟨b, hb, rfl⟩⟩ | ⟨t, ht, rfl⟩⟩ | ⟨u, hu, rfl⟩⟩ | ⟨b, hb, rfl⟩
  · left; left; left; left; left; left; exact ⟨v, h.vars v hv, rfl⟩
  · left; left; left; left; left; right; exact ⟨c, h.consts c hc, rfl⟩
  · left; left; left; left; right; exact ⟨u, h.unary u hu, rfl⟩
  · left; left; left; right; exact ⟨b, h.binary b hb, rfl⟩
  · left; left; right; exact ⟨t, h.ternary t ht, rfl⟩
  · left; right; exact ⟨u, h.unaryRel u hu, rfl⟩
  · right; exact ⟨b, h.binaryRel b hb, rfl⟩

theorem remove_allNames_subset {Δ : Signature} {x n : String} (h : n ∈ (Δ.remove x).allNames) :
    n ∈ Δ.allNames :=
  allNames_subset (remove_subset Δ x) _ h

/-! ### Names -/

theorem mem_allNames_of_var {Δ : Signature} {v : Var} (h : v ∈ Δ.vars) :
    v.name ∈ Δ.allNames := by
  simp only [allNames, List.mem_append]
  simp [List.mem_map_of_mem h]

theorem mem_allNames_of_const {Δ : Signature} {c : Decl.Const} (h : c ∈ Δ.consts) :
    c.name ∈ Δ.allNames := by
  simp only [allNames, List.mem_append]
  simp [List.mem_map_of_mem h]

theorem mem_allNames_of_unary {Δ : Signature} {u : Decl.Unary} (h : u ∈ Δ.unary) :
    u.name ∈ Δ.allNames := by
  simp only [allNames, List.mem_append]
  simp [List.mem_map_of_mem h]

theorem mem_allNames_of_binary {Δ : Signature} {b : Decl.Binary} (h : b ∈ Δ.binary) :
    b.name ∈ Δ.allNames := by
  simp only [allNames, List.mem_append]
  simp [List.mem_map_of_mem h]

theorem mem_allNames_of_ternary {Δ : Signature} {t : Decl.Ternary} (h : t ∈ Δ.ternary) :
    t.name ∈ Δ.allNames := by
  simp only [allNames, List.mem_append]
  simp [List.mem_map_of_mem h]

theorem mem_allNames_of_unaryRel {Δ : Signature} {u : Decl.UnaryRel} (h : u ∈ Δ.unaryRel) :
    u.name ∈ Δ.allNames := by
  simp only [allNames, List.mem_append]
  simp [List.mem_map_of_mem h]

theorem mem_allNames_of_binaryRel {Δ : Signature} {b : Decl.BinaryRel} (h : b ∈ Δ.binaryRel) :
    b.name ∈ Δ.allNames := by
  simp only [allNames, List.mem_append]
  simp [List.mem_map_of_mem h]

theorem remove_allNames {Δ : Signature} {n x : String} (h : n ∈ (Δ.remove x).allNames) :
    n ≠ x := by
  rintro rfl
  simp [allNames, remove, and_assoc] at h

theorem allNames_declVar_of_not_in {Δ : Signature} {x : String} {τ : Srt}
    (h : x ∉ Δ.allNames) : (Δ.declVar ⟨x, τ⟩).allNames = x :: Δ.allNames := by
  rw [declVar, remove_eq_of_not_in h]
  simp [allNames, addVar]

theorem not_mem_allNames_addConst {Δ : Signature} {s : Decl.Const} {x : String}
    (hΔ : x ∉ Δ.allNames) (hs : x ≠ s.name) : x ∉ (Δ.addConst s).allNames := by
  simp_all [allNames, addConst]

theorem not_mem_allNames_addUnary {Δ : Signature} {s : Decl.Unary} {x : String}
    (hΔ : x ∉ Δ.allNames) (hs : x ≠ s.name) : x ∉ (Δ.addUnary s).allNames := by
  simp_all [allNames, addUnary]

theorem not_mem_allNames_addBinary {Δ : Signature} {s : Decl.Binary} {x : String}
    (hΔ : x ∉ Δ.allNames) (hs : x ≠ s.name) : x ∉ (Δ.addBinary s).allNames := by
  simp_all [allNames, addBinary]

theorem not_mem_allNames_addTernary {Δ : Signature} {s : Decl.Ternary} {x : String}
    (hΔ : x ∉ Δ.allNames) (hs : x ≠ s.name) : x ∉ (Δ.addTernary s).allNames := by
  simp_all [allNames, addTernary]

theorem not_mem_allNames_addUnaryRel {Δ : Signature} {s : Decl.UnaryRel} {x : String}
    (hΔ : x ∉ Δ.allNames) (hs : x ≠ s.name) : x ∉ (Δ.addUnaryRel s).allNames := by
  simp_all [allNames, addUnaryRel]

theorem not_mem_allNames_addBinaryRel {Δ : Signature} {s : Decl.BinaryRel} {x : String}
    (hΔ : x ∉ Δ.allNames) (hs : x ≠ s.name) : x ∉ (Δ.addBinaryRel s).allNames := by
  simp_all [allNames, addBinaryRel]

theorem not_mem_allNames_declVar {Δ : Signature} {v : Var} {x : String}
    (hΔ : x ∉ Δ.allNames) (hv : x ≠ v.name) :
    x ∉ (Δ.declVar v).allNames := by
  intro h
  have h' : x ∈ v.name :: (Δ.remove v.name).allNames := by
    simpa [Signature.declVar, Signature.addVar, Signature.allNames] using h
  cases h' with
  | head => exact hv rfl
  | tail _ htail => exact hΔ (Signature.remove_allNames_subset htail)

/-! ### Well-formedness -/

theorem wf_addVar {Δ : Signature} {v : Var}
    (hΔ : Δ.wf) (hfresh : v.name ∉ Δ.allNames) : (Δ.addVar v).wf :=
  List.nodup_cons.mpr ⟨hfresh, hΔ⟩

theorem wf_addConst {Δ : Signature} {c : Decl.Const}
    (hΔ : Δ.wf) (hfresh : c.name ∉ Δ.allNames) : (Δ.addConst c).wf := by
  refine (List.Perm.nodup_iff ?_).mpr (List.nodup_cons.mpr ⟨hfresh, hΔ⟩)
  simp [allNames, addConst, List.perm_iff_count, List.count_cons]
  omega

theorem wf_addUnary {Δ : Signature} {u : Decl.Unary}
    (hΔ : Δ.wf) (hfresh : u.name ∉ Δ.allNames) : (Δ.addUnary u).wf := by
  refine (List.Perm.nodup_iff ?_).mpr (List.nodup_cons.mpr ⟨hfresh, hΔ⟩)
  simp [allNames, addUnary, List.perm_iff_count, List.count_cons]
  omega

theorem wf_addBinary {Δ : Signature} {b : Decl.Binary}
    (hΔ : Δ.wf) (hfresh : b.name ∉ Δ.allNames) : (Δ.addBinary b).wf := by
  refine (List.Perm.nodup_iff ?_).mpr (List.nodup_cons.mpr ⟨hfresh, hΔ⟩)
  simp [allNames, addBinary, List.perm_iff_count, List.count_cons]
  omega

theorem wf_addTernary {Δ : Signature} {t : Decl.Ternary}
    (hΔ : Δ.wf) (hfresh : t.name ∉ Δ.allNames) : (Δ.addTernary t).wf := by
  refine (List.Perm.nodup_iff ?_).mpr (List.nodup_cons.mpr ⟨hfresh, hΔ⟩)
  simp [allNames, addTernary, List.perm_iff_count, List.count_cons]
  omega

theorem wf_addUnaryRel {Δ : Signature} {u : Decl.UnaryRel}
    (hΔ : Δ.wf) (hfresh : u.name ∉ Δ.allNames) : (Δ.addUnaryRel u).wf := by
  refine (List.Perm.nodup_iff ?_).mpr (List.nodup_cons.mpr ⟨hfresh, hΔ⟩)
  simp [allNames, addUnaryRel, List.perm_iff_count, List.count_cons]
  omega

theorem wf_addBinaryRel {Δ : Signature} {b : Decl.BinaryRel}
    (hΔ : Δ.wf) (hfresh : b.name ∉ Δ.allNames) : (Δ.addBinaryRel b).wf := by
  refine (List.Perm.nodup_iff ?_).mpr (List.nodup_cons.mpr ⟨hfresh, hΔ⟩)
  simp [allNames, addBinaryRel, List.perm_iff_count, List.count_cons]
  omega

private theorem allNames_remove_sublist (Δ : Signature) (x : String) :
    List.Sublist (Δ.remove x).allNames Δ.allNames := by
  simp only [remove, allNames]
  repeat' apply List.Sublist.append
  all_goals exact List.filter_sublist.map _

theorem wf_remove {Δ : Signature} (hΔ : Δ.wf) (x : String) : (Δ.remove x).wf := by
  rw [wf] at hΔ ⊢
  exact hΔ.sublist (allNames_remove_sublist Δ x)

theorem wf_declVar {Δ : Signature} {v : Var} (hΔ : Δ.wf) : (Δ.declVar v).wf :=
  wf_addVar (wf_remove hΔ v.name) fun h => remove_allNames h rfl

theorem wf_declVars {Δ : Signature} {vs : List Var} (hΔ : Δ.wf) : (Δ.declVars vs).wf := by
  induction vs generalizing Δ with
  | nil =>
    simpa [declVars] using hΔ
  | cons v vs ih =>
    simpa [declVars] using ih (wf_declVar (Δ := Δ) (v := v) hΔ)

theorem wf_unique_var {Δ : Signature} {x : String} {τ τ' : Srt}
    (hΔ : Δ.wf) (hv : ⟨x, τ⟩ ∈ Δ.vars) (hv' : ⟨x, τ'⟩ ∈ Δ.vars) : τ' = τ := by
  have hnd : (Δ.vars.map Var.name).Nodup := hΔ.sublist (by grind [allNames])
  cases List.inj_on_of_nodup_map hnd hv hv' rfl
  exact rfl

theorem wf_unique_const {Δ : Signature} {x : String} {τ τ' : Srt}
    (hΔ : Δ.wf) (hc : ⟨x, τ⟩ ∈ Δ.consts) (hc' : ⟨x, τ'⟩ ∈ Δ.consts) : τ' = τ := by
  have hnd : (Δ.consts.map Decl.Const.name).Nodup := hΔ.sublist (by grind [allNames])
  cases List.inj_on_of_nodup_map hnd hc hc' rfl
  exact rfl

theorem wf_unique_unary {Δ : Signature} {x : String} {τ₁ τ₂ τ₁' τ₂' : Srt}
    (hΔ : Δ.wf) (hu : ⟨x, τ₁, τ₂⟩ ∈ Δ.unary) (hu' : ⟨x, τ₁', τ₂'⟩ ∈ Δ.unary) :
    τ₁' = τ₁ ∧ τ₂' = τ₂ := by
  have hnd : (Δ.unary.map Decl.Unary.name).Nodup := hΔ.sublist (by grind [allNames])
  cases List.inj_on_of_nodup_map hnd hu hu' rfl
  exact ⟨rfl, rfl⟩

theorem wf_unique_binary {Δ : Signature} {x : String} {τ₁ τ₂ τ₃ τ₁' τ₂' τ₃' : Srt}
    (hΔ : Δ.wf) (hb : ⟨x, τ₁, τ₂, τ₃⟩ ∈ Δ.binary) (hb' : ⟨x, τ₁', τ₂', τ₃'⟩ ∈ Δ.binary) :
    τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ τ₃' = τ₃ := by
  have hnd : (Δ.binary.map Decl.Binary.name).Nodup := hΔ.sublist (by grind [allNames])
  cases List.inj_on_of_nodup_map hnd hb hb' rfl
  exact ⟨rfl, rfl, rfl⟩

theorem wf_unique_ternary {Δ : Signature} {x : String}
    {τ₁ τ₂ τ₃ τ₄ τ₁' τ₂' τ₃' τ₄' : Srt}
    (hΔ : Δ.wf) (ht : ⟨x, τ₁, τ₂, τ₃, τ₄⟩ ∈ Δ.ternary)
    (ht' : ⟨x, τ₁', τ₂', τ₃', τ₄'⟩ ∈ Δ.ternary) :
    τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ τ₃' = τ₃ ∧ τ₄' = τ₄ := by
  have hnd : (Δ.ternary.map Decl.Ternary.name).Nodup := hΔ.sublist (by grind [allNames])
  cases List.inj_on_of_nodup_map hnd ht ht' rfl
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem wf_unique_unaryRel {Δ : Signature} {x : String} {τ τ' : Srt}
    (hΔ : Δ.wf) (hu : ⟨x, τ⟩ ∈ Δ.unaryRel) (hu' : ⟨x, τ'⟩ ∈ Δ.unaryRel) : τ' = τ := by
  have hnd : (Δ.unaryRel.map Decl.UnaryRel.name).Nodup := hΔ.sublist (by grind [allNames])
  cases List.inj_on_of_nodup_map hnd hu hu' rfl
  exact rfl

theorem wf_unique_binaryRel {Δ : Signature} {x : String} {τ₁ τ₂ τ₁' τ₂' : Srt}
    (hΔ : Δ.wf) (hb : ⟨x, τ₁, τ₂⟩ ∈ Δ.binaryRel) (hb' : ⟨x, τ₁', τ₂'⟩ ∈ Δ.binaryRel) :
    τ₁' = τ₁ ∧ τ₂' = τ₂ := by
  have hnd : (Δ.binaryRel.map Decl.BinaryRel.name).Nodup := hΔ.sublist (by grind [allNames])
  cases List.inj_on_of_nodup_map hnd hb hb' rfl
  exact ⟨rfl, rfl⟩

theorem wf_no_const_of_var {Δ : Signature} {x : String} {τ τ' : Srt}
    (hΔ : Δ.wf) (hv : ⟨x, τ⟩ ∈ Δ.vars) : ⟨x, τ'⟩ ∉ Δ.consts := by
  intro hc
  simp only [wf, allNames, List.nodup_append] at hΔ
  exact hΔ.1.1.1.1.1.2.2 x (List.mem_map_of_mem hv) x (List.mem_map_of_mem hc) rfl

theorem wf_no_var_of_const {Δ : Signature} {x : String} {τ τ' : Srt}
    (hΔ : Δ.wf) (hc : ⟨x, τ⟩ ∈ Δ.consts) : ⟨x, τ'⟩ ∉ Δ.vars := by
  intro hv
  exact wf_no_const_of_var hΔ hv hc

theorem wf_no_unaryRel_of_unary {Δ : Signature} {x : String} {τ₁ τ₂ τ' : Srt}
    (hΔ : Δ.wf) (hu : ⟨x, τ₁, τ₂⟩ ∈ Δ.unary) : ⟨x, τ'⟩ ∉ Δ.unaryRel := by
  intro hrel
  simp only [wf, allNames, List.nodup_append] at hΔ
  exact hΔ.1.2.2 x (by simp [List.mem_map_of_mem hu]) x (List.mem_map_of_mem hrel) rfl

theorem wf_no_binaryRel_of_binary {Δ : Signature} {x : String} {τ₁ τ₂ τ₃ τ₁' τ₂' : Srt}
    (hΔ : Δ.wf) (hb : ⟨x, τ₁, τ₂, τ₃⟩ ∈ Δ.binary) : ⟨x, τ₁', τ₂'⟩ ∉ Δ.binaryRel := by
  intro hrel
  simp only [wf, allNames, List.nodup_append] at hΔ
  exact hΔ.2.2 x (by simp [List.mem_map_of_mem hb]) x (List.mem_map_of_mem hrel) rfl

/-! ### Symbol inclusion -/

/-- `Subset` without the variables. -/
structure SymbolSubset (Δ₁ Δ₂ : Signature) : Prop where
  consts : ∀ c ∈ Δ₁.consts, c ∈ Δ₂.consts
  unary  : ∀ u ∈ Δ₁.unary, u ∈ Δ₂.unary
  binary : ∀ b ∈ Δ₁.binary, b ∈ Δ₂.binary
  ternary : ∀ t ∈ Δ₁.ternary, t ∈ Δ₂.ternary
  unaryRel : ∀ u ∈ Δ₁.unaryRel, u ∈ Δ₂.unaryRel
  binaryRel : ∀ b ∈ Δ₁.binaryRel, b ∈ Δ₂.binaryRel

theorem SymbolSubset.refl (Δ : Signature) : Δ.SymbolSubset Δ :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem SymbolSubset.trans {Δ₁ Δ₂ Δ₃ : Signature}
    (h₁₂ : Δ₁.SymbolSubset Δ₂) (h₂₃ : Δ₂.SymbolSubset Δ₃) : Δ₁.SymbolSubset Δ₃ :=
  ⟨fun c hc => h₂₃.consts c (h₁₂.consts c hc),
   fun u hu => h₂₃.unary u (h₁₂.unary u hu),
   fun b hb => h₂₃.binary b (h₁₂.binary b hb),
   fun t ht => h₂₃.ternary t (h₁₂.ternary t ht),
   fun u hu => h₂₃.unaryRel u (h₁₂.unaryRel u hu),
   fun b hb => h₂₃.binaryRel b (h₁₂.binaryRel b hb)⟩

theorem Subset.symbolSubset {Δ Δ' : Signature} (h : Δ.Subset Δ') : Δ.SymbolSubset Δ' :=
  ⟨h.consts, h.unary, h.binary, h.ternary, h.unaryRel, h.binaryRel⟩

theorem SymbolSubset.subset_addConst (Δ : Signature) (c : Decl.Const) :
    Δ.SymbolSubset (Δ.addConst c) :=
  ⟨fun _ hc' => List.mem_cons_of_mem _ hc', fun _ hu => hu, fun _ hb => hb,
   fun _ ht => ht, fun _ hu => hu, fun _ hb => hb⟩

theorem SymbolSubset.declVar {Δ Δ' : Signature} (h : Δ.SymbolSubset Δ') (v : Var) :
    (Δ.declVar v).SymbolSubset Δ' :=
  ⟨fun _ h' => h.consts _ (mem_declVar_consts.mp h').1,
   fun _ h' => h.unary _ (mem_declVar_unary.mp h').1,
   fun _ h' => h.binary _ (mem_declVar_binary.mp h').1,
   fun _ h' => h.ternary _ (mem_declVar_ternary.mp h').1,
   fun _ h' => h.unaryRel _ (mem_declVar_unaryRel.mp h').1,
   fun _ h' => h.binaryRel _ (mem_declVar_binaryRel.mp h').1⟩

/-- `declVars` adds no symbols other than variables. -/
theorem SymbolSubset.declVars {Δ Δ' : Signature} (h : Δ.SymbolSubset Δ') (vs : List Var) :
    (Δ.declVars vs).SymbolSubset Δ' := by
  induction vs generalizing Δ with
  | nil => simpa [declVars] using h
  | cons v vs ih => simpa [declVars] using ih (SymbolSubset.declVar h v)

/-- The symbols of `Δ` are in `Δ'`, so none of them has the name `y'` that
`declVar` removes on the right. -/
theorem SymbolSubset.declVar_fresh {Δ Δ' : Signature} {y y' : String} {τ : Srt}
    (h : Δ.SymbolSubset Δ') (hfresh : y' ∉ Δ'.allNames) :
    (Δ.declVar ⟨y, τ⟩).SymbolSubset (Δ'.declVar ⟨y', τ⟩) := by
  constructor <;> intro s hs <;>
    simp only [Signature.mem_declVar_consts, Signature.mem_declVar_unary,
      Signature.mem_declVar_binary, Signature.mem_declVar_ternary,
      Signature.mem_declVar_unaryRel, Signature.mem_declVar_binaryRel] at hs ⊢
  · exact ⟨h.consts s hs.1, fun hEq =>
      hfresh (hEq ▸ Signature.mem_allNames_of_const (h.consts s hs.1))⟩
  · exact ⟨h.unary s hs.1, fun hEq =>
      hfresh (hEq ▸ Signature.mem_allNames_of_unary (h.unary s hs.1))⟩
  · exact ⟨h.binary s hs.1, fun hEq =>
      hfresh (hEq ▸ Signature.mem_allNames_of_binary (h.binary s hs.1))⟩
  · exact ⟨h.ternary s hs.1, fun hEq =>
      hfresh (hEq ▸ Signature.mem_allNames_of_ternary (h.ternary s hs.1))⟩
  · exact ⟨h.unaryRel s hs.1, fun hEq =>
      hfresh (hEq ▸ Signature.mem_allNames_of_unaryRel (h.unaryRel s hs.1))⟩
  · exact ⟨h.binaryRel s hs.1, fun hEq =>
      hfresh (hEq ▸ Signature.mem_allNames_of_binaryRel (h.binaryRel s hs.1))⟩

end Signature
