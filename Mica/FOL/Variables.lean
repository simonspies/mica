-- SUMMARY: Sorts, variables, and signatures for the first-order logic layer.
import Mica.TinyML.RuntimeExpr

-- ---------------------------------------------------------------------------
-- Sorts
-- ---------------------------------------------------------------------------

inductive Srt where
  | int
  | bool
  | value
  | vallist
  deriving DecidableEq, Repr

@[reducible] def Srt.denote : Srt → Type
  | .int => Int
  | .bool => Bool
  | .value => Runtime.Val
  | .vallist => List Runtime.Val

instance : DecidableEq (Srt.denote τ) := by
  cases τ <;> simp [Srt.denote] <;> infer_instance

instance : Inhabited (Srt.denote τ) := by
  cases τ <;> simp [Srt.denote] <;> infer_instance

-- ---------------------------------------------------------------------------
-- Variables and Contexts
-- ---------------------------------------------------------------------------

structure Var where
  name : String
  sort : Srt
  deriving DecidableEq, Repr

abbrev VarCtx := List Var

def VarCtx.disjoint (C : VarCtx) :=
  ∀ x x' t t', ⟨x, t⟩ ∈ C → ⟨x', t'⟩ ∈ C → x = x' → t = t'

-- ---------------------------------------------------------------------------
-- Signature: extends VarCtx with named function symbols
-- ---------------------------------------------------------------------------

namespace FOL

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

end FOL

structure Signature where
  vars   : VarCtx
  consts : List FOL.Const
  unary  : List FOL.Unary
  binary : List FOL.Binary

namespace Signature

def empty : Signature := ⟨[], [], [], []⟩

@[simp] theorem empty_vars    : (empty : Signature).vars   = [] := rfl
@[simp] theorem empty_consts  : (empty : Signature).consts = [] := rfl
@[simp] theorem empty_unary   : (empty : Signature).unary  = [] := rfl
@[simp] theorem empty_binary  : (empty : Signature).binary = [] := rfl

def addVar (Δ : Signature) (v : Var) : Signature := { Δ with vars := v :: Δ.vars }
def addVars (Δ : Signature) (vs : List Var) : Signature := { Δ with vars := vs ++ Δ.vars }

def addConst (Δ : Signature) (c : FOL.Const) : Signature := { Δ with consts := c :: Δ.consts }
def addUnary (Δ : Signature) (u : FOL.Unary) : Signature := { Δ with unary := u :: Δ.unary }
def addBinary (Δ : Signature) (b : FOL.Binary) : Signature := { Δ with binary := b :: Δ.binary }
def remove (Δ : Signature) (x : String) : Signature :=
  { vars := Δ.vars.filter (·.name != x)
    consts := Δ.consts.filter (·.name != x)
    unary := Δ.unary.filter (·.name != x)
    binary := Δ.binary.filter (·.name != x) }

/-- Declare a variable with binder-shadowing semantics. -/
def declVar (Δ : Signature) (v : Var) : Signature := (Δ.remove v.name).addVar v

/-- Declare several variables left-to-right with binder-shadowing semantics. -/
def declVars (Δ : Signature) (vs : List Var) : Signature := vs.foldl declVar Δ

def allNames (Δ : Signature) : List String :=
  Δ.vars.map Var.name ++ Δ.consts.map FOL.Const.name ++
  Δ.unary.map FOL.Unary.name ++ Δ.binary.map FOL.Binary.name

def wf (Δ : Signature) : Prop := Δ.allNames.Nodup

theorem mem_allNames_of_var {Δ : Signature} {v : Var} (h : v ∈ Δ.vars) :
    v.name ∈ Δ.allNames :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨v, h, rfl⟩)))

theorem mem_allNames_of_const {Δ : Signature} {c : FOL.Const} (h : c ∈ Δ.consts) :
    c.name ∈ Δ.allNames :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, h, rfl⟩)))

theorem mem_allNames_of_unary {Δ : Signature} {u : FOL.Unary} (h : u ∈ Δ.unary) :
    u.name ∈ Δ.allNames :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨u, h, rfl⟩))

theorem mem_allNames_of_binary {Δ : Signature} {b : FOL.Binary} (h : b ∈ Δ.binary) :
    b.name ∈ Δ.allNames :=
  List.mem_append_right _ (List.mem_map.mpr ⟨b, h, rfl⟩)

theorem nodup_allNames_addConst {Δ : Signature} {c : FOL.Const}
    (hnd : Δ.allNames.Nodup) (hfresh : c.name ∉ Δ.allNames) :
    (Δ.addConst c).allNames.Nodup := by
  suffices h : (Δ.addConst c).allNames.Perm (c.name :: Δ.allNames) from
    h.nodup_iff.mpr (List.nodup_cons.mpr ⟨hfresh, hnd⟩)
  -- addConst c inserts c.name between vars and consts in allNames
  -- allNames (addConst c Δ) = vs ++ (c :: cs) ++ us ++ bs
  -- c :: allNames Δ           = c :: (vs ++ cs ++ us ++ bs)
  -- These are permutations via comm of the first two segments.
  show (Δ.vars.map Var.name ++ (c.name :: Δ.consts.map FOL.Const.name) ++
    Δ.unary.map FOL.Unary.name ++ Δ.binary.map FOL.Binary.name).Perm
    (c.name :: (Δ.vars.map Var.name ++ Δ.consts.map FOL.Const.name ++
    Δ.unary.map FOL.Unary.name ++ Δ.binary.map FOL.Binary.name))
  simp only [List.append_assoc]
  exact List.perm_middle

theorem allNames_addConst (Δ : Signature) (c : FOL.Const) :
    (Δ.addConst c).allNames = Δ.vars.map Var.name ++ (c.name :: Δ.consts.map FOL.Const.name) ++
    Δ.unary.map FOL.Unary.name ++ Δ.binary.map FOL.Binary.name := by
  simp [allNames, addConst]

@[simp] theorem mem_remove_vars {Δ : Signature} {v : Var} {x : String} :
    v ∈ (Δ.remove x).vars ↔ v ∈ Δ.vars ∧ v.name ≠ x := by
  simp [remove]

@[simp] theorem mem_remove_consts {Δ : Signature} {c : FOL.Const} {x : String} :
    c ∈ (Δ.remove x).consts ↔ c ∈ Δ.consts ∧ c.name ≠ x := by
  simp [remove]

@[simp] theorem mem_remove_unary {Δ : Signature} {u : FOL.Unary} {x : String} :
    u ∈ (Δ.remove x).unary ↔ u ∈ Δ.unary ∧ u.name ≠ x := by
  simp [remove]

@[simp] theorem mem_remove_binary {Δ : Signature} {b : FOL.Binary} {x : String} :
    b ∈ (Δ.remove x).binary ↔ b ∈ Δ.binary ∧ b.name ≠ x := by
  simp [remove]

theorem remove_allNames {Δ : Signature} {n x : String} (h : n ∈ (Δ.remove x).allNames) :
    n ≠ x := by
  simp only [allNames, List.mem_append, List.mem_map] at h
  rcases h with ⟨⟨⟨v, hv, rfl⟩ | ⟨c, hc, rfl⟩⟩ | ⟨u, hu, rfl⟩⟩ | ⟨b, hb, rfl⟩
  · exact (mem_remove_vars.mp hv).2
  · exact (mem_remove_consts.mp hc).2
  · exact (mem_remove_unary.mp hu).2
  · exact (mem_remove_binary.mp hb).2

theorem wf_empty : Signature.empty.wf := by simp [wf, allNames]

theorem wf_addConst {Δ : Signature} {c : FOL.Const}
    (hΔ : Δ.wf) (hfresh : c.name ∉ Δ.allNames) : (Δ.addConst c).wf :=
  nodup_allNames_addConst hΔ hfresh

theorem wf_addVar {Δ : Signature} {v : Var}
    (hΔ : Δ.wf) (hfresh : v.name ∉ Δ.allNames) : (Δ.addVar v).wf := by
  unfold wf at hΔ ⊢
  suffices h : (Δ.addVar v).allNames.Perm (v.name :: Δ.allNames) from
    h.nodup_iff.mpr (List.nodup_cons.mpr ⟨hfresh, hΔ⟩)
  show ((v :: Δ.vars).map Var.name ++ Δ.consts.map FOL.Const.name ++
    Δ.unary.map FOL.Unary.name ++ Δ.binary.map FOL.Binary.name).Perm
    (v.name :: (Δ.vars.map Var.name ++ Δ.consts.map FOL.Const.name ++
    Δ.unary.map FOL.Unary.name ++ Δ.binary.map FOL.Binary.name))
  simp

def ofVars (vars : VarCtx) : Signature := ⟨vars, [], [], []⟩

@[simp] theorem ofVars_vars (vars : VarCtx) : (ofVars vars).vars = vars := rfl

@[simp] theorem ofVars_declVars_consts (vars vs : List Var) :
    ((Signature.ofVars vars).declVars vs).consts = [] := by
  induction vs generalizing vars with
  | nil => rfl
  | cons v vs ih =>
    simpa [Signature.declVars, Signature.declVar, Signature.ofVars, Signature.addVar, Signature.remove]
      using ih (vars := v :: vars.filter (fun w => w.name != v.name))

@[simp] theorem ofVars_declVars_unary (vars vs : List Var) :
    ((Signature.ofVars vars).declVars vs).unary = [] := by
  induction vs generalizing vars with
  | nil => rfl
  | cons v vs ih =>
    simpa [Signature.declVars, Signature.declVar, Signature.ofVars, Signature.addVar, Signature.remove]
      using ih (vars := v :: vars.filter (fun w => w.name != v.name))

@[simp] theorem ofVars_declVars_binary (vars vs : List Var) :
    ((Signature.ofVars vars).declVars vs).binary = [] := by
  induction vs generalizing vars with
  | nil => rfl
  | cons v vs ih =>
    simpa [Signature.declVars, Signature.declVar, Signature.ofVars, Signature.addVar, Signature.remove]
      using ih (vars := v :: vars.filter (fun w => w.name != v.name))

def ofConsts (consts : List FOL.Const) : Signature := ⟨[], consts, [], []⟩

@[simp] theorem ofConsts_consts (consts : List FOL.Const) : (ofConsts consts).consts = consts := rfl

structure Subset (Δ₁ Δ₂ : Signature) : Prop where
  vars   : ∀ x ∈ Δ₁.vars, x ∈ Δ₂.vars
  consts : ∀ c ∈ Δ₁.consts, c ∈ Δ₂.consts
  unary  : ∀ u ∈ Δ₁.unary, u ∈ Δ₂.unary
  binary : ∀ b ∈ Δ₁.binary, b ∈ Δ₂.binary

structure SymbolSubset (Δ₁ Δ₂ : Signature) : Prop where
  consts : ∀ c ∈ Δ₁.consts, c ∈ Δ₂.consts
  unary  : ∀ u ∈ Δ₁.unary, u ∈ Δ₂.unary
  binary : ∀ b ∈ Δ₁.binary, b ∈ Δ₂.binary

theorem Subset.refl (Δ : Signature) : Δ.Subset Δ :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem SymbolSubset.refl (Δ : Signature) : Δ.SymbolSubset Δ :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem SymbolSubset.ofVars (vars : VarCtx) (Δ : Signature) : (Signature.ofVars vars).SymbolSubset Δ :=
  by
    constructor <;> intro x hx <;> simp [Signature.ofVars] at hx

theorem SymbolSubset.trans {Δ₁ Δ₂ Δ₃ : Signature}
    (h₁₂ : Δ₁.SymbolSubset Δ₂) (h₂₃ : Δ₂.SymbolSubset Δ₃) : Δ₁.SymbolSubset Δ₃ :=
  ⟨fun c hc => h₂₃.consts c (h₁₂.consts c hc),
   fun u hu => h₂₃.unary u (h₁₂.unary u hu),
   fun b hb => h₂₃.binary b (h₁₂.binary b hb)⟩

theorem SymbolSubset.subset_addConst (Δ : Signature) (c : FOL.Const) :
    Δ.SymbolSubset (Δ.addConst c) :=
  ⟨fun _ hc' => List.mem_cons_of_mem _ hc', fun _ hu => hu, fun _ hb => hb⟩

theorem SymbolSubset.declVar {Δ Δ' : Signature} (h : Δ.SymbolSubset Δ') (v : Var) :
    (Δ.declVar v).SymbolSubset Δ' := by
  constructor
  · intro c hc
    rcases Signature.mem_remove_consts.mp (by simpa [Signature.declVar, Signature.addVar] using hc) with ⟨hc, _⟩
    exact h.consts c hc
  · intro u hu
    rcases Signature.mem_remove_unary.mp (by simpa [Signature.declVar, Signature.addVar] using hu) with ⟨hu, _⟩
    exact h.unary u hu
  · intro b hb
    rcases Signature.mem_remove_binary.mp (by simpa [Signature.declVar, Signature.addVar] using hb) with ⟨hb, _⟩
    exact h.binary b hb

theorem allNames_subset {Δ Δ' : Signature} (h : Δ.Subset Δ') :
    ∀ n ∈ Δ.allNames, n ∈ Δ'.allNames := by
  intro n hn
  simp only [allNames, List.mem_append, List.mem_map] at hn ⊢
  rcases hn with ⟨⟨⟨v, hv, rfl⟩ | ⟨c, hc, rfl⟩⟩ | ⟨u, hu, rfl⟩⟩ | ⟨b, hb, rfl⟩
  · left; left; left; exact ⟨v, h.vars v hv, rfl⟩
  · left; left; right; exact ⟨c, h.consts c hc, rfl⟩
  · left; right; exact ⟨u, h.unary u hu, rfl⟩
  · right; exact ⟨b, h.binary b hb, rfl⟩

theorem Subset.addVar {Δ Δ' : Signature} (h : Δ.Subset Δ') (v : Var) :
    (Δ.addVar v).Subset (Δ'.addVar v) :=
  ⟨fun x hx => by cases hx with | head => left | tail _ hmem => right; exact h.vars x hmem,
   h.consts, h.unary, h.binary⟩

theorem Subset.addVars {Δ Δ' : Signature} (h : Δ.Subset Δ') (vs : List Var) :
    (Δ.addVars vs).Subset (Δ'.addVars vs) :=
  ⟨fun x hx => by
    cases List.mem_append.mp hx with
    | inl hmem => exact List.mem_append_left _ hmem
    | inr hmem => exact List.mem_append_right _ (h.vars x hmem),
   h.consts, h.unary, h.binary⟩

theorem Subset.subset_addVar (Δ : Signature) (v : Var) :
    Δ.Subset (Δ.addVar v) :=
  ⟨fun _ hx => List.mem_cons_of_mem _ hx, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.subset_addConst (Δ : Signature) (c : FOL.Const) :
    Δ.Subset (Δ.addConst c) :=
  ⟨fun _ h => h, fun _ hc => List.mem_cons_of_mem _ hc, fun _ h => h, fun _ h => h⟩

theorem Subset.subset_addUnary (Δ : Signature) (u : FOL.Unary) :
    Δ.Subset (Δ.addUnary u) :=
  ⟨fun _ h => h, fun _ h => h, fun _ hu => List.mem_cons_of_mem _ hu, fun _ h => h⟩

theorem Subset.subset_addBinary (Δ : Signature) (b : FOL.Binary) :
    Δ.Subset (Δ.addBinary b) :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ hb => List.mem_cons_of_mem _ hb⟩

theorem Subset.subset_addVars (Δ : Signature) (vs : List Var) :
    Δ.Subset (Δ.addVars vs) :=
  ⟨fun _ hx => List.mem_append_right _ hx, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.addVars_cons (Δ : Signature) (v : Var) (vs : List Var) :
    (Δ.addVars (v :: vs)).Subset ((Δ.addVar v).addVars vs) := by
  constructor
  · intro x hx
    change x ∈ (v :: vs) ++ Δ.vars at hx
    change x ∈ vs ++ (v :: Δ.vars)
    simp only [List.mem_cons, List.mem_append, or_assoc] at hx ⊢
    rcases hx with rfl | hx | hx
    · right; left; rfl
    · left; exact hx
    · right; right; exact hx
  · intro c hc; exact hc
  · intro u hu; exact hu
  · intro b hb; exact hb

theorem Subset.addVar_addVars (Δ : Signature) (v : Var) (vs : List Var) :
    ((Δ.addVar v).addVars vs).Subset (Δ.addVars (v :: vs)) := by
  constructor
  · intro x hx
    change x ∈ vs ++ (v :: Δ.vars) at hx
    change x ∈ (v :: vs) ++ Δ.vars
    simp only [List.mem_cons, List.mem_append, or_assoc] at hx ⊢
    rcases hx with hx | rfl | hx
    · right; left; exact hx
    · left; rfl
    · right; right; exact hx
  · intro c hc; exact hc
  · intro u hu; exact hu
  · intro b hb; exact hb

theorem Subset.of_vars_subset_ofVars {vars vars' : VarCtx} (h : vars ⊆ vars') :
    (Signature.ofVars vars).Subset (Signature.ofVars vars') :=
  ⟨h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.trans {Δ₁ Δ₂ Δ₃ : Signature} (h₁₂ : Δ₁.Subset Δ₂) (h₂₃ : Δ₂.Subset Δ₃) :
    Δ₁.Subset Δ₃ :=
  ⟨fun x hx => h₂₃.vars x (h₁₂.vars x hx),
   fun c hc => h₂₃.consts c (h₁₂.consts c hc),
   fun u hu => h₂₃.unary u (h₁₂.unary u hu),
   fun b hb => h₂₃.binary b (h₁₂.binary b hb)⟩

theorem Subset.mono_vars {Δ Δ' : Signature} (h : Δ.Subset Δ') : Δ.vars ⊆ Δ'.vars :=
  h.vars

theorem remove_subset (Δ : Signature) (x : String) : (Δ.remove x).Subset Δ :=
  ⟨fun _ h => (mem_remove_vars.mp h).1,
   fun _ h => (mem_remove_consts.mp h).1,
   fun _ h => (mem_remove_unary.mp h).1,
   fun _ h => (mem_remove_binary.mp h).1⟩

theorem remove_allNames_subset {Δ : Signature} {x n : String} (h : n ∈ (Δ.remove x).allNames) :
    n ∈ Δ.allNames :=
  allNames_subset (remove_subset Δ x) _ h

theorem remove_idempotent (Δ : Signature) (x : String) : (Δ.remove x).remove x = Δ.remove x := by
  cases Δ
  simp [remove, List.filter_filter]

theorem remove_eq_of_not_in {Δ : Signature} {x : String} (h : x ∉ Δ.allNames) :
    Δ.remove x = Δ := by
  cases Δ with
  | mk vars consts unary binary =>
  simp only [allNames, List.mem_append, List.mem_map] at h
  have hvars : List.filter (fun v : Var => v.name != x) vars = vars := by
    apply List.filter_eq_self.2
    intro v hv
    have hx : v.name ≠ x := by
      intro hname
      exact h (Or.inl (Or.inl (Or.inl ⟨v, hv, hname⟩)))
    simp [hx]
  have hconsts : List.filter (fun c : FOL.Const => c.name != x) consts = consts := by
    apply List.filter_eq_self.2
    intro c hc
    have hx : c.name ≠ x := by
      intro hname
      exact h (Or.inl (Or.inl (Or.inr ⟨c, hc, hname⟩)))
    simp [hx]
  have hunary : List.filter (fun u : FOL.Unary => u.name != x) unary = unary := by
    apply List.filter_eq_self.2
    intro u hu
    have hx : u.name ≠ x := by
      intro hname
      exact h (Or.inl (Or.inr ⟨u, hu, hname⟩))
    simp [hx]
  have hbinary : List.filter (fun b : FOL.Binary => b.name != x) binary = binary := by
    apply List.filter_eq_self.2
    intro b hb
    have hx : b.name ≠ x := by
      intro hname
      exact h (Or.inr ⟨b, hb, hname⟩)
    simp [hx]
  simp [remove, hvars, hconsts, hunary, hbinary]

private theorem allNames_remove_sublist (Δ : Signature) (x : String) :
    List.Sublist (Δ.remove x).allNames Δ.allNames := by
  cases Δ with
  | mk vars consts unary binary =>
    simp [remove, allNames]
    apply List.Sublist.append
    · exact (List.filter_sublist (l := vars) (p := fun v : Var => v.name != x)).map Var.name
    · apply List.Sublist.append
      · exact (List.filter_sublist (l := consts) (p := fun c : FOL.Const => c.name != x)).map FOL.Const.name
      · apply List.Sublist.append
        · exact (List.filter_sublist (l := unary) (p := fun u : FOL.Unary => u.name != x)).map FOL.Unary.name
        · exact (List.filter_sublist (l := binary) (p := fun b : FOL.Binary => b.name != x)).map FOL.Binary.name

theorem wf_remove {Δ : Signature} (hΔ : Δ.wf) (x : String) : (Δ.remove x).wf := by
  rw [wf] at hΔ ⊢
  exact hΔ.sublist (allNames_remove_sublist Δ x)

theorem wf_remove_addVar {Δ : Signature} {x : String} {τ : Srt}
    (hΔ : Δ.wf) : ((Δ.remove x).addVar ⟨x, τ⟩).wf := by
  apply wf_addVar (wf_remove hΔ x)
  intro hx
  exact remove_allNames hx rfl

theorem wf_declVar {Δ : Signature} {v : Var} (hΔ : Δ.wf) : (Δ.declVar v).wf := by
  simpa [declVar] using (wf_remove_addVar (Δ := Δ) (x := v.name) (τ := v.sort) hΔ)

theorem wf_declVars {Δ : Signature} {vs : List Var} (hΔ : Δ.wf) : (Δ.declVars vs).wf := by
  induction vs generalizing Δ with
  | nil =>
    simpa [declVars] using hΔ
  | cons v vs ih =>
    simpa [declVars] using ih (wf_declVar (Δ := Δ) (v := v) hΔ)

theorem allNames_remove_addVar_of_not_in {Δ : Signature} {x : String} {τ : Srt}
    (h : x ∉ Δ.allNames) : ((Δ.remove x).addVar ⟨x, τ⟩).allNames = x :: Δ.allNames := by
  rw [remove_eq_of_not_in h]
  simp [allNames, addVar]

private theorem unique_sort_of_nodup_map_name {l : List Var} {x : String} {τ τ' : Srt}
    (hnd : (l.map Var.name).Nodup) (hv : ⟨x, τ⟩ ∈ l) (hv' : ⟨x, τ'⟩ ∈ l) : τ' = τ := by
  induction l with
  | nil => simp at hv
  | cons v vs ih =>
    rw [List.map, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hv with rfl | hmem
    · rcases List.mem_cons.mp hv' with heq | hmem'
      · exact (Var.mk.inj heq).2
      · exact absurd (List.mem_map_of_mem hmem') hnd.1
    · rcases List.mem_cons.mp hv' with rfl | hmem'
      · exact absurd (List.mem_map_of_mem hmem) hnd.1
      · exact ih hnd.2 hmem hmem'

private theorem unique_sort_of_nodup_map_const_name {l : List FOL.Const} {x : String} {τ τ' : Srt}
    (hnd : (l.map FOL.Const.name).Nodup) (hc : ⟨x, τ⟩ ∈ l) (hc' : ⟨x, τ'⟩ ∈ l) : τ' = τ := by
  induction l with
  | nil => simp at hc
  | cons v vs ih =>
    rw [List.map, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hc with rfl | hmem
    · rcases List.mem_cons.mp hc' with heq | hmem'
      · exact (FOL.Const.mk.inj heq).2
      · exact absurd (List.mem_map_of_mem hmem') hnd.1
    · rcases List.mem_cons.mp hc' with rfl | hmem'
      · exact absurd (List.mem_map_of_mem hmem) hnd.1
      · exact ih hnd.2 hmem hmem'

theorem wf_unique_var {Δ : Signature} {x : String} {τ τ' : Srt}
    (hΔ : Δ.wf) (hv : ⟨x, τ⟩ ∈ Δ.vars) (hv' : ⟨x, τ'⟩ ∈ Δ.vars) : τ' = τ :=
  unique_sort_of_nodup_map_name
    (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hΔ).1).1).1
    hv hv'

theorem wf_unique_const {Δ : Signature} {x : String} {τ τ' : Srt}
    (hΔ : Δ.wf) (hc : ⟨x, τ⟩ ∈ Δ.consts) (hc' : ⟨x, τ'⟩ ∈ Δ.consts) : τ' = τ :=
  unique_sort_of_nodup_map_const_name
    (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hΔ).1).1).2.1
    hc hc'

theorem wf_no_const_of_var {Δ : Signature} {x : String} {τ τ' : Srt}
    (hΔ : Δ.wf) (hv : ⟨x, τ⟩ ∈ Δ.vars) : ⟨x, τ'⟩ ∉ Δ.consts := by
  intro hc
  have hnodup : Δ.allNames.Nodup := hΔ
  have hsplit₁ := List.nodup_append.mp hnodup
  have hsplit₂ := List.nodup_append.mp hsplit₁.1
  have hsplit₃ := List.nodup_append.mp hsplit₂.1
  have hdisj := hsplit₃.2.2
  have hxv : x ∈ Δ.vars.map Var.name := List.mem_map.mpr ⟨⟨x, τ⟩, hv, rfl⟩
  have hxc : x ∈ Δ.consts.map FOL.Const.name := List.mem_map.mpr ⟨⟨x, τ'⟩, hc, rfl⟩
  exact hdisj x hxv x hxc rfl

theorem wf_no_var_of_const {Δ : Signature} {x : String} {τ τ' : Srt}
    (hΔ : Δ.wf) (hc : ⟨x, τ⟩ ∈ Δ.consts) : ⟨x, τ'⟩ ∉ Δ.vars := by
  intro hv
  exact wf_no_const_of_var hΔ hv hc

theorem Subset.remove {Δ Δ' : Signature} (h : Δ.Subset Δ') (x : String) :
    (Δ.remove x).Subset (Δ'.remove x) := by
  constructor
  · intro v hv
    rcases mem_remove_vars.mp hv with ⟨hv, hx⟩
    exact mem_remove_vars.mpr ⟨h.vars v hv, hx⟩
  · intro c hc
    rcases mem_remove_consts.mp hc with ⟨hc, hx⟩
    exact mem_remove_consts.mpr ⟨h.consts c hc, hx⟩
  · intro u hu
    rcases mem_remove_unary.mp hu with ⟨hu, hx⟩
    exact mem_remove_unary.mpr ⟨h.unary u hu, hx⟩
  · intro b hb
    rcases mem_remove_binary.mp hb with ⟨hb, hx⟩
    exact mem_remove_binary.mpr ⟨h.binary b hb, hx⟩

theorem Subset.declVar {Δ Δ' : Signature} (h : Δ.Subset Δ') (v : Var) :
    (Δ.declVar v).Subset (Δ'.declVar v) := by
  simpa [declVar] using (Subset.addVar (Subset.remove h v.name) v)

theorem Subset.declVars {Δ Δ' : Signature} (h : Δ.Subset Δ') (vs : List Var) :
    (Δ.declVars vs).Subset (Δ'.declVars vs) := by
  induction vs generalizing Δ Δ' with
  | nil => simpa [declVars] using h
  | cons v vs ih =>
    simpa [declVars] using ih (Subset.declVar h v)

/-- A `Signature.ofVars _ |>.declVars _` signature has no consts/unary/binary, so
    `Subset Δ` reduces to just the vars inclusion. -/
theorem Subset.ofVars {vars vs : List Var} {Δ : Signature}
    (hvars : ((Signature.ofVars vars).declVars vs).vars ⊆ Δ.vars) :
    ((Signature.ofVars vars).declVars vs).Subset Δ :=
  ⟨hvars, fun _ hc => by simp at hc, fun _ hu => by simp at hu, fun _ hb => by simp at hb⟩


end Signature

-- ---------------------------------------------------------------------------
-- Environments
-- ---------------------------------------------------------------------------

/-- An interpretation environment for evaluation.

There is intentionally no separate variable environment. SMT-LIB and Z3 see only a
nullary symbol name like `x`; they do not distinguish, at evaluation time, between
`Term.var τ x` and an uninterpreted constant printed as `x`. We therefore interpret both
through the same `consts` map so the Lean semantics matches the SMT semantics. -/
structure Env where
  consts : (τ : Srt) → String → τ.denote
  unary  : (τ₁ τ₂ : Srt) → String → τ₁.denote → τ₂.denote
  binary : (τ₁ τ₂ τ₃ : Srt) → String → τ₁.denote → τ₂.denote → τ₃.denote

theorem Env.ext {e1 e2 : Env}
    (h1 : e1.consts = e2.consts)
    (h2 : e1.unary = e2.unary) (h3 : e1.binary = e2.binary) : e1 = e2 := by
  cases e1; cases e2; congr

def Env.lookupConst (ρ : Env) (τ : Srt) (x : String) : τ.denote := ρ.consts τ x

def Env.updateConst (ρ : Env) (τ : Srt) (x : String) (v : τ.denote) : Env :=
  { ρ with consts := fun τ' y => if h : τ' = τ ∧ y = x then h.1 ▸ v else ρ.consts τ' y }

def Env.updateUnary (ρ : Env) (τ₁ τ₂ : Srt) (x : String) (f : τ₁.denote → τ₂.denote) : Env :=
  { ρ with unary := fun τ₁' τ₂' y =>
    if h : τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ y = x then h.1 ▸ h.2.1 ▸ f else ρ.unary τ₁' τ₂' y }

def Env.updateBinary (ρ : Env) (τ₁ τ₂ τ₃ : Srt) (x : String)
    (f : τ₁.denote → τ₂.denote → τ₃.denote) : Env :=
  { ρ with binary := fun τ₁' τ₂' τ₃' y =>
    if h : τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ τ₃' = τ₃ ∧ y = x then h.1 ▸ h.2.1 ▸ h.2.2.1 ▸ f
    else ρ.binary τ₁' τ₂' τ₃' y }

def Env.empty : Env :=
  ⟨fun _ _ => default, fun _ _ _ _ => default, fun _ _ _ _ _ => default⟩

instance : Inhabited Env := { default := Env.empty }

@[simp] theorem Env.lookupConst_updateConst_same {ρ : Env} {τ : Srt} {x : String} {v : τ.denote} :
    (ρ.updateConst τ x v).lookupConst τ x = v := by
  simp [Env.updateConst, Env.lookupConst]

@[simp] theorem Env.lookupConst_updateConst_ne {ρ : Env} {τ : Srt} {x y : String} {v : τ.denote} (h : y ≠ x) :
    (Env.updateConst ρ τ x v).lookupConst τ y = ρ.lookupConst τ y := by
  simp [Env.updateConst, Env.lookupConst, h]

theorem Env.lookupConst_updateConst_ne' {ρ : Env} {τ τ' : Srt} {x y : String} {v : τ.denote}
    (h : y ≠ x ∨ τ' ≠ τ) : (ρ.updateConst τ x v).lookupConst τ' y = ρ.lookupConst τ' y := by
  simp only [Env.updateConst, Env.lookupConst]
  split
  · next heq => cases h with
    | inl h => exact absurd heq.2 h
    | inr h => exact absurd heq.1 h
  · rfl

theorem Env.updateConst_unary {ρ : Env} {τ : Srt} {x : String} {v : τ.denote} :
    (ρ.updateConst τ x v).unary = ρ.unary := rfl

theorem Env.updateConst_binary {ρ : Env} {τ : Srt} {x : String} {v : τ.denote} :
    (ρ.updateConst τ x v).binary = ρ.binary := rfl

def Env.agreeOn (Δ : Signature) (ρ ρ' : Env) : Prop :=
  (∀ v ∈ Δ.vars, ρ.consts v.sort v.name = ρ'.consts v.sort v.name) ∧
  (∀ c ∈ Δ.consts, ρ.consts c.sort c.name = ρ'.consts c.sort c.name) ∧
  (∀ u ∈ Δ.unary, ρ.unary u.arg u.ret u.name = ρ'.unary u.arg u.ret u.name) ∧
  (∀ b ∈ Δ.binary, ρ.binary b.arg1 b.arg2 b.ret b.name = ρ'.binary b.arg1 b.arg2 b.ret b.name)

theorem Env.agreeOn_refl : Env.agreeOn Δ ρ ρ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Env.agreeOn_mono {Δ₁ Δ₂ : Signature} (hsub : Δ₁.Subset Δ₂)
    (h : Env.agreeOn Δ₂ ρ ρ') : Env.agreeOn Δ₁ ρ ρ' :=
  ⟨fun x hx => h.1 x (hsub.vars x hx),
   fun c hc => h.2.1 c (hsub.consts c hc),
   fun u hu => h.2.2.1 u (hsub.unary u hu),
   fun b hb => h.2.2.2 b (hsub.binary b hb)⟩

theorem Env.agreeOn_remove {Δ : Signature} {ρ ρ' : Env} {x : String}
    (h : Env.agreeOn Δ ρ ρ') : Env.agreeOn (Δ.remove x) ρ ρ' :=
  Env.agreeOn_mono (Signature.remove_subset Δ x) h

theorem Env.agreeOn_symm {Δ : Signature} {ρ ρ' : Env} (h : Env.agreeOn Δ ρ ρ') : Env.agreeOn Δ ρ' ρ :=
  ⟨fun v hv => (h.1 v hv).symm,
   fun c hc => (h.2.1 c hc).symm,
   fun u hu => (h.2.2.1 u hu).symm,
   fun b hb => (h.2.2.2 b hb).symm⟩

theorem Env.agreeOn_trans {Δ : Signature}
    (h₁₂ : Env.agreeOn Δ ρ₁ ρ₂) (h₂₃ : Env.agreeOn Δ ρ₂ ρ₃) : Env.agreeOn Δ ρ₁ ρ₃ :=
  ⟨fun x hx => (h₁₂.1 x hx).trans (h₂₃.1 x hx),
   fun c hc => (h₁₂.2.1 c hc).trans (h₂₃.2.1 c hc),
   fun u hu => (h₁₂.2.2.1 u hu).trans (h₂₃.2.2.1 u hu),
   fun b hb => (h₁₂.2.2.2 b hb).trans (h₂₃.2.2.2 b hb)⟩

theorem Env.agreeOn_addVars_cons (Δ : Signature) (v : Var) (vs : List Var) (ρ ρ' : Env) :
    Env.agreeOn (Δ.addVars (v :: vs)) ρ ρ' ↔ Env.agreeOn ((Δ.addVar v).addVars vs) ρ ρ' :=
  ⟨Env.agreeOn_mono (Signature.Subset.addVar_addVars Δ v vs), Env.agreeOn_mono (Signature.Subset.addVars_cons Δ v vs)⟩

theorem Env.agreeOn_update {ρ ρ' : Env} {Δ : Signature} {τ : Srt} {x : String} {v : τ.denote} :
    Env.agreeOn Δ ρ ρ' →
    Env.agreeOn (Δ.addVar ⟨x, τ⟩) (ρ.updateConst τ x v) (ρ'.updateConst τ x v) :=
  fun hagree =>
  ⟨fun w hw => by
    cases hw with
    | head => simp [Env.updateConst]
    | tail _ hw =>
      by_cases hn : w.name = x <;> by_cases ht : w.sort = τ
      · cases w; simp only at hn ht; subst hn ht
        simp [Env.updateConst]
      · simp [Env.updateConst, ht, hagree.1 w hw]
      · simp [Env.updateConst, hn, hagree.1 w hw]
      · simp [Env.updateConst, hn, hagree.1 w hw],
   fun c hc => by
     by_cases hn : c.name = x <;> by_cases ht : c.sort = τ
     · cases c; simp only at hn ht; subst hn ht
       simp [Env.updateConst]
     · simp [Env.updateConst, ht, hagree.2.1 c hc]
     · simp [Env.updateConst, hn, hagree.2.1 c hc]
     · simp [Env.updateConst, hn, hagree.2.1 c hc],
   fun u hu => by rw [Env.updateConst_unary]; exact hagree.2.2.1 u hu,
   fun b hb => by rw [Env.updateConst_binary]; exact hagree.2.2.2 b hb⟩

theorem Env.agreeOn_declVar {ρ ρ' : Env} {Δ : Signature} {τ : Srt} {x : String} {v : τ.denote} :
    Env.agreeOn Δ ρ ρ' →
    Env.agreeOn (Δ.declVar ⟨x, τ⟩) (ρ.updateConst τ x v) (ρ'.updateConst τ x v) := by
  intro hagree
  simpa [Signature.declVar] using (Env.agreeOn_update (Env.agreeOn_remove hagree))

theorem Env.agreeOn_update_fresh_const {ρ : Env} {c : FOL.Const} {u : c.sort.denote}
    {Δ : Signature} (hfresh : c.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateConst c.sort c.name u) := by
  constructor
  · intro w hw
    have hne : w.name ≠ c.name := by
      intro heq
      apply hfresh
      rw [← heq]
      exact Signature.mem_allNames_of_var hw
    exact (Env.lookupConst_updateConst_ne' (Or.inl hne)).symm
  · constructor
    · intro c' hc'
      have hne : c'.name ≠ c.name := by
        intro heq
        apply hfresh
        rw [← heq]
        exact Signature.mem_allNames_of_const hc'
      exact (Env.lookupConst_updateConst_ne' (Or.inl hne)).symm
    · constructor
      · intro u' hu'
        rw [Env.updateConst_unary]
      · intro b' hb'
        rw [Env.updateConst_binary]

/-- Double update with the same variable - second update wins. -/
@[simp] theorem Env.updateConst_updateConst_same {ρ : Env} {τ : Srt} {x : String} {v w : τ.denote} :
    (ρ.updateConst τ x v).updateConst τ x w = ρ.updateConst τ x w := by
  apply Env.ext
  · funext τ' y
    simp only [Env.updateConst]
    split
    · simp
    · simp
  all_goals rfl

/-- Updates to different variables commute. -/
theorem Env.updateConst_comm {ρ : Env} {τ : Srt} {x y : String} {v w : τ.denote}
    (h : x ≠ y) : (ρ.updateConst τ x v).updateConst τ y w = (ρ.updateConst τ y w).updateConst τ x v := by
  apply Env.ext
  · funext τ' z
    simp only [Env.updateConst]
    split <;> split <;> simp_all
    · next h1 h2 => exact absurd (h2.2 ▸ h1.2) h
  all_goals rfl
