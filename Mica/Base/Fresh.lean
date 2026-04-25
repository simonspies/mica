-- SUMMARY: Generic fresh-name generation utilities and their injectivity and freshness proofs.
-- Base/Fresh.lean — Generic fresh element generation from an injective function
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.IntervalCases

/-- Helper function to search for a fresh element.
    `n` is the fuel (decreases), `m` is the current index to try.
    Returns `some (f m)` if `f m ∉ xs`, otherwise recurses with `n-1, m+1`. -/
private def freshAux {X : Type} [DecidableEq X] (f : Nat → X) (xs : List X) : Nat → Nat → Option X
  | 0, m => if f m ∈ xs then none else some (f m)
  | n + 1, m => if f m ∈ xs then freshAux f xs n (m + 1) else some (f m)

/-- Generate a fresh element not in `xs` using injective function `f`.
    Tries `f 0, f 1, ...` up to `f xs.length`.
    Returns `f 0` if all candidates are in `xs` (shouldn't happen if `f` is injective). -/
def fresh {X : Type} [DecidableEq X] (f : Nat → X) (xs : List X) : X :=
  match freshAux f xs xs.length 0 with
  | some x => x
  | none => f 0

@[simp]
theorem fresh_nil {X : Type} [DecidableEq X] (f : Nat → X) : fresh f [] = f 0 := by
  simp [fresh, freshAux]

-- ============================================================
-- Helper lemmas about nodup lists
-- ============================================================

private theorem nodup_sublist_length_le {X : Type} [DecidableEq X] (xs ys : List X)
    (hnodup : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  have h := hnodup.subperm hsub
  exact h.length_le

-- ============================================================
-- Properties and proof
-- ============================================================

private def candidates {X : Type} (f : Nat → X) (n : Nat) : List X :=
  List.range (n + 1) |>.map f

private theorem freshAux_none_imp {X : Type} [DecidableEq X] (f : Nat → X) (xs : List X) (n m : Nat) :
    freshAux f xs n m = none → ∀ i, m ≤ i ∧ i ≤ m + n → f i ∈ xs := by
  induction n generalizing m with
  | zero =>
    intro hnone i ⟨hle, hge⟩
    have : i = m := by omega
    rw [this]
    simp only [freshAux] at hnone
    split at hnone
    · assumption
    · contradiction
  | succ n ih =>
    intro hnone i ⟨hle, hge⟩
    simp only [freshAux] at hnone
    split at hnone
    · rename_i hmem
      by_cases h : i = m
      · rw [h]; exact hmem
      · have : m + 1 ≤ i ∧ i ≤ (m + 1) + n := by omega
        exact ih (m := m + 1) hnone i this
    · contradiction

private theorem freshAux_some_not_mem {X : Type} [DecidableEq X] (f : Nat → X) (xs : List X) (n m : Nat) (x : X) :
    freshAux f xs n m = some x → x ∉ xs := by
  induction n generalizing m with
  | zero =>
    intro hsome
    simp only [freshAux] at hsome
    split at hsome
    · contradiction
    · rename_i hnotin
      cases hsome
      exact hnotin
  | succ n ih =>
    intro hsome
    simp only [freshAux] at hsome
    split at hsome
    · exact ih (m := m + 1) hsome
    · rename_i hnotin
      cases hsome
      exact hnotin

private theorem candidates_nodup {X : Type} (f : Nat → X) (n : Nat) (hf : Function.Injective f) :
    (candidates f n).Nodup := by
  unfold candidates
  exact List.Nodup.map hf List.nodup_range

theorem fresh_not_mem {X : Type} [DecidableEq X] (f : Nat → X) (xs : List X) (hf : Function.Injective f) :
    fresh f xs ∉ xs := by
  unfold fresh
  split
  · -- Case: freshAux returned some x
    rename_i x heq
    exact freshAux_some_not_mem f xs xs.length 0 x heq
  · -- Case: freshAux returned none (impossible by pigeonhole)
    rename_i heq
    have hall : ∀ i, 0 ≤ i ∧ i ≤ xs.length → f i ∈ xs := by
      intro i ⟨_, hi⟩
      exact freshAux_none_imp f xs xs.length 0 heq i ⟨by omega, by omega⟩
    have hsub : ∀ x ∈ candidates f xs.length, x ∈ xs := by
      intro x hx
      simp [candidates, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact hall i ⟨by omega, by omega⟩
    have hnodup : (candidates f xs.length).Nodup := candidates_nodup f xs.length hf
    have hlen : (candidates f xs.length).length = xs.length + 1 := by
      simp [candidates]
    have : (candidates f xs.length).length ≤ xs.length :=
      nodup_sublist_length_le (candidates f xs.length) xs hnodup hsub
    omega

-- ============================================================
-- Common Instantiations
-- ============================================================
def addPrimes (base : String) (n : Nat) : String :=
  base ++ String.ofList (List.replicate n '\'')

theorem addPrimes_injective (base : String) :
    Function.Injective (addPrimes base) := by
  intro n m heq; unfold addPrimes at heq
  have h := congrArg String.length heq; simp [String.length_append] at h; omega

private def alwaysAddNumbers (base: String) (n : Nat) : String :=
  base ++ String.ofList ((Nat.digits 10 n).reverse.map Nat.digitChar)

private theorem digitChar_inj_lt {n m : Nat} (hn : n < 10) (hm : m < 10)
    (h : Nat.digitChar n = Nat.digitChar m) : n = m := by
  interval_cases n <;> interval_cases m <;> simp_all [Nat.digitChar]

private theorem map_digitChar_inj {l m : List Nat}
    (hl : ∀ x ∈ l, x < 10) (hm : ∀ x ∈ m, x < 10)
    (h : l.map Nat.digitChar = m.map Nat.digitChar) : l = m := by
  induction l generalizing m with
  | nil => cases m with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a l ih =>
    cases m with
    | nil => simp at h
    | cons b m =>
      obtain ⟨hab, htl⟩ := List.cons.inj h
      congr 1
      · exact digitChar_inj_lt (hl a List.mem_cons_self)
                                (hm b List.mem_cons_self) hab
      · exact ih (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
                 (fun x hx => hm x (List.mem_cons.mpr (Or.inr hx)))
                 htl

private theorem append_left_cancel_str {base s t : String}
    (h : base ++ s = base ++ t) : s = t := by
  have h' := congrArg String.toList h
  simp only [String.toList_append] at h'
  exact String.ext (List.append_cancel_left h')

private theorem alwaysAddNumbers_injective (base: String) :
    Function.Injective (alwaysAddNumbers base) := by
  intro n m heq
  simp only [alwaysAddNumbers] at heq
  have hstr := append_left_cancel_str heq
  have hlist := String.ofList_injective hstr
  have hrev : (Nat.digits 10 n).reverse = (Nat.digits 10 m).reverse :=
    map_digitChar_inj
      (fun x hx => Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hx))
      (fun x hx => Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hx))
      hlist
  exact Nat.digits_inj_iff.mp (List.reverse_inj.mp hrev)

private def exceptZero {X : Type} (base: X) (f : Nat → X) (n: Nat) :=
  match n with
  | .zero => base
  | .succ _ => f n

def addNumbers  (base: String) : Nat → String :=
  exceptZero base (alwaysAddNumbers base)

private theorem ofList_map_digitChar_ne_empty {n : Nat} (hn : n ≠ 0) :
    String.ofList ((Nat.digits 10 n).reverse.map Nat.digitChar) ≠ "" := by
  simp only [ne_eq, String.ofList_eq_empty_iff, List.map_eq_nil_iff, List.reverse_eq_nil_iff,
             Nat.digits_ne_nil_iff_ne_zero]
  exact hn

theorem addNumbers_injective (base: String) :
    Function.Injective (addNumbers base) := by
  intro n m heq
  cases n with
  | zero =>
    cases m with
    | zero => rfl
    | succ m =>
      simp only [addNumbers, exceptZero, alwaysAddNumbers] at heq
      have h' := congrArg String.toList heq
      simp only [String.toList_append, String.toList_ofList] at h'
      have hnil : (Nat.digits 10 m.succ).reverse.map Nat.digitChar = [] :=
        List.append_cancel_left (h'.symm.trans (List.append_nil _).symm)
      exact absurd (String.ofList_nil ▸ congrArg String.ofList hnil)
        (ofList_map_digitChar_ne_empty m.succ_ne_zero)
  | succ n =>
    cases m with
    | zero =>
      simp only [addNumbers, exceptZero, alwaysAddNumbers] at heq
      have h' := congrArg String.toList heq
      simp only [String.toList_append, String.toList_ofList] at h'
      have hnil : (Nat.digits 10 n.succ).reverse.map Nat.digitChar = [] :=
        List.append_cancel_left (h'.trans (List.append_nil _).symm)
      exact absurd (String.ofList_nil ▸ congrArg String.ofList hnil)
        (ofList_map_digitChar_ne_empty n.succ_ne_zero)
    | succ m =>
      exact alwaysAddNumbers_injective base heq
