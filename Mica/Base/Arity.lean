-- SUMMARY: Intrinsic arities and the argument tuples indexed by them.

/-! # Arity

An `Arity` is the number of arguments of a built-in operation. `Arity.tup`
is the shape of a tuple of that many arguments. The intrinsic registry and
the relational encoder both index their arguments by this type. Therefore it
is below both of them.
-/

/-- The arity of an intrinsic. Add more cases if you need them. -/
inductive Arity
  | zero
  | one
  | two
  | three
  deriving DecidableEq, Repr

/-- The number of arguments of an `Arity`. -/
def Arity.toNat : Arity → Nat
  | .zero => 0
  | .one  => 1
  | .two  => 2
  | .three => 3

/-- The type of a tuple of `n` elements of type `α`. -/
abbrev Arity.tup : Arity → Type → Type
  | .zero, _ => Unit
  | .one,  α => α
  | .two,  α => α × α
  | .three, α => α × α × α

/-- `p` is true of each element of the tuple. -/
def Arity.All {α : Type} (p : α → Prop) : (n : Arity) → Arity.tup n α → Prop
  | .zero, _ => True
  | .one, a => p a
  | .two, (a, b) => p a ∧ p b
  | .three, (a, b, c) => p a ∧ p b ∧ p c

/-- Apply `f` to each element of the tuple. -/
def Arity.map {α β : Type} (f : α → β) : (n : Arity) → Arity.tup n α → Arity.tup n β
  | .zero, _ => ()
  | .one, a => f a
  | .two, (a, b) => (f a, f b)
  | .three, (a, b, c) => (f a, f b, f c)

/-- Make a tuple from a list of the correct length. -/
def Arity.ofList {α : Type} : (n : Arity) → (xs : List α) → xs.length = n.toNat →
    Arity.tup n α
  | .zero, [], _ => ()
  | .zero, _ :: _, h => by simp [Arity.toNat] at h
  | .one, [], h => by simp [Arity.toNat] at h
  | .one, [a], _ => a
  | .one, _ :: _ :: _, h => by simp [Arity.toNat] at h
  | .two, [], h => by simp [Arity.toNat] at h
  | .two, [_], h => by simp [Arity.toNat] at h
  | .two, [a, b], _ => (a, b)
  | .two, _ :: _ :: _ :: _, h => by simp [Arity.toNat] at h
  | .three, [], h => by simp [Arity.toNat] at h
  | .three, [_], h => by simp [Arity.toNat] at h
  | .three, [_, _], h => by simp [Arity.toNat] at h
  | .three, [a, b, c], _ => (a, b, c)
  | .three, _ :: _ :: _ :: _ :: _, h => by simp [Arity.toNat] at h

/-- If `p` is true of each element of the list, then `p` is true of each
    element of the tuple. -/
theorem Arity.ofList_all {α : Type} {p : α → Prop} (n : Arity) (xs : List α)
    (hlen : xs.length = n.toNat) (hxs : ∀ x ∈ xs, p x) : Arity.All p n (Arity.ofList n xs hlen) := by
  cases n <;> simp [Arity.toNat] at hlen
  · subst xs; trivial
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact hxs a (by simp)
  · rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at hlen
    subst rest
    exact ⟨hxs a (by simp), hxs b (by simp)⟩
  · rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at hlen
    subst rest
    exact ⟨hxs a (by simp), hxs b (by simp), hxs c (by simp)⟩

/-- If two lists of the correct length are equal after you map them, then
    the two tuples are also equal after you map them. -/
theorem Arity.map_ofList_eq {α β γ : Type} (f : α → γ) (g : β → γ) (n : Arity)
    (xs : List α) (ys : List β)
    (hlen₁ : xs.length = n.toNat) (hlen₂ : ys.length = n.toNat)
    (hmap : xs.map f = ys.map g) :
    Arity.map f n (Arity.ofList n xs hlen₁) =
      Arity.map g n (Arity.ofList n ys hlen₂) := by
  cases n
  · simp [Arity.toNat] at hlen₁ hlen₂
    subst xs; subst ys; rfl
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by simpa [Arity.toNat] using hlen₁)
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp (by simpa [Arity.toNat] using hlen₂)
    simpa [Arity.map, Arity.ofList] using hmap
  · rcases xs with _ | ⟨a, _ | ⟨b, rest₁⟩⟩ <;>
      rcases ys with _ | ⟨c, _ | ⟨d, rest₂⟩⟩ <;> simp [Arity.toNat] at hlen₁ hlen₂
    subst rest₁; subst rest₂
    simpa [Arity.map, Arity.ofList] using hmap
  · rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest₁⟩⟩⟩ <;>
      rcases ys with _ | ⟨d, _ | ⟨e, _ | ⟨f', rest₂⟩⟩⟩ <;>
      simp [Arity.toNat] at hlen₁ hlen₂
    subst rest₁; subst rest₂
    simpa [Arity.map, Arity.ofList] using hmap
