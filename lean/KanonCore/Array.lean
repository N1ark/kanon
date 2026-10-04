/-!
# Arrays, as the generated models use them

A Kanon `t array` is an immutable array, which Lean models by `Array t`
(a literal is `#[a, b]`, `array_of_list` is `List.toArray`, and `array_to_list`
`Array.toList`). Indices are integers, as in Kanon: `array_length`, `array_get`
and `array_set` are `arrayLength`, `arrayGet` and `arraySet`.

An index out of bounds is a precondition that Kanon does not check: the OCaml
operations raise `Invalid_argument`, and these ones are total, so that they are
defined where OCaml's are not: `arrayGet` is `default` there, and `arraySet` is
the identity. Nothing is proved about these values, which must not be relied on.
-/

namespace Kanon

/-- `array_length`: the number of elements. -/
def arrayLength {α : Type} (a : Array α) : Int := a.size

/-- `array_get`: the element at an index in bounds, `default` out of bounds. -/
def arrayGet {α : Type} [Inhabited α] (a : Array α) (i : Int) : α :=
  if 0 ≤ i then a.getD i.toNat default else default

/-- `array_set`: the array with the element at an index in bounds replaced, a
copy; `a` out of bounds. -/
def arraySet {α : Type} (a : Array α) (i : Int) (v : α) : Array α :=
  if 0 ≤ i then a.setIfInBounds i.toNat v else a

variable {α : Type}

theorem arrayLength_nonneg (a : Array α) : 0 ≤ arrayLength a := by
  simp [arrayLength]

theorem arrayLength_arraySet (a : Array α) (i : Int) (v : α) :
    arrayLength (arraySet a i v) = arrayLength a := by
  unfold arrayLength arraySet
  split <;> simp

theorem arrayLength_toArray (l : List α) : arrayLength l.toArray = l.length := by
  simp [arrayLength]

theorem arrayLength_empty : arrayLength (#[] : Array α) = 0 := by
  simp [arrayLength]

/-- Reading the element that was set. -/
theorem arrayGet_arraySet_same [Inhabited α] (a : Array α) (i : Int) (v : α)
    (h : 0 ≤ i ∧ i < arrayLength a) : arrayGet (arraySet a i v) i = v := by
  obtain ⟨h0, h1⟩ := h
  have hi : i.toNat < a.size := by simp [arrayLength] at h1; omega
  simp [arrayGet, arraySet, h0, hi]

/-- Reading another element. -/
theorem arrayGet_arraySet_ne [Inhabited α] (a : Array α) (i j : Int) (v : α) (h : i ≠ j) :
    arrayGet (arraySet a i v) j = arrayGet a j := by
  unfold arrayGet arraySet
  by_cases hi : 0 ≤ i <;> by_cases hj : 0 ≤ j <;> simp [hi, hj]
  have : i.toNat ≠ j.toNat := by omega
  simp [this]

/-- Setting the element that is there changes nothing. -/
theorem arraySet_arrayGet [Inhabited α] (a : Array α) (i : Int) (h : 0 ≤ i ∧ i < arrayLength a) :
    arraySet a i (arrayGet a i) = a := by
  obtain ⟨h0, h1⟩ := h
  have hi : i.toNat < a.size := by simp [arrayLength] at h1; omega
  have : a.getD i.toNat default = a[i.toNat] := by simp [hi]
  simp only [arrayGet, arraySet, h0, ite_true, this]
  ext j
  · simp
  · grind

/-- Setting an element twice keeps the last. -/
theorem arraySet_arraySet_same (a : Array α) (i : Int) (v w : α) :
    arraySet (arraySet a i v) i w = arraySet a i w := by
  unfold arraySet
  split <;> simp [Array.setIfInBounds_setIfInBounds]

/-- `array_to_list` and `array_of_list` are inverse. -/
theorem toList_toArray (l : List α) : l.toArray.toList = l := by simp

theorem toArray_toList (a : Array α) : a.toList.toArray = a := by simp

/-- The element of a list that is read: `arrayGet` of the array of a list. -/
theorem arrayGet_toArray [Inhabited α] (l : List α) (i : Int) (h : 0 ≤ i ∧ i < l.length) :
    arrayGet l.toArray i = l[i.toNat]'(by omega) := by
  obtain ⟨h0, h1⟩ := h
  have : i.toNat < l.length := by omega
  simp [arrayGet, h0, this]

end Kanon
