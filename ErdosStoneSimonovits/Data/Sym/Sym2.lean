import Mathlib

open Finset Function Sym

namespace Sym2

variable {α : Type*}

section ToMultiset

/-- Map an unordered pair to an unordered list. -/
def toMultiset {α : Type*} (z : Sym2 α) : Multiset α := by
  refine Sym2.lift ?_ z
  use Multiset.ofList [·, ·]
  simp [List.Perm.swap]

/-- Mapping an unordered pair to an unordered list produces a multiset of size `2`. -/
lemma card_toMultiset {α : Type*} (z : Sym2 α) : z.toMultiset.card = 2 := by
  induction z
  simp [Sym2.toMultiset]

/-- The members of an unordered pair are members of the corresponding unordered list. -/
theorem mem_toMultiset {α : Type*} {x : α} {z : Sym2 α} :
    x ∈ z ↔ x ∈ (z.toMultiset : Multiset α) := by
  induction z
  simp [Sym2.toMultiset]

end ToMultiset

section ToFinset

/-- Map an unordered pair to a finite set. -/
abbrev toFinset [DecidableEq α] (z : Sym2 α) : Finset α :=
  (z.toMultiset : Multiset α).toFinset

/-- The members of an unordered pair are members of the corresponding finite set. -/
theorem mem_toFinset [DecidableEq α] {x : α} {z : Sym2 α} : x ∈ z ↔ x ∈ z.toFinset := by
  rw [Sym2.mem_toMultiset, Multiset.mem_toFinset]

lemma toFinset_mk_eq [DecidableEq α] {x y : α} : s(x, y).toFinset = {x, y} := by
  ext; simp [← Sym2.mem_toFinset, ← Sym2.mem_iff, Sym2.mem_toMultiset]

/-- The size of the finite set corresponding to an unordered pair on the diagonal is `1`. -/
theorem card_toFinset_of_isDiag [DecidableEq α] (z : Sym2 α) (h : z.IsDiag) :
    #(z : Sym2 α).toFinset = 1 := by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

/-- The size of the finite set corresponding to an unordered pair off the diagonal is `2`. -/
theorem card_toFinset_of_not_isDiag [DecidableEq α] (z : Sym2 α) (h : ¬z.IsDiag) :
    #(z : Sym2 α).toFinset = 2 := by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

end ToFinset

end Sym2
