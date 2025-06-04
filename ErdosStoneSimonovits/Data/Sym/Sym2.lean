import Mathlib

open Finset Function Sym

namespace Sym2

variable {α : Type*}

section ToMultiset

/-- Map an unordered pair to an unordered list. -/
def toMultiset {α : Type*} (z : Sym2 α) : Multiset α := by
  refine Sym2.lift ?_ z
  use (Multiset.ofList [·, ·])
  simp [List.Perm.swap]

/-- Mapping an unordered pair to an unordered list produces a multiset of size `2`. -/
lemma card_toMultiset {α : Type*} (z : Sym2 α) : z.toMultiset.card = 2 := by
  induction z
  simp [Sym2.toMultiset]

/-- The members of an unordered pair are members of the corresponding unordered list. -/
@[simp]
theorem mem_toMultiset {α : Type*} {x : α} {z : Sym2 α} :
    x ∈ (z.toMultiset : Multiset α) ↔ x ∈ z := by
  induction z
  simp [Sym2.toMultiset]

end ToMultiset

section ToFinset

variable [DecidableEq α]

/-- Map an unordered pair to a finite set. -/
def toFinset (z : Sym2 α) : Finset α := (z.toMultiset : Multiset α).toFinset

/-- The members of an unordered pair are members of the corresponding finite set. -/
@[simp]
theorem mem_toFinset {x : α} {z : Sym2 α} : x ∈ z.toFinset ↔ x ∈ z := by
  rw [← Sym2.mem_toMultiset, Sym2.toFinset, Multiset.mem_toFinset]

lemma toFinset_mk_eq {x y : α} : s(x, y).toFinset = {x, y} := by
  ext; simp [←Sym2.mem_toFinset, ←Sym2.mem_iff, Sym2.mem_toMultiset]

/-- Mapping an unordered pair on the diagonal to a finite set produces a finset of size `1`. -/
theorem card_toFinset_of_isDiag (z : Sym2 α) (h : z.IsDiag) : #(z : Sym2 α).toFinset = 1 := by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

/-- Mapping an unordered pair off the diagonal to a finite set produces a finset of size `2`. -/
theorem card_toFinset_of_not_isDiag (z : Sym2 α) (h : ¬z.IsDiag) : #(z : Sym2 α).toFinset = 2 := by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

/-- Mapping an unordered pair to a finite set produces a finset of size `1` if the pair is on the
diagonal, else of size `2` if the pair is off the diagonal. -/
theorem card_toFinset (z : Sym2 α) : #(z : Sym2 α).toFinset = if z.IsDiag then 1 else 2 := by
  by_cases h : z.IsDiag
  · simp [card_toFinset_of_isDiag z h, h]
  · simp [card_toFinset_of_not_isDiag z h, h]

end ToFinset

end Sym2
