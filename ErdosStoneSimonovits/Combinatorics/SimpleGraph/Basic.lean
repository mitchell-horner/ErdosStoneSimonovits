import Mathlib

open Finset Function Set.Notation

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

lemma neighborSet_subset_support (v : V) : G.neighborSet v ⊆ G.support :=
  fun _ hadj ↦ ⟨v, hadj.symm⟩

section FromEdgeSet

variable (s : Set (Sym2 V))

instance [DecidablePred (· ∈ s)] [DecidableEq V] : DecidableRel (fromEdgeSet s).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ s(v, w) ∈ s ∧ v ≠ w

end FromEdgeSet

section IsCompleteBetween

variable {s t : Set V}

/-- The condition that the portion of the simple graph `G` _between_ `s` and `t` is complete, that
is, every vertex in `s` is adjacent to every vertex in `t`, and vice versa. -/
def IsCompleteBetween (G : SimpleGraph V) (s t : Set V) :=
  ∀ ⦃v₁⦄, v₁ ∈ s → ∀ ⦃v₂⦄, v₂ ∈ t → G.Adj v₁ v₂

theorem IsCompleteBetween.disjoint (h : G.IsCompleteBetween s t) : Disjoint s t :=
  Set.disjoint_left.mpr fun v hv₁ hv₂ ↦ (G.loopless v) (h hv₁ hv₂)

theorem isCompleteBetween_comm : G.IsCompleteBetween s t ↔ G.IsCompleteBetween t s where
  mp h _ h₁ _ h₂ := (h h₂ h₁).symm
  mpr h _ h₁ _ h₂ := (h h₂ h₁).symm

alias ⟨IsCompleteBetween.symm, _⟩ := isCompleteBetween_comm

theorem IsCompleteBetween.induce (h : G.IsCompleteBetween s t) (u : Set V) :
    (G.induce u).IsCompleteBetween (u ↓∩ s) (u ↓∩ t) := by
  intro _ hs _ ht
  rw [comap_adj, Embedding.coe_subtype]
  exact h hs ht

end IsCompleteBetween

end SimpleGraph
