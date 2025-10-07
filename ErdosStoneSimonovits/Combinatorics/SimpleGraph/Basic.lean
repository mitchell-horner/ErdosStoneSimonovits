import Mathlib

open Finset Function

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

def IsCompleteBetween (G : SimpleGraph V) (s t : Set V) :=
  ∀ ⦃v₁⦄, v₁ ∈ s → ∀ ⦃v₂⦄, v₂ ∈ t → G.Adj v₁ v₂

theorem IsCompleteBetween.disjoint
    (h : G.IsCompleteBetween s t) : Disjoint s t :=
  Set.disjoint_left.mpr fun v hv₁ hv₂ ↦ (G.loopless v) (h hv₁ hv₂)

end IsCompleteBetween

end SimpleGraph
