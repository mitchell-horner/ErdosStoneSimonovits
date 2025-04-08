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

end SimpleGraph
