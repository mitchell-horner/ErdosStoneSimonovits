import Mathlib

open Finset Function

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

lemma neighborSet_subset_support (v : V) : G.neighborSet v ⊆ G.support :=
  fun _ hadj ↦ ⟨v, hadj.symm⟩

end SimpleGraph
