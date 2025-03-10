import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Finite

open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

section DegreeSum

variable [Fintype V] [DecidableRel G.Adj] [DecidableEq V]

/-- The degree-sum formula only counting over the vertices that form edges.
See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version. -/
theorem sum_degrees_support_eq_twice_card_edges :
    ∑ v ∈ G.support, G.degree v = 2 * #G.edgeFinset := by
  simp_rw [← sum_degrees_eq_twice_card_edges,
    ← sum_add_sum_compl G.support.toFinset, self_eq_add_right]
  apply sum_eq_zero
  intro v hv
  rw [degree_eq_zero_iff_not_mem_support]
  rwa [mem_compl, Set.mem_toFinset] at hv

end DegreeSum

end SimpleGraph
