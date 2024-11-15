import Mathlib

import ErdosStoneSimonovits.SpecialGraphs

namespace SimpleGraph

/-- The extremal numbers of the `completeGraph α` are equal to the number of
edges in the corresponding `turanGraph`.

This is a corollary of **Turán's theorem**.
See `isTuranMaximal_turanGraph`. -/
theorem extremalNumber_completeGraph
    (β α : Type*) [Fintype β] [DecidableEq β] [Fintype α] [Nontrivial α] :
    extremalNumber β (completeGraph α) =
      (turanGraph (Fintype.card β) (Fintype.card α-1)).edgeFinset.card := by
  let n := Fintype.card β
  let r := Fintype.card α-1
  have hr_pos : 0 < r := by
    rw [Nat.sub_pos_iff_lt]
    exact Fintype.one_lt_card
  have f : completeGraph α ≃g completeGraph (Fin (r+1)) := by
    refine Iso.completeGraph (Fintype.equivFinOfCardEq ?_)
    rw [Nat.sub_one_add_one]
    exact Fintype.card_ne_zero
  suffices h: extremalNumber (Fin n) (completeGraph (Fin (r+1)))
      = (turanGraph n r).edgeFinset.card by
    simp_rw [←h, completeGraph_eq_top]
    exact extremalNumber_eq_of_iso f (Fintype.equivFin β)
  have hT : (turanGraph n r).IsTuranMaximal r :=
    isTuranMaximal_turanGraph hr_pos
  simp_rw [IsTuranMaximal,
    ←not_isIsoSubgraph_completeGraph_iff_cliqueFree] at hT
  symm; rw [card_edgeFinset_eq_extremalNumber_iff hT.1]
  exact hT.2

/-- The `turanGraph` is, up to isomorphism, the unique extremal graph
forbidding the `completeGraph α`.

This is **Turán's theorem**.
See `isTuranMaximal_iff_nonempty_iso_turanGraph`. -/
theorem card_edgeFinset_eq_extremalNumber_completeGraph_iff_iso_turanGraph
    {β: Type*} [Fintype β] (G : SimpleGraph β) [DecidableRel G.Adj]
    (α : Type*) [Fintype α] [Nontrivial α] :
    ¬(completeGraph α).IsIsoSubgraph G ∧
        G.edgeFinset.card = extremalNumber β (completeGraph α)
      ↔ Nonempty (G ≃g turanGraph (Fintype.card β) (Fintype.card α-1)) := by
  let n := Fintype.card β
  let r := Fintype.card α-1
  have hr_pos : 0 < r := by
    rw [Nat.sub_pos_iff_lt]
    exact Fintype.one_lt_card
  have f : completeGraph α ≃g completeGraph (Fin (r+1)) := by
    refine Iso.completeGraph (Fintype.equivFinOfCardEq ?_)
    rw [Nat.sub_one_add_one]
    exact Fintype.card_ne_zero
  simp_rw [←isTuranMaximal_iff_nonempty_iso_turanGraph hr_pos,
    IsTuranMaximal, ←not_isIsoSubgraph_completeGraph_iff_cliqueFree,
    ←isIsoSubgraph_iff_of_iso f, and_congr_right_iff]
  intro h_free
  simp_rw [card_edgeFinset_eq_extremalNumber_iff h_free]
