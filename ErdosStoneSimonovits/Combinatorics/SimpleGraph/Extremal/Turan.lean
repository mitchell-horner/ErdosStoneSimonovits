import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.Basic
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Finite

namespace SimpleGraph

open Finset Fintype

variable {V : Type*} (G : SimpleGraph V)

/-- A simple graph does not contain `⊤ : SimpleGraph (Fin n)` if and only if it
has no `n`-cliques. -/
theorem completeGraph_free_iff_cliqueFree {n : ℕ} :
    (⊤ : SimpleGraph (Fin n)).Free G ↔ G.CliqueFree n := by
  rw [← not_iff_not, not_free, cliqueFree_iff, not_isEmpty_iff]
  refine ⟨fun ⟨f⟩ ↦ ⟨⟨f, f.injective⟩, ⟨?_, f.toHom.map_adj⟩⟩, fun ⟨f⟩ ↦ ⟨f, f.injective⟩⟩
  simpa [← f.injective.ne_iff] using G.ne_of_adj

variable [Fintype V] [DecidableRel G.Adj]

lemma isTuranMaximal_iff_isExtremal_completeGraph_free {r} :
    G.IsTuranMaximal r ↔ G.IsExtremal (⊤ : SimpleGraph (Fin (r+1))).Free := by
  simp_rw [IsTuranMaximal, IsExtremal, completeGraph_free_iff_cliqueFree]

/-- The extremal numbers of `⊤` are equal to the number of edges in `turanGraph`.

This is a corollary of **Turán's theorem**. See `SimpleGraph.isTuranMaximal_turanGraph`. -/
theorem extremalNumber_completeGraph
    (β α : Type*) [Fintype β] [DecidableEq β] [Fintype α] [Nontrivial α] :
    extremalNumber β (⊤ : SimpleGraph α) = #(turanGraph (card β) (card α-1)).edgeFinset := by
  have h : (turanGraph (card β) (card α-1)).IsTuranMaximal (card α-1) :=
    isTuranMaximal_turanGraph (Nat.sub_pos_iff_lt.mpr one_lt_card)
  have e : (⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph (Fin (card α-1+1))) :=
    Iso.completeGraph <| equivFinOfCardEq (Nat.sub_one_add_one card_ne_zero).symm
  simp_rw [isTuranMaximal_iff_isExtremal_completeGraph_free, isExtremal_free_iff,
    ← extremalNumber_congr (equivFin β) e] at h
  exact h.2.symm

variable [DecidableEq V]

/-- The `turanGraph` is, up to isomorphism, the unique extremal graph forbidding `completeGraph`.

This is **Turán's theorem**. See `SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`. -/
theorem card_edgeFinset_eq_extremalNumber_completeGraph_iff_iso_turanGraph
    (α : Type*) [Fintype α] [Nontrivial α] :
    (⊤ : SimpleGraph α).Free G ∧ #G.edgeFinset = extremalNumber V (⊤ : SimpleGraph α)
      ↔ Nonempty (G ≃g turanGraph (card V) (card α-1)) := by
  have e : (⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph (Fin (card α-1+1))) :=
    Iso.completeGraph <| equivFinOfCardEq (Nat.sub_one_add_one card_ne_zero).symm
  simp_rw [← isTuranMaximal_iff_nonempty_iso_turanGraph (Nat.sub_pos_iff_lt.mpr one_lt_card),
    isTuranMaximal_iff_isExtremal_completeGraph_free, isExtremal_free_iff,
    ← free_congr e.symm, extremalNumber_congr (Equiv.refl V) e]
