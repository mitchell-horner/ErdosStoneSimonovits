import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.Basic
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Finite

namespace SimpleGraph

open Finset Fintype

lemma turanGraph_adj {n r v w} :
  (turanGraph n r).Adj v w ↔ v % r ≠ w % r := by rfl

variable {V : Type*} {G : SimpleGraph V} {n : ℕ} {α : Type*} [Fintype α]

/-- A simple graph does not contain `⊤ : SimpleGraph α` iff it has no `card α`-cliques. -/
theorem top_free_iff_cliqueFree :
    (⊤ : SimpleGraph α).Free G ↔ G.CliqueFree (card α) := by
  rw [← not_iff_not, not_free, cliqueFree_iff, not_isEmpty_iff,
    isContained_congr (Iso.completeGraph (Fintype.equivFin α)) Iso.refl]
  refine ⟨fun ⟨f⟩ ↦ ⟨f.toEmbedding, ⟨?_, f.toHom.map_adj⟩⟩, fun ⟨f⟩ ↦ ⟨f.toCopy⟩⟩
  simpa [← f.injective.ne_iff] using G.ne_of_adj

variable [Fintype V] [DecidableRel G.Adj] [Nontrivial α]

lemma isExtremal_top_free_iff_isTuranMaximal :
    G.IsExtremal (⊤ : SimpleGraph α).Free ↔ G.IsTuranMaximal (card α - 1) := by
  simp_rw [IsTuranMaximal, IsExtremal,
    Nat.sub_one_add_one Fintype.card_ne_zero, top_free_iff_cliqueFree]

lemma isExtremal_top_free_turanGraph :
    (turanGraph n (card α - 1)).IsExtremal (⊤ : SimpleGraph α).Free := by
  rw [isExtremal_top_free_iff_isTuranMaximal]
  exact isTuranMaximal_turanGraph (Nat.sub_pos_iff_lt.mpr Fintype.one_lt_card)

/-- The extremal numbers of `⊤` are equal to the number of edges in `turanGraph`.

This is a corollary of **Turán's theorem**. See `SimpleGraph.isTuranMaximal_turanGraph`. -/
theorem extremalNumber_top :
    extremalNumber n (⊤ : SimpleGraph α) = #(turanGraph n (card α - 1)).edgeFinset := by
  conv =>
    enter [1, 1]
    rw [← Fintype.card_fin n]
  symm
  exact card_edgeFinset_of_isExtremal_free isExtremal_top_free_turanGraph

/-- The `turanGraph` is, up to isomorphism, the unique extremal graph forbidding `⊤`.

This is a corollary of **Turán's theorem**.
See `SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`. -/
theorem card_edgeFinset_eq_extremalNumber_top_iff_iso_turanGraph :
    (⊤ : SimpleGraph α).Free G ∧ #G.edgeFinset = extremalNumber (card V) (⊤ : SimpleGraph α)
      ↔ Nonempty (G ≃g turanGraph (card V) (card α - 1)) := by
  rw [← isTuranMaximal_iff_nonempty_iso_turanGraph (Nat.sub_pos_iff_lt.mpr one_lt_card),
    ← isExtremal_top_free_iff_isTuranMaximal, isExtremal_free_iff]
