import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Copy

open Finset Fintype Function

namespace SimpleGraph

variable {α β : Type*} {G : SimpleGraph α}

section Clique

/-- The vertices in a copy of `⊤` are a clique. -/
theorem isClique_image_copy_top (f : Copy (⊤ : SimpleGraph β) G) :
    G.IsClique (f '' Set.univ) := by
  intro _ ⟨_, _, h⟩ _ ⟨_, _, h'⟩ heq
  rw [← h, show f _ = f.topEmbedding _ by rfl, ← h', show f _ = f.topEmbedding _ by rfl] at heq ⊢
  rwa [← f.topEmbedding.coe_toEmbedding, (f.topEmbedding.apply_eq_iff_eq _ _).ne,
    ← top_adj, ← f.topEmbedding.map_adj_iff] at heq

end Clique

section NClique

/-- The vertices in a copy of `⊤ : SimpleGraph β` are a `card β`-clique. -/
theorem isNClique_map_copy_top [Fintype β] (f : Copy (⊤ : SimpleGraph β) G) :
    G.IsNClique (card β) (univ.map f.toEmbedding) := by
  rw [isNClique_iff, card_map, card_univ, coe_map, coe_univ]
  exact ⟨isClique_image_copy_top f, rfl⟩

end NClique

section CliqueFree

/-- A simple graph has no `card β`-cliques iff it does not contain `⊤ : SimpleGraph β`. -/
theorem cliqueFree_iff_top_free {β : Type*} [Fintype β] :
    G.CliqueFree (card β) ↔ (⊤ : SimpleGraph β).Free G := by
  rw [← not_iff_not, not_free, cliqueFree_iff, not_isEmpty_iff,
    isContained_congr (Iso.completeGraph (Fintype.equivFin β)) Iso.refl]
  exact ⟨fun ⟨f⟩ ↦ ⟨f.toCopy⟩, fun ⟨f⟩ ↦ ⟨f.topEmbedding⟩⟩

end CliqueFree

end SimpleGraph
