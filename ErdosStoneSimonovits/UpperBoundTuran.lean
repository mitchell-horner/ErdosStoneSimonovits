import Mathlib

import ErdosStoneSimonovits.Nat
import ErdosStoneSimonovits.Bipartite
import ErdosStoneSimonovits.SpecialGraphs

namespace SimpleGraph

open BigOperators

open Classical in
/-- There exist extremal graphs on vertex type `β` that have no `n`-cliques
provided that `n ≥ 2`. -/
theorem exists_extremal_graph_cliqueFree [Fintype β] {n : ℕ} (hn : n ≥ 2) :
    ∃ E : SimpleGraph β, E.CliqueFree n ∧
      ∀ B : SimpleGraph β,
        B.CliqueFree n → B.edgeFinset.card ≤ E.edgeFinset.card := by
  let p := ((CliqueFree · n) : SimpleGraph β → Prop)
  let hp : ∃ B, p B := ⟨⊥, cliqueFree_bot hn⟩
  exact exists_extremal_graph p hp

/-- A `r+1`-clique free simple graph on the vertex type `V` has at most
`(1-1/r)*(Fintype.card V)^2/2` edges.

This is the upper-bound of **Turán's theorem**. -/
theorem card_edgeFinset_le_of_cliqueFree
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : ℕ} (hr : r ≥ 1) (h : G.CliqueFree (r+1)) :
    G.edgeFinset.card ≤ ((1-1/r)*(Fintype.card V)^2/2 : ℝ) := by
  by_cases h_le_r : Fintype.card V ≤ r
  . by_cases h_eq_zero : Fintype.card V = 0
    . calc (G.edgeFinset.card : ℝ)
        _ ≤ (Fintype.card V).choose 2 := by
            rw [Nat.cast_le]
            exact card_edgeFinset_le_card_choose_two
        _ = (1-1/r)*(Fintype.card V)^2/2 := by
            rw [h_eq_zero, Nat.choose_zero_succ]
            ring_nf
    . calc (G.edgeFinset.card : ℝ)
        _ ≤ (Fintype.card V).choose 2 := by
            rw [Nat.cast_le]
            exact card_edgeFinset_le_card_choose_two
        _ = (1-1/(Fintype.card V))*(Fintype.card V)^2/2 := by
            field_simp [h_eq_zero, Nat.cast_choose_two]
            ring_nf
        _ ≤ (1-1/r)*(Fintype.card V)^2/2 := by
            rw [div_le_div_iff zero_lt_two zero_lt_two,
              mul_le_mul_right zero_lt_two, mul_le_mul_right _,
              sub_le_sub_iff_left,one_div_le_one_div, Nat.cast_le]
            . exact h_le_r
            . rw [Nat.cast_pos]
              exact hr
            . rw [Nat.cast_pos, Nat.pos_iff_ne_zero]
              exact h_eq_zero
            . rw [sq_pos_iff, Nat.cast_ne_zero]
              exact h_eq_zero
  . have hr_lt : r < Fintype.card V := lt_of_not_le h_le_r
    classical
    -- there exists a `r+1`-clique-free extremal graph
    have ⟨M, h_cliqueFree, h_extremal⟩ :
      ∃ M : SimpleGraph V, M.CliqueFree (r+1) ∧
        ∀ G : SimpleGraph V,
          G.CliqueFree (r+1) → G.edgeFinset.card ≤ M.edgeFinset.card := by
      apply exists_extremal_graph_cliqueFree
      field_simp [Nat.succ_le_succ_iff, hr]
    suffices h_le : M.edgeFinset.card ≤ ((1-1/r)*(Fintype.card V)^2/2 : ℝ) by
      trans (M.edgeFinset.card : ℝ)
      . rw [Nat.cast_le]
        convert h_extremal G h
      . exact h_le
    -- the `r+1`-clique-free extremal graph contains an `r`-clique
    have nh_cliqueFree : ¬M.CliqueFree r := by
        by_contra h_cliqueFree'
        have h_clique := CliqueFree.mono hr_lt h_cliqueFree Finset.univ
        rw [isNClique_iff, not_and_or, Finset.card_univ, eq_self_iff_true,
            not_true, or_false, isClique_iff, Set.Pairwise] at h_clique
        push_neg at h_clique
        have ⟨v, _, w, _, h_ne, hadj⟩ := h_clique
        let M' := M ⊔ edge v w
        have h_clique' : M'.CliqueFree (r+1) :=
          CliqueFree.sup_edge h_cliqueFree' v w
        have h_lt' : M.edgeFinset.card < M'.edgeFinset.card :=
          calc M.edgeFinset.card
            _ < M.edgeFinset.card + 1 := Nat.lt_succ_self _
            _ = (M ⊔ edge v w).edgeFinset.card :=
                (card_edgeFinset_sup_edge M hadj h_ne).symm
        absurd h_extremal M' h_clique'
        push_neg
        convert h_lt'
    let ⟨s, h_isClique⟩ := not_forall_not.mp nh_cliqueFree
    have h_card_compl :
        Fintype.card ((↑s)ᶜ : Set V) = (Fintype.card V)-r := by
      simp_rw [←Finset.coe_compl, Finset.coe_sort_coe, Fintype.card_coe,
        Finset.card_compl, h_isClique.card_eq]
    suffices h_le : (M.between s (↑s)ᶜ).edgeFinset.card
          + (M.induce s).edgeFinset.card
          + (M.induce (↑s)ᶜ).edgeFinset.card
        ≤ ((1-1/r)*(Fintype.card V)^2/2 : ℝ) by
      simp_rw [card_edgeFinset_decomposition_of_compl M s,
        card_edgeFinset_restrict_eq_induce, Nat.cast_add]
      convert h_le
    -- there are at most `(r-1)*(Fintype.card V-r)` edges between `s` and `sᶜ`
    have h₁ : (M.between s (↑s)ᶜ).edgeFinset.card
        ≤ ((Fintype.card V-r)*(r-1) : ℝ) := by
      have h_isBipartite :
          (M.between s (↑s)ᶜ).IsBipartite s (sᶜ : Finset V) := by
        rw [Finset.coe_compl]
        exact isBipartite_between_of_disjoint (disjoint_compl_right)
      rw [←Nat.cast_pred hr, ←Nat.cast_sub (le_of_lt hr_lt),
        ←Nat.cast_mul, Nat.cast_le]
      calc (M.between s (↑s)ᶜ).edgeFinset.card
        _ = ∑ v ∈ sᶜ, (M.between s (↑s)ᶜ).degree v := by
            convert isBipartite_sum_degrees_eq_card_edges' h_isBipartite
        _ ≤ ∑ v ∈ sᶜ, (r-1) := by
            apply Finset.sum_le_sum
            by_contra! h_lt
            replace ⟨v, hv, h_lt⟩ := h_lt
            -- if `degree v ≥ r` then `insert v s` is an `r`-clique
            have h_neighborFinset:
                (M.between s (↑s)ᶜ).neighborFinset v = s := by
              rw [←card_neighborFinset_eq_degree, ←h_isClique.card_eq] at h_lt
              apply Finset.eq_of_subset_of_card_le _ (Nat.le_of_pred_lt h_lt)
              exact isBipartite_neighborFinset_subset' h_isBipartite hv
            have hadj : ∀ w ∈ s, M.Adj v w := by
              rw [isBipartite_neighborFinset' h_isBipartite hv,
                Finset.filter_eq_self] at h_neighborFinset
              intro w hw
              apply between_le s (↑s)ᶜ
              exact (h_neighborFinset w hw).symm
            absurd IsNClique.insert ⟨h_isClique.clique, by rfl⟩ hadj
            rw [h_isClique.card_eq]
            exact h_cliqueFree (insert v s)
        _ = ((Fintype.card V)-r)*(r-1) := by
            rw [Finset.sum_const, Finset.card_compl, h_isClique.card_eq,
              smul_eq_mul]
    -- there are at most `r.choose 2` edges in `s`
    have h₂ : (M.induce s).edgeFinset.card
        ≤ (r*(r-1)/2 : ℝ) := by
      rw [←Nat.cast_choose_two, Nat.cast_le, ←h_isClique.card_eq,
        ←Fintype.card_coe s]
      exact card_edgeFinset_le_card_choose_two
    -- there are at most `(1-1/r)*(Fintype.card V-r)^2/2` edges in `sᶜ`
    have h₃ : (M.induce (↑s)ᶜ).edgeFinset.card
        ≤ ((1-1/r)*(Fintype.card V-r)^2/2 : ℝ) := by
      have h_cliqueFree : (M.induce (↑s)ᶜ).CliqueFree (r+1) :=
        CliqueFree.comap (Embedding.induce ((↑s)ᶜ : Set V)) h_cliqueFree
      convert card_edgeFinset_le_of_cliqueFree hr h_cliqueFree using 1
      rw [h_card_compl, Nat.cast_sub (le_of_lt hr_lt)]
    convert add_le_add_three h₁ h₂ h₃ using 1
    field_simp
    ring_nf
termination_by (Fintype.card V)
decreasing_by
  rw [h_card_compl]
  exact Nat.sub_lt_self hr (le_of_lt hr_lt)

/-- A simple graph does not contain `completeGraph (Fin n)` as an isomorphic
subgraph if and only if it has no `n`-cliques. -/
theorem not_isIsoSubgraph_completeGraph_iff_cliqueFree {n : ℕ} :
    ¬(completeGraph (Fin n)).IsIsoSubgraph G ↔ G.CliqueFree n := by
  rw [←not_iff_not, not_not, cliqueFree_iff, not_isEmpty_iff]
  refine ⟨?_, fun ⟨f⟩ ↦ ⟨f, f.injective⟩⟩
  intro ⟨f, hf⟩
  use ⟨f, hf⟩
  intro v w
  rw [top_adj]
  refine ⟨?_, Hom.map_adj f⟩
  contrapose
  push_neg
  intro h
  rw [h]
  exact G.loopless (f w)

/-- The extremal numbers of the `r+1`-complete graphs on the type `V` are at
most `(1-1/r)*(Fintype.card V)^2/2`.

See `card_edgeFinset_le_of_cliqueFree`. -/
theorem extremalNumber_completeGraph_le (V : Type*) [Fintype V] (hr : 1 ≤ r) :
    extremalNumber V (completeGraph (Fin (r+1)))
      ≤ ((1-1/r)*(Fintype.card V)^2/2 : ℝ) := by
  have h_nonneg : 0 ≤ ((1-1/r)*(Fintype.card V)^2/2 : ℝ) := by
    apply div_nonneg _ zero_le_two
    apply mul_nonneg _ (sq_nonneg _)
    exact Nat.one_sub_one_div_cast_nonneg r
  simp_rw [extremalNumber_le_iff_of_nonneg _ _ h_nonneg,
    not_isIsoSubgraph_completeGraph_iff_cliqueFree]
  intro G h_cliqueFree
  classical
  exact card_edgeFinset_le_of_cliqueFree hr h_cliqueFree
