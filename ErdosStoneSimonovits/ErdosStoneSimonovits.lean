import Mathlib

import ErdosStoneSimonovits.Nat
import ErdosStoneSimonovits.QuadraticFunctions

import ErdosStoneSimonovits.Degree
import ErdosStoneSimonovits.Bipartite
import ErdosStoneSimonovits.SpecialGraphs

import ErdosStoneSimonovits.TuranDensity

open Topology Asymptotics Real

namespace SimpleGraph

/-- Suppose `r`, `t` are natural numbers and `ε > 0` is a real number. A simple
graph of sufficently many vertices `n` having a minimal degree of at least
`(1-1/r+ε)*n` contains a copy of a complete equipartite graph in `r+1`
partitions each of size `t` as an isomorphic subgraph.

This is the minimal-degree version of the *Erdős-Stone theorem*. -/
theorem isIsoSubgraph_completeEquipartiteGraph_of_minDegree
    {ε : ℝ} (hε_pos : 0 < ε) (r t : ℕ) :
    ∃ N, ∀ {V : Type u} [Fintype V] [DecidableEq V], N < Fintype.card V →
      ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
        G.minDegree ≥ (1-1/r+ε)*(Fintype.card V)
        → (completeEquipartiteGraph (Fin (r+1)) (Fin t)).IsIsoSubgraph G := by
  by_cases hr_or_t : r = 0 ∨ t = 0
  -- base case
  . cases hr_or_t with
    | inl hr =>
      use t
      intro V _ _ h_cardV G _ _
      rw [hr, zero_add]
      apply isIsoSubgraph_of_isEmpty_edgeSet
      simp_rw [Fintype.card_prod, Fintype.card_fin, one_mul]
      exact le_of_lt h_cardV
    | inr ht =>
      use 0
      intros
      rw [ht]
      exact isIsoSubgraph_of_isEmpty
  -- inductive step
  . have ⟨hr_pos, ht_pos⟩ : 0 < r ∧ 0 < t := by
      push_neg at hr_or_t
      simpa [←Nat.pos_iff_ne_zero] using hr_or_t
    haveI : Nonempty (Fin t) := by
      rw [←Fintype.card_pos_iff, Fintype.card_fin]
      exact ht_pos
    -- choose ε' > 0
    let ε' := 1/((r-1)*r) + ε
    have hε'_pos : 0 < ε' := by
      apply add_pos_of_nonneg_of_pos _ hε_pos
      rw [one_div_nonneg]
      field_simp
      exact hr_pos
    -- choose `t' > 0`
    let t' := ⌈t/(r*ε)⌉₊ + 1
    have ht'_pos : 0 < t' :=
      lt_of_lt_of_le zero_lt_one (Nat.le_add_left _ _)
    -- inductive hypothesis
    have ⟨N, ih⟩ :=
      isIsoSubgraph_completeEquipartiteGraph_of_minDegree hε'_pos (r-1) t'
    let N' := max N ⌈((t'.choose t)^r*t+r*t')*(t'-t)/(t'*r*ε-t)⌉₊
    use N'
    intro V _ _ hN'_lt_cardV G _ hδ_ge
    have hN_lt_cardV : N < Fintype.card V :=
      lt_of_le_of_lt (le_max_left _ _) hN'_lt_cardV
    -- inequalities involving `r`, `t`, `t'`, `ε`, `ε'`
    have hrε_pos : 0 < r*ε := by
      apply mul_pos _ hε_pos
      rw [Nat.cast_pos]
      exact hr_pos
    have hrε_lt_one : r*ε < 1 := by
      by_contra! nh
      rw [←div_le_iff₀'] at nh
      absurd calc (G.minDegree : ℝ)
        _ ≥ (1-1/r+ε)*(Fintype.card V) := hδ_ge
        _ ≥ (Fintype.card V) := by
            apply le_mul_of_one_le_left (Nat.cast_nonneg _)
            rw [sub_add, le_sub_self_iff, sub_nonpos]
            exact nh
      push_neg
      rw [Nat.cast_lt]
      haveI : Nonempty V := by
        rw [←Fintype.card_pos_iff]
        exact lt_of_le_of_lt (Nat.zero_le _) hN'_lt_cardV
      exact minDegree_lt_card G
      rw [Nat.cast_pos]
      exact hr_pos
    have ht_lt_t'rε : t < t'*r*ε := by
      rw [mul_assoc, ←div_mul_cancel₀ (t : ℝ) hrε_pos.ne',
        mul_lt_mul_right hrε_pos, Nat.cast_add_one]
      exact lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one)
        (add_le_add_right (Nat.le_ceil _) _)
    have ht_lt_t' : (t : ℝ) < (t' : ℝ) := by
      replace ht'_pos : 0 < (t' : ℝ) := by
        rw [Nat.cast_pos]
        exact ht'_pos
      rw [←mul_lt_iff_lt_one_right ht'_pos, ←mul_assoc] at hrε_lt_one
      exact ht_lt_t'rε.trans hrε_lt_one
    replace ht_lt_t' : t < t' := by
      rwa [Nat.cast_lt] at ht_lt_t'
    have ht'_le_N' : (t' : ℝ) ≤ (N' : ℝ) :=
      calc (t' : ℝ)
        _ ≤ r*t' := by
            rw [le_mul_iff_one_le_left, Nat.one_le_cast]
            exact hr_pos
            rw [Nat.cast_pos]
            exact ht'_pos
        _ ≤ (t'.choose t)^r*t + r*t' := by field_simp
        _ ≤ ((t'.choose t)^r*t + r*t')*(t'-t)/(t'*r*ε-t) := by
            rw [mul_div_assoc, le_mul_iff_one_le_right, one_le_div]
            apply sub_le_sub_right
            rw [mul_assoc, mul_le_iff_le_one_right]
            exact le_of_lt hrε_lt_one
            rw [Nat.cast_pos]
            exact ht'_pos
            rw [sub_pos]
            exact ht_lt_t'rε
            apply add_pos_of_nonneg_of_pos
            all_goals field_simp
        _ ≤ N' := by
            apply (Nat.le_ceil _).trans
            rw [Nat.cast_le]
            exact le_max_right N _
    replace ht'_le_N' : t' ≤ N' := by rwa [Nat.cast_le] at ht'_le_N'
    -- identify `completeEquipartiteGraph (Fin r) (Fin t')`
    have h_iso_sub :
        (completeEquipartiteGraph (Fin r) (Fin t')).IsIsoSubgraph G := by
      by_cases hr_one : r = 1
      . rw [hr_one]
        apply isIsoSubgraph_of_isEmpty_edgeSet
        simp_rw [Fintype.card_prod, Fintype.card_fin, one_mul]
        exact le_of_lt (lt_of_le_of_lt ht'_le_N' hN'_lt_cardV)
      . have hr_ne : (r : ℝ) ≠ 0 := by
          rw [Nat.cast_ne_zero]
          exact hr_pos.ne'
        have hrpred_ne : (r-1 : ℝ) ≠ 0 := by
          rw [sub_ne_zero, Nat.cast_ne_one]
          exact hr_one
        have hδ_ge' : G.minDegree ≥ (1-1/↑(r-1)+ε')*(Fintype.card V) :=
          calc (G.minDegree : ℝ)
            _ ≥ (1-1/(r-1)+(1/(r-1)-1/r)+ε)*(Fintype.card V) := by
                rw [sub_add_sub_cancel]
                exact hδ_ge
            _ = (1-1/(r-1)+1/((r-1)*r)+ε)*(Fintype.card V) := by
                rw [←one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
                  hrpred_ne hr_ne]
                field_simp
            _ = (1-1/↑(r-1)+ε')*(Fintype.card V) := by
                rw [Nat.cast_pred hr_pos]
                ring_nf
        rw [←Nat.succ_pred_eq_of_pos hr_pos]
        exact ih hN_lt_cardV hδ_ge'
    rw [isIsoSubgraph_completeEquipartiteGraph_iff] at h_iso_sub
    -- `A₁, …, Aᵣ` partitions of `completeEquipartiteGraph (Fin r) (Fin t')`
    have ⟨A, hA⟩ := h_iso_sub
    have h_cardA (i : Fin r) : (A i).val.card = t' := by
      have h_mem := (A i).prop
      simp_rw [Finset.mem_powersetCard, Fintype.card_fin t'] at h_mem
      exact h_mem.2
    have h_pairwise_disjointA :
        Set.univ.PairwiseDisjoint (Subtype.val ∘ (A ·)) := by
      intro i₁ _ i₂ _ hi
      rw [Function.onFun_apply, Finset.disjoint_left]
      intro v hi₁
      by_contra! hi₂
      absurd G.loopless v
      apply hA i₁ i₂ hi v hi₁ v hi₂
    rw [←Finset.coe_univ] at h_pairwise_disjointA
    -- `U` vertices in `A₁ ∪ … ∪ Aᵣ`
    let U : Finset V :=
      (Finset.univ.disjiUnion (Subtype.val ∘ (A ·)) h_pairwise_disjointA)ᶜ
    have h_cardUcompl : Uᶜ.card = r*t' := by
      simp_rw [compl_compl _, Finset.card_disjiUnion, Function.comp_apply,
        h_cardA, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
    -- `W ⊆ U` vertices adjacent to at least `t` vertices in each `A₁, …, Aᵣ`
    let W := U.filter fun v ↦
      ∀ i : Fin r, ∃ s : Finset.powersetCard t (A i).val,
        ∀ w ∈ s.val, G.Adj v w
    -- `W.card` is arbitrarily large
    have h_cardW : ((t'.choose t)^r*t : ℝ) < (W.card : ℝ) := by
      -- double-counting edges between `U` and `Uᶜ`
      have h_between_isBipartite :
          (G.between U (↑U)ᶜ).IsBipartite U (Uᶜ : Finset V) := by
        rw [Finset.coe_compl U]
        exact isBipartite_between_of_disjoint (disjoint_compl_right)
      -- counting over `Uᶜ`
      have h_le_between :
          Uᶜ.card*((1-1/r+ε)*(Fintype.card V)-Uᶜ.card)
            ≤ ((G.between U (↑U)ᶜ).edgeFinset.card : ℝ) :=
        calc Uᶜ.card*((1-1/r+ε)*(Fintype.card V)-Uᶜ.card)
          _ ≤ Uᶜ.card*(G.minDegree-Uᶜ.card) := by
              apply mul_le_mul_of_nonneg_left
              apply sub_le_sub_right hδ_ge
              exact Nat.cast_nonneg _
          _ = ∑ _ ∈ Uᶜ, (G.minDegree-Uᶜ.card : ℝ) := by
              rw [Finset.sum_const]
              ring_nf
          _ ≤ ∑ v ∈ Uᶜ, (G.between U (↑U)ᶜ).degree v := by
              rw [Nat.cast_sum]
              apply Finset.sum_le_sum
              intro v hv
              rw [sub_le_iff_le_add, ←Nat.cast_add, Nat.cast_le]
              exact (minDegree_le_degree G v).trans
                (degree_le_between_degree_plus_card' U hv)
          _ = (G.between U (↑U)ᶜ).edgeFinset.card := by
              rw [Nat.cast_inj, eq_comm]
              convert isBipartite_sum_degrees_eq_card_edges'
                h_between_isBipartite
      -- if `v ∈ U\W`, then `G.degree v < (r-1)*t'+t`, else `v ∈ W`
      have h_degree_lt {v : V} (hv : v ∈ U\W) :
          (G.between U (↑U)ᶜ).degree v < Uᶜ.card-t'+t := by
        rw [Finset.mem_sdiff, Finset.mem_filter] at hv
        push_neg at hv
        have ⟨i, hs⟩ := hv.2 hv.1
        rw [h_cardUcompl, ←Nat.sub_one_mul, ←card_neighborFinset_eq_degree,
          isBipartite_neighborFinset h_between_isBipartite hv.1, compl_compl,
          Finset.disjiUnion_eq_biUnion, Finset.filter_biUnion,
          Finset.card_biUnion, ←Finset.union_compl {i}, Finset.union_comm,
          Finset.sum_union disjoint_compl_left, Finset.sum_singleton]
        apply add_lt_add_of_le_of_lt
        . calc _
            _ ≤ ∑ i' ∈ {i}ᶜ, (A i').val.card := by
                apply Finset.sum_le_sum
                intro _ _
                exact Finset.card_filter_le _ _
            _ = (r-1)*t' := by
                simp_rw [h_cardA, Finset.sum_const, Finset.card_compl,
                  Fintype.card_fin, Finset.card_singleton, smul_eq_mul]
        . contrapose! hs
          rw [←Finset.powersetCard_nonempty] at hs
          replace ⟨s, hs⟩ := hs
          use ⟨s, Finset.powersetCard_mono (Finset.filter_subset _ _) hs⟩
          rw [Finset.mem_powersetCard] at hs
          intro w hw
          replace hw := hs.1 hw
          rw [Finset.mem_filter,
            between_adj_of_disjoint (disjoint_compl_right)] at hw
          exact hw.2.1
        intro i₁ hi₁ i₂ hi₂ h
        apply Finset.disjoint_filter_filter
        apply h_pairwise_disjointA hi₁ hi₂ h
      -- counting over `U`
      have h_between_le :
          ((G.between U (↑U)ᶜ).edgeFinset.card : ℝ)
            ≤ ((Fintype.card V)-Uᶜ.card)*(Uᶜ.card-(t'-t))+W.card*(t'-t) :=
        calc ((G.between U (↑U)ᶜ).edgeFinset.card : ℝ)
          _ = ∑ v ∈ U, ((G.between U (↑U)ᶜ).degree v : ℝ) := by
              rw [←Nat.cast_sum, Nat.cast_inj]
              convert isBipartite_sum_degrees_eq_card_edges
                h_between_isBipartite
          _ = ∑ v ∈ U\W, ((G.between U (↑U)ᶜ).degree v : ℝ)
                + ∑ v ∈ W, ((G.between U (↑U)ᶜ).degree v : ℝ) := by
              rw [eq_comm, Finset.sum_sdiff]
              exact Finset.filter_subset _ _
          _ ≤ ∑ _ ∈ U\W, (Uᶜ.card-t'+t : ℝ)
                + ∑ _ ∈ W, (Uᶜ.card : ℝ) := by
              apply add_le_add
              all_goals apply Finset.sum_le_sum
              . intro v hv
                rw [←Nat.cast_sub, ←Nat.cast_add, Nat.cast_le]
                exact le_of_lt (h_degree_lt hv)
                rw [h_cardUcompl]
                apply Nat.le_mul_of_pos_left
                exact hr_pos
              . intro v hv
                rw [Nat.cast_le]
                exact isBipartite_degree_le h_between_isBipartite
                  (Finset.filter_subset _ _ hv)
          _ = ((Fintype.card V)-Uᶜ.card)*(Uᶜ.card-(t'-t))+W.card*(t'-t) := by
              have hW_sub : W ⊆ U := Finset.filter_subset _ _
              have h_cardW_le : W.card ≤ U.card :=
                Finset.card_le_card (Finset.filter_subset _ _)
              simp_rw [Finset.sum_const, Finset.card_sdiff hW_sub,
                nsmul_eq_mul, Nat.cast_sub h_cardW_le]
              conv_lhs =>
                lhs; lhs;
                rw [←compl_compl U]
              have h_cardUcompl_le : Uᶜ.card ≤ Fintype.card V := by
                exact Finset.card_le_card (Finset.subset_univ _)
              simp_rw [Finset.card_compl Uᶜ, Nat.cast_sub h_cardUcompl_le]
              ring_nf
      have h_cardW_mul_right :
          ((t'.choose t)^r*t*(t'-t) : ℝ) < (W.card*(t'-t) : ℝ) :=
        calc ((t'.choose t)^r*t*(t'-t) : ℝ)
          _ < (Fintype.card V)*(t'*r*ε-t)-r*t'*(t'-t) := by
              rw [←add_sub_cancel_right (_^r*t : ℝ) (r*t' : ℝ), sub_mul,
                ←div_mul_cancel₀ ((_^r*t+r*t')*(t'-t) : ℝ)]
              apply sub_lt_sub_right
              . apply mul_lt_mul_of_pos_right
                . apply lt_of_le_of_lt (b := (N' : ℝ))
                  . apply (Nat.le_ceil _).trans
                    rw [Nat.cast_le]
                    exact le_max_right _ _
                  . rw [Nat.cast_lt]
                    exact hN'_lt_cardV
                . rw [sub_pos]
                  exact ht_lt_t'rε
              . rw [sub_ne_zero]
                exact ht_lt_t'rε.ne'
          _ ≤ W.card*(t'-t) := by
              convert sub_left_le_of_le_add
                (h_le_between.trans h_between_le) using 1
              field_simp [h_cardUcompl]
              ring_nf
      rwa [mul_lt_mul_right] at h_cardW_mul_right
      rw [sub_pos, Nat.cast_lt]
      exact ht_lt_t'
    have h_cardW : (t'.choose t)^r*t < W.card := by
      rwa [←Nat.cast_pow, ←Nat.cast_mul, Nat.cast_lt] at h_cardW
    -- strong pigeonhole principle
    let F : W → Π i : Fin r, Finset.powersetCard t (A i).val := by
      intro ⟨w, hw⟩ i
      rw [Finset.mem_filter] at hw
      exact (hw.2 i).choose
    have hF (w : W) (i : Fin r) : ∀ v ∈ (F w i).val, G.Adj w v := by
      have hw := w.prop
      rw [Finset.mem_filter] at hw
      exact (hw.2 i).choose_spec
    haveI : Nonempty (Π i : Fin r, Finset.powersetCard t (A i).val) := by
      rw [Classical.nonempty_pi]; intro i
      rw [Finset.nonempty_coe_sort, Finset.powersetCard_nonempty, h_cardA i]
      exact le_of_lt ht_lt_t'
    have ⟨y, hy⟩ : ∃ y : Π i : Fin r, Finset.powersetCard t (A i).val,
        t ≤ (Finset.univ.filter (F · = y)).card := by
      apply Fintype.exists_le_card_fiber_of_mul_le_card
      simp_rw [Fintype.card_pi, Fintype.card_coe, Finset.card_powersetCard,
        h_cardA, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact le_of_lt h_cardW
    rw [isIsoSubgraph_completeEquipartiteGraph_succ_iff, Fintype.card_fin t]
    -- identify `completeEquipartiteGraph (Fin r) (Fin t)`
    let A' (i : Fin r) : (Finset.univ : Finset V).powersetCard t := by
      use (y i).val
      have hyi := (y i).prop
      rw [Finset.mem_powersetCard] at hyi ⊢
      exact ⟨Finset.subset_univ _, hyi.2⟩
    use A'
    constructor
    . intro i₁ i₂ hi v₁ hv₁ v₂ hv₂
      apply hA i₁ i₂ hi
      . have hyi₁ := (y i₁).prop
        rw [Finset.mem_powersetCard] at hyi₁
        exact hyi₁.1 hv₁
      . have hyi₂ := (y i₂).prop
        rw [Finset.mem_powersetCard] at hyi₂
        exact hyi₂.1 hv₂
    -- identify `completeEquipartiteGraph (Fin (r+1)) (Fin t')`
    . have ⟨s', hs'⟩ := Finset.exists_subset_card_eq hy
      let s : Finset.univ.powersetCard t := by
        use s'.map (Function.Embedding.subtype (· ∈ W))
        rw [Finset.mem_powersetCard, Finset.card_map]
        exact ⟨Finset.subset_univ _, hs'.2⟩
      use s
      intro v₁ hv₁ i v₂ hv₂
      have hv₁' := Finset.property_of_mem_map_subtype s' hv₁
      let v₁' : W := ⟨v₁, hv₁'⟩
      apply hF v₁' i v₂
      replace hv₁' : v₁' ∈ s' := by
        rw [Finset.mem_map] at hv₁
        convert hv₁.choose_spec.1
        rw [Subtype.ext_iff]
        exact hv₁.choose_spec.2.symm
      replace hv₁' := hs'.1 hv₁'
      rw [Finset.mem_filter] at hv₁'
      rw [hv₁'.2]
      exact hv₂

/-- This auxiliary lemma encapsulates recursively removing minimal degree
vertices until `c*s.card ≤ (G.induce s).minDegree`. -/
private lemma exists_induced_subgraph_for_minDegree
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ s : Finset V,
      (s : Set V) ⊆ G.support ∧
      c*s.card ≤ (G.induce s).minDegree ∧
      (G.induce s).edgeFinset.card ≥
        G.edgeFinset.card
        -c*((Fintype.card G.support)^2-s.card^2)/2
        -(Fintype.card G.support-s.card)/2 := by
  by_cases hδ :
      c*G.support.toFinset.card ≤ (G.induce G.support.toFinset).minDegree
  -- base case
  . refine ⟨G.support.toFinset, by simp, hδ, ?_⟩
    suffices h_coe_toFinset :
        (G.induce G.support).edgeFinset.card ≥ G.edgeFinset.card
          -c*((Fintype.card G.support)^2-G.support.toFinset.card^2)/2
          -((Fintype.card G.support)-G.support.toFinset.card)/2 by
      convert h_coe_toFinset
      all_goals rw [Set.coe_toFinset]
    simp_rw [Set.toFinset_card G.support, card_edgeFinset_induce_support_eq]
    ring_nf; rfl
  -- inductive step
  . replace hδ :
        (G.induce G.support).minDegree < c*(Fintype.card G.support) := by
      push_neg at hδ
      convert hδ
      all_goals simp
    have h_card_support_pos : 0 < Fintype.card G.support := by
      contrapose! hδ
      rw [Nat.le_zero] at hδ
      field_simp [hδ]
    haveI : Nonempty G.support := by
      rwa [Fintype.card_pos_iff] at h_card_support_pos
    -- delete minimal degree vertex
    have ⟨x, hδ_eq_degx⟩ := exists_minimal_degree_vertex (G.induce G.support)
    let G' := G.deleteIncidenceSet ↑x
    have ⟨s, h_subset, ihδ, ih_card_edgeFinset⟩ :=
      exists_induced_subgraph_for_minDegree hc_nonneg hc_le_one G'
    replace h_subset : (s : Set V) ⊆ G.support \ {↑x} := by
      trans G'.support
      . exact h_subset
      . convert deleteIncidenceSet_support_subset G ↑x
    have hx_not_mem : ↑x ∉ (s : Set V) := by
      rw [Set.subset_diff, Set.disjoint_singleton_right] at h_subset
      exact h_subset.2
    -- delete induce eq induce
    replace ihδ : c*s.card ≤ (G.induce s).minDegree := by
      convert ihδ using 1
      simp_rw [deleteIncidenceSet_induce_of_not_mem G hx_not_mem]
    replace ih_card_edgeFinset :
        (G.induce s).edgeFinset.card ≥ G'.edgeFinset.card
          - c*((Fintype.card G'.support)^2-s.card^2)/2
          - ((Fintype.card G'.support)-s.card)/2 := by
      convert ih_card_edgeFinset using 1
      simp_rw [Set.toFinset_card,
        deleteIncidenceSet_induce_of_not_mem G hx_not_mem]
    refine ⟨s, ?_, ihδ, ?_⟩
    . rw [Set.subset_diff] at h_subset
      exact h_subset.1
    . calc ((G.induce s).edgeFinset.card : ℝ)
        _ ≥ G'.edgeFinset.card
          - (c*((Fintype.card G'.support)^2-s.card^2)/2
            + (Fintype.card G'.support-s.card)/2) := by
            rwa [sub_sub] at ih_card_edgeFinset
        _ ≥ (G.edgeFinset.card-c*(Fintype.card G.support))
          - (c*((Fintype.card G.support-1)^2-s.card^2)/2
            + (Fintype.card G.support-1-s.card)/2) := by
            apply sub_le_sub
            -- exactly `G.minDegree` edges deleted from edge set
            . rw [card_edgeFinset_deleteIncidenceSet G ↑x,
                Nat.cast_sub (degree_le_card_edgeFinset G x),
                ←degree_restrict_support_eq, degree_restrict_eq_induce,
                ←hδ_eq_degx]
              exact sub_le_sub_left (le_of_lt hδ) _
            -- at least `x` is deleted from support
            . rw [←add_div, ←add_div, div_le_div_right zero_lt_two]
              apply add_le_add
              . apply mul_le_mul_of_nonneg_left _ hc_nonneg
                rw [sub_le_sub_iff_right]
                apply pow_le_pow_left (Nat.cast_nonneg _)
                rw [←Nat.cast_pred Fintype.card_pos, Nat.cast_le]
                exact card_support_deleteIncidenceSet G x.prop
              . rw [sub_le_sub_iff_right,
                  ←Nat.cast_pred Fintype.card_pos, Nat.cast_le]
                exact card_support_deleteIncidenceSet G x.prop
        _ = (G.edgeFinset.card
            - c*((Fintype.card G.support)^2-s.card^2)/2
            - (Fintype.card G.support-s.card)/2)
          + (1-c)/2 := by ring_nf
        _ ≥ G.edgeFinset.card
          - c*((Fintype.card G.support)^2-s.card^2)/2
          - (Fintype.card G.support-s.card)/2 := by
            apply le_add_of_nonneg_right
            apply div_nonneg _ zero_le_two
            exact sub_nonneg_of_le hc_le_one
termination_by Fintype.card G.support
decreasing_by
  rw [Nat.pos_iff_ne_zero] at h_card_support_pos
  exact lt_of_le_of_lt
    (card_support_deleteIncidenceSet G x.prop) (Nat.pred_lt h_card_support_pos)

/-- This auxiliary lemma improves the bound on `s.card^2`.

See `exists_induced_subgraph_for_minDegree`. -/
private lemma exists_induced_subgraph_for_minDegree_for_card_sq
    {c ε : ℝ} (hc_nonneg : 0 ≤ c) (hε_nonneg : 0 ≤ ε)
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.edgeFinset.card ≥ (c+ε)*(Fintype.card V)^2/2) :
    ∃ s : Finset V,
      c*s.card ≤ (G.induce s).minDegree ∧
      ε*(Fintype.card V)^2-(Fintype.card V) ≤ s.card^2 := by
  by_cases h_cardV_zero : Fintype.card V = 0
  . use ∅
    simp [h_cardV_zero]
  . have h_cardV_pos : 0 < Fintype.card V := by
      rwa [←ne_eq, ←Nat.pos_iff_ne_zero] at h_cardV_zero
    have hc_le_one : c ≤ 1 := by
      by_contra! hc_gt_one
      absurd calc ((Fintype.card V)^2/2 : ℝ)
        _ < (c+ε)*(Fintype.card V)^2/2 := by
            apply div_lt_div_of_pos_right _ zero_lt_two
            apply lt_mul_of_one_lt_left
            . apply pow_pos
              rw [Nat.cast_pos]
              exact h_cardV_pos
            . apply lt_of_lt_of_le hc_gt_one
              exact le_add_of_nonneg_right hε_nonneg
        _ ≤ G.edgeFinset.card := h
      push_neg
      calc (G.edgeFinset.card : ℝ)
        _ ≤ (Fintype.card V)*(Fintype.card V-1)/2 := by
            rw [←Nat.cast_choose_two, Nat.cast_le]
            exact card_edgeFinset_le_card_choose_two
        _ ≤ (Fintype.card V)^2/2 := by
            rw [div_le_div_right zero_lt_two, pow_two]
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            exact le_of_lt (sub_one_lt _)
    have ⟨s, _, hδ, hs⟩ := exists_induced_subgraph_for_minDegree
      hc_nonneg hc_le_one G
    refine ⟨s, hδ, ?_⟩
    suffices h_cards_sq :
        ε*(Fintype.card V)^2/2-(Fintype.card V)/2 ≤ s.card^2/2 by
      rwa [←sub_div, div_le_div_right zero_lt_two] at h_cards_sq
    calc ε*(Fintype.card V)^2/2-(Fintype.card V)/2
      _ = (c+ε)*(Fintype.card V)^2/2
        -(c*(Fintype.card V)^2/2 + (Fintype.card V)/2) := by ring_nf
      _ ≤ (s.card*(s.card-1)/2
          + (c*((Fintype.card G.support)^2 - s.card^2)/2
          + ((Fintype.card G.support) - s.card)/2))
        - (c*(Fintype.card V)^2/2 + (Fintype.card V)/2) := by
          apply sub_le_sub_right
          apply le_trans h
          rw [ge_iff_le, sub_sub, sub_le_iff_le_add] at hs
          apply le_trans hs
          apply add_le_add_right
          rw [←Nat.cast_choose_two, Nat.cast_le, ←Fintype.card_coe s]
          exact card_edgeFinset_le_card_choose_two
      _ = s.card^2/2
        - (c*s.card^2/2 + s.card + c*((Fintype.card V)^2
          - (Fintype.card G.support)^2)/2
          + ((Fintype.card V) - (Fintype.card G.support))/2) := by ring_nf
      _ ≤ s.card^2/2 := by
          apply sub_le_self
          repeat apply add_nonneg
          . apply div_nonneg _ zero_le_two
            apply mul_nonneg hc_nonneg
            exact pow_nonneg (Nat.cast_nonneg _) _
          . exact Nat.cast_nonneg _
          . apply div_nonneg _ zero_le_two
            apply mul_nonneg hc_nonneg
            apply sub_nonneg_of_le
            apply pow_le_pow_left (Nat.cast_nonneg _)
            rw [Nat.cast_le]
            exact card_support_le G
          . apply div_nonneg _ zero_le_two
            apply sub_nonneg_of_le
            rw [Nat.cast_le]
            exact card_support_le G

/-- Suppose `r`, `t` are natural numbers and `ε > 0` is a real number. A simple
graph of sufficently many vertices `n` having at least `(1-1/r+ε)*n^2/2` edges
contains a copy of a complete equipartite graph in `r+1` partitions each of
size `t` as an isomorphic subgraph.

This is the *Erdős-Stone theorem*. -/
theorem isIsoSubgraph_completeEquipartiteGraph_of_card_edgeFinset
    (r t : ℕ) {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ N, ∀ {V : Type u} [Fintype V] [DecidableEq V], N < Fintype.card V →
      ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
        G.edgeFinset.card ≥ (1-1/r+ε)*(Fintype.card V)^2/2
        → (completeEquipartiteGraph (Fin (r+1)) (Fin t)).IsIsoSubgraph G := by
  -- choose `ε'`
  let ε' := ε/2
  have hε'_pos : 0 < ε' := div_pos hε_pos zero_lt_two
  -- choose `c`
  let c := 1-1/r+ε/2
  have hc_pos : 0 < c :=
    add_pos_of_nonneg_of_pos (Nat.one_sub_one_div_cast_nonneg r) hε'_pos
  -- minimal-degree version of Erdős-Stone theorem
  have ⟨N, h_iso_sub⟩ :=
    isIsoSubgraph_completeEquipartiteGraph_of_minDegree hε'_pos r t
  let N' := ⌈1/ε'+N/(sqrt ε')⌉₊
  use N'
  intro V _ _ hN'_lt_cardV G _ h
  -- `s` satisfies minimal-degree version of Erdős-Stone theorem
  rw [←add_halves ε, ←add_assoc] at h
  obtain ⟨s, hδ, h_cards_sq⟩ :=
    exists_induced_subgraph_for_minDegree_for_card_sq
      (le_of_lt hc_pos) (le_of_lt hε'_pos) h
  -- `x ↦ ε' * x^2 - x` is strictly monotonic on `[1 / (2 * ε'), ∞)`
  have h_strictMonoOn :=
    quadratic_strictMonoOn_of_leadingCoeff_pos ε' (-1) 0 hε'_pos
  simp_rw [neg_one_mul, ←sub_eq_add_neg, add_zero, neg_neg] at h_strictMonoOn
  have hN_mem_Ici : (1/ε'+N/sqrt ε' : ℝ) ∈ Set.Ici (1/(2*ε')) := by
    rw [Set.mem_Ici]
    trans 1/ε'
    . rw [mul_comm, ←div_div, half_le_self_iff, one_div_nonneg]
      exact le_of_lt hε'_pos
    . apply le_add_of_nonneg_right
      exact div_nonneg (Nat.cast_nonneg _) (sqrt_nonneg ε')
  have hN'_mem_Ici : (⌈1/ε'+N/sqrt ε'⌉₊ : ℝ) ∈ Set.Ici (1/(2*ε')) := by
    rw [Set.mem_Ici]
    trans 1/ε'+N/sqrt ε'
    . rwa [Set.mem_Ici] at hN_mem_Ici
    . exact Nat.le_ceil _
  have h_cardV_mem_Ici : (Fintype.card V : ℝ) ∈ Set.Ici (1/(2*ε')) := by
    rw [Set.mem_Ici]
    trans (N' : ℝ)
    . rwa [Set.mem_Ici] at hN'_mem_Ici
    . rw [Nat.cast_le]
      exact le_of_lt hN'_lt_cardV
  -- `s.card` satisfies minimal-degree version of Erdős-Stone theorem
  have hN_sq_lt_cards_sq : (N^2 : ℝ) < (s.card^2 : ℝ) :=
    calc (s.card^2 : ℝ)
      _ ≥ ε'*(Fintype.card V)^2-(Fintype.card V) := h_cards_sq
      _ > ε'*N'^2-N' := by
          apply h_strictMonoOn hN'_mem_Ici h_cardV_mem_Ici
          rw [Nat.cast_lt]
          exact hN'_lt_cardV
      _ ≥ ε'*(1/ε'+N/(sqrt ε'))^2-(1/ε'+N/(sqrt ε')) := by
          apply h_strictMonoOn.monotoneOn hN_mem_Ici hN'_mem_Ici
          exact Nat.le_ceil _
      _ = N^2+N/sqrt ε' := by
          ring_nf
          field_simp
          ring_nf
      _ ≥ N^2 := by
          apply le_add_of_nonneg_right
          exact div_nonneg (Nat.cast_nonneg _) (sqrt_nonneg ε')
  have hN_lt_cards : N < s.card := by
    rwa [←Nat.cast_pow, ←Nat.cast_pow, Nat.cast_lt,
      Nat.pow_lt_pow_iff_left two_ne_zero] at hN_sq_lt_cards_sq
  -- identify `completeEquipartiteGraph (Fin (r+1)) (Fin t')`
  simp_rw [←Fintype.card_coe, ←Finset.coe_sort_coe] at hN_lt_cards hδ
  exact (h_iso_sub hN_lt_cards hδ).trans ⟨SubgraphIso.induce G s⟩

variable {W : Type*} [Fintype W] {H : SimpleGraph W}

omit [Fintype W] in
lemma chromaticNumber_succ_iff {r : ℕ} :
    H.chromaticNumber = r+1 ↔ ¬H.Colorable r ∧ H.Colorable (r+1) := by
  constructor
  . intro h
    constructor
    . contrapose! h
      apply ne_of_lt
      rw [←chromaticNumber_le_iff_colorable] at h
      apply lt_of_le_of_lt h
      rw [←Nat.cast_add_one, Nat.cast_lt]
      exact Nat.lt_succ_self _
    . rw [←chromaticNumber_le_iff_colorable, le_iff_eq_or_lt]
      left; exact h
  . intro ⟨nh, h⟩
    apply le_antisymm
    . rwa [←chromaticNumber_le_iff_colorable, Nat.cast_add] at h
    . rw [←chromaticNumber_le_iff_colorable.not] at nh
      push_neg at nh
      exact Order.add_one_le_of_lt nh

/-- Suppose `r > 0` is a natural number such that the chromatic number of the
simple graph `H` equals `r+1`, and `ε > 0` is a real number. The extremal
number `extremalNumber V H` for a sufficently large vertex type `V` is greater
than `(1-1/r-ε)*(card V)^2/2` and at most `(1-1/r+ε)*(card V)^2/2`.

This is the *Erdős-Stone-Simonovits theorem*. -/
theorem lt_extremalNumber_le_of_chromaticNumber {ε : ℝ} (hε_pos : 0 < ε)
    {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r+1) :
    ∃ N, ∀ {V : Type u} [Fintype V] [DecidableEq V], N < Fintype.card V →
      (1-1/r-ε)*(Fintype.card V)^2/2 < extremalNumber V H ∧
      extremalNumber V H ≤ (1-1/r+ε)*(Fintype.card V)^2/2 := by
  have ⟨nhc, hc⟩ := chromaticNumber_succ_iff.mp hχ
  have ⟨N₁, h₁⟩ := lt_ex nhc
  have ⟨N₂, h₂⟩ := ex_le hc
  use max N₁ N₂
  intro V _ _ h_cardV
  refine ⟨h₁ ?_, h₂ ?_⟩
  . exact lt_of_le_of_lt (Nat.le_max_left N₁ N₂) h_cardV
  . exact lt_of_le_of_lt (Nat.le_max_right N₁ N₂) h_cardV
where
  lt_ex (nhc : ¬H.Colorable r) :
      ∃ N, ∀ {V : Type u} [Fintype V] [DecidableEq V], N < Fintype.card V →
        (1-1/r-ε)*(Fintype.card V)^2/2 < extremalNumber V H := by
    let N := ⌈2*r/ε⌉₊
    use N
    intro V _ _ hN_lt_cardV
    have h_cardV_pos : 0 < Fintype.card V :=
      lt_of_le_of_lt N.zero_le hN_lt_cardV
    by_cases hlt_ε : 1-1/r < ε
    . calc (1-1/r-ε)*(Fintype.card V)^2/2
        _ < 0 := by
            rw [←sub_neg] at hlt_ε
            apply div_neg_of_neg_of_pos _ zero_lt_two
            apply mul_neg_of_neg_of_pos hlt_ε
            apply pow_pos
            rw [Nat.cast_pos]
            exact lt_of_le_of_lt (Nat.zero_le _) hN_lt_cardV
        _ ≤ extremalNumber V H := Nat.cast_nonneg _
    . have hε_le : ε ≤ 1-1/r := le_of_not_lt hlt_ε
      have hr_lt_cardV : (r : ℝ) < (Fintype.card V : ℝ) := by
        calc (r : ℝ)
          _ ≤ 2*r/ε := by
              rw [le_div_iff₀ hε_pos, mul_comm, mul_le_mul_right]
              exact hε_le.trans
                ((Nat.one_sub_one_div_cast_le_one r).trans one_le_two)
              rw [Nat.cast_pos]
              exact hr_pos
          _ ≤ N := Nat.le_ceil _
          _ < Fintype.card V := by
              rw [Nat.cast_lt]
              exact hN_lt_cardV
      replace hr_lt_cardV : r < Fintype.card V := by
          rwa [Nat.cast_lt] at hr_lt_cardV
      have h2r_lt_εcardV : 2*r < ε*(Fintype.card V) := by
        rw [←div_lt_iff' hε_pos]
        apply lt_of_le_of_lt (Nat.le_ceil _)
        rw [Nat.cast_lt]
        exact hN_lt_cardV
      -- `completeEquipartiteGraph (Fin r) (Fin t)` does not contain `H`
      let t := Fintype.card V/r
      haveI : Nonempty (Fin r × Fin t) := by
        simp_rw [nonempty_prod, ←Fin.pos_iff_nonempty]
        exact ⟨hr_pos, Nat.div_pos (le_of_lt hr_lt_cardV) hr_pos⟩
      have hc : (completeEquipartiteGraph (Fin r) (Fin t)).Colorable r :=
        completeEquipartiteGraph_colorable_of_fin
      apply lt_extremalNumber_of_colorable _ nhc hc _
      . simp_rw [Fintype.card_prod, Fintype.card_fin]
        exact Nat.mul_div_le _ _
      . calc (1-1/r-ε)*(Fintype.card V)^2/2
          _ < (1-1/r)*(Fintype.card V)^2/2-r*(Fintype.card V) := by
              rw [sub_mul, sub_div]
              apply sub_lt_sub_left
              rw [lt_div_iff zero_lt_two, mul_comm, ←mul_assoc, pow_two,
                ←mul_assoc]
              apply mul_lt_mul_of_pos_right
              exact h2r_lt_εcardV
              rw [Nat.cast_pos]
              exact h_cardV_pos
          _ = (1-1/↑r)*↑r^2*t^2/2
            - (↑r*↑(Fintype.card V)
              - (1-1/↑r)*(↑(Fintype.card V)*↑(Fintype.card V%r)))
            - (1-1/↑r)*↑(Fintype.card V % r)^2/2 := by
              conv_lhs =>
                lhs; rw [←Nat.div_add_mod (Fintype.card V) r, Nat.cast_add,
                  add_sq, add_assoc, mul_add, add_div]
                lhs; rw [Nat.cast_mul, mul_pow, ←mul_assoc]
              rw [Nat.mul_div_eq_sub_mod (Fintype.card V) r,
                Nat.cast_sub (Nat.mod_le _ _)]
              ring_nf
          _ ≤ (1-1/r)*r^2*t^2/2 := by
              rw [sub_sub]
              apply sub_le_self
              apply add_nonneg
              . apply sub_nonneg_of_le
                rw [←mul_assoc, mul_comm (r : ℝ) _]
                apply mul_le_mul _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
                . rw [mul_le_iff_le_one_left]
                  exact Nat.one_sub_one_div_cast_le_one r
                  rw [Nat.cast_pos]
                  exact h_cardV_pos
                . rw [Nat.cast_le]
                  exact le_of_lt (Nat.mod_lt _ hr_pos)
              . apply div_nonneg _ zero_le_two
                apply mul_nonneg (Nat.one_sub_one_div_cast_nonneg _)
                rw [←Nat.cast_pow]
                exact Nat.cast_nonneg _
          _ = (completeEquipartiteGraph (Fin r) (Fin t)).edgeFinset.card := by
              simp_rw [card_edgeFinset_completeEquipartiteGraph,
                Fintype.card_fin, Nat.cast_mul, Nat.cast_pow,
                Nat.cast_choose_two]
              field_simp
              ring_nf
  ex_le (hc : H.Colorable (r+1)) :
      ∃ N, ∀ {V : Type u} [Fintype V] [DecidableEq V], N < Fintype.card V →
        extremalNumber V H ≤ (1-1/r+ε)*(Fintype.card V)^2/2 := by
    have ⟨t, h₁⟩ :=
      isIsoSubgraph_completeEquipartiteGraph_of_colorable hc
    -- Erdős-Stone theorem
    have ⟨N, h₂⟩ :=
      isIsoSubgraph_completeEquipartiteGraph_of_card_edgeFinset r t hε_pos
    use N
    intro V _ _ hN_lt_cardV
    trans (extremalNumber V (completeEquipartiteGraph (Fin (r+1)) (Fin t)) : ℝ)
    -- `completeEquipartiteGraph (Fin (r+1)) (Fin t)` contains `H`
    . rw [Nat.cast_le]
      apply extremalNumber_le_extremalNumber_of_isIsoSubgraph
      apply h₁
      rw [Fintype.card_fin]
    . have h_nonneg : 0 ≤ (1-1/r+ε)*(Fintype.card V)^2/2 := by
        apply div_nonneg _ zero_le_two
        apply mul_nonneg
        . apply add_nonneg _ (le_of_lt hε_pos)
          exact Nat.one_sub_one_div_cast_nonneg _
        . rw [←Nat.cast_pow]
          exact Nat.cast_nonneg _
      -- contains `completeEquipartiteGraph (Fin (r+1)) (Fin t)`
      rw [extremalNumber_le_iff_of_nonneg V _ h_nonneg]
      classical
      intro G
      contrapose!
      intro h
      exact h₂ hN_lt_cardV (le_of_lt h)

/-- Suppose `r > 0` is a natural number such that the chromatic number of the
simple graph `H` equals `r+1`. The difference of the extremal number
`extremalNumber (Fin n) H` and `(1-1/r)*n^2/2` is little-o of `n^2` at
infinity.

This is a corollary of the *Erdős-Stone-Simonovits theorem*. -/
theorem isLittleO_extremalNumber_of_chromaticNumber
    {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r+1) :
    (fun (n : ℕ) ↦ (extremalNumber (Fin n) H-(1-1/r)*n^2/2 : ℝ))
      =o[Filter.atTop] (fun (n : ℕ) ↦ (n^2 : ℝ)) := by
  rw [isLittleO_iff]
  intro ε hε_pos
  rw [Filter.eventually_atTop]
  have ⟨N, h⟩ := lt_extremalNumber_le_of_chromaticNumber hε_pos hr_pos hχ
  use N+1
  intro n hn
  replace hn : Fintype.card (Fin n) > N := by
    rw [Fintype.card_fin]
    exact hn
  specialize h hn
  rw [Fintype.card_fin] at h
  rw [norm_eq_abs, ←abs_of_pos hε_pos, norm_eq_abs,
    ←abs_mul, ←sq_le_sq]
  apply sq_le_sq'
  all_goals linarith

/-- Suppose `r > 0` is a natural number such that the chromatic number of the
simple graph `H` equals `r+1`. The density of the extremal graphs that do not
contain `H` as an isomorphic subgraph tends to `1-1/r` at infinity.

This is a corollary of the *Erdős-Stone-Simonovits theorem*. -/
theorem tendsto_extremalNumber_div_choose_two_of_chromaticNumber
    {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r+1) :
    Filter.Tendsto (fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ))
      Filter.atTop (𝓝 (1-1/r)) := by
  have h₁ : Filter.Tendsto (fun (n : ℕ) ↦ (1-(n/(n-1)) : ℝ))
      Filter.atTop (𝓝 0) := by
    rw [←sub_self 1]
    exact (tendsto_const_nhds).sub (tendsto_natCast_div_add_atTop (-1 : ℝ))
  apply Filter.Tendsto.const_mul (1-1/r : ℝ) at h₁
  simp_rw [mul_zero, mul_sub, mul_one] at h₁
  have h₂ := IsLittleO.trans_isTheta
    (isLittleO_extremalNumber_of_chromaticNumber hr_pos hχ)
    Nat.isTheta_choose_two.symm
  apply IsLittleO.tendsto_div_nhds_zero at h₂
  simp_rw [sub_div, mul_div_assoc] at h₂
  have h₂_sub_h₁ := h₂.sub h₁
  simp_rw [sub_zero] at h₂_sub_h₁
  rw [←tendsto_sub_nhds_zero_iff]
  convert h₂_sub_h₁ using 1
  ext n
  by_cases hn : (n : ℝ) = 0
  . field_simp [hn]
  . rw [Nat.cast_choose_two, div_div_div_eq, pow_two,
      ←mul_assoc 2 _ (n-1 : ℝ), mul_assoc (n : ℝ) _ 2, mul_comm (n : ℝ) 2,
      mul_comm (n : ℝ) (2*n : ℝ), mul_div_mul_comm]
    field_simp [hn]
    ring_nf

/-- Suppose `r > 0` is a natural number such that the chromatic number of the
simple graph `H` equals `r+1`. The Turán density of `H` equals `1-1/r`.

This is a corollary of the *Erdős-Stone-Simonovits theorem*. -/
theorem turanDensity_eq_of_chromaticNumber
    {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r+1) :
    turanDensity H = 1-1/r :=
  Filter.Tendsto.limUnder_eq
    (tendsto_extremalNumber_div_choose_two_of_chromaticNumber hr_pos hχ)

/-- Suppose `r > 1` is a natural number such that the chromatic number of the
simple graph `H` equals `r+1`. The extremal number `extremalNumber (Fin n) H`
is asymptotically equivalent to `(1-1/r)*(n.choose 2)` at infinity.

This is a corollary of the *Erdős-Stone-Simonovits theorem*. -/
theorem isEquivalent_extremalNumber_of_chromaticNumber
    {r : ℕ} (hr : 1 < r) (hχ : H.chromaticNumber = r+1) :
    (fun (n : ℕ) ↦ (extremalNumber (Fin n) H : ℝ))
      ~[Filter.atTop] (fun (n : ℕ) ↦ ((1-1/r)*(n.choose 2) : ℝ)) := by
  have hπ : turanDensity H = 1-1/r :=
    turanDensity_eq_of_chromaticNumber (hr.trans' zero_lt_one) hχ
  have hπ_pos : 0 < turanDensity H := by
    rw [hπ]
    exact Nat.one_sub_one_div_cast_pos hr
  have h := isEquivalent_extremalNumber H hπ_pos.ne'
  simpa [hπ] using h
