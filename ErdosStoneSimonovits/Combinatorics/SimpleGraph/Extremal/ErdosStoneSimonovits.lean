import Mathlib
import ErdosStoneSimonovits.Analysis.SpecialFunctions.Choose
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Bipartite
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Equipartite
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.TuranDensity
import ErdosStoneSimonovits.Data.Finset.Union
import ErdosStoneSimonovits.Data.Nat.Cast.Order.Field
import ErdosStoneSimonovits.Data.Nat.Defs

open Asymptotics Filter Finset Fintype Real Topology

namespace SimpleGraph

section ErdosStone

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
  {ε : ℝ} {r t t' : ℕ} (A : G.completeEquipartiteSubgraph r t')

local notation "K" => A.verts

/-- `W` is the set of vertices in the complement of a complete equipartite subgraph,
in `r` parts each of size `t'`, adjacent to at least `t` vertices in each part of the complete
equipartite subgraph.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
private abbrev aux (t : ℕ) : Finset V :=
  { v ∈ Kᶜ | ∀ i : Fin r, ∃ s : (A.parts i).val.powersetCard t, ∀ w ∈ s.val, G.Adj v w }

local notation "W" => aux A t

private lemma aux_subset_verts_compl : W ⊆ Kᶜ := by apply filter_subset

omit [DecidableRel G.Adj] in
private lemma between_verts_isBipartiteWith : (G.between K Kᶜ).IsBipartiteWith K ↑Kᶜ := by
  rw [coe_compl K]
  exact between_isBipartiteWith (disjoint_compl_right)

private lemma le_card_edgeFinset_between_verts :
    (#K*(G.minDegree-#K) : ℝ) ≤ #(G.between K Kᶜ).edgeFinset := by
  rw [← isBipartiteWith_sum_degrees_eq_card_edges (between_verts_isBipartiteWith A),
    ← nsmul_eq_mul, ← sum_const, Nat.cast_sum]
  apply sum_le_sum; intro v hv
  rw [sub_le_iff_le_add]
  exact_mod_cast (minDegree_le_degree G v).trans (degree_le_between_plus hv)

/-- For `v ∈ Kᶜ\W`, since `v` is adjacent to fewer than `t` vertices in at least one part of the
complete equipartite subgraph, it follows that `v` is adjacent to fewer than `#K-(t'-t)` vertices
in `K`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
private lemma degree_between_verts_lt_of_mem_sdiff {v : V} (hv : v ∈ Kᶜ\W) :
    (G.between K Kᶜ).degree v < #K-t'+t := by
  rw [mem_sdiff, mem_filter] at hv
  push_neg at hv
  have ⟨i, hs⟩ := hv.2 hv.1
  rw [← card_neighborFinset_eq_degree,
    isBipartiteWith_neighborFinset' (between_verts_isBipartiteWith A) hv.1,
    filter_disjiUnion, card_disjiUnion, ← union_compl {i}, union_comm,
    sum_union disjoint_compl_left, sum_singleton]
  apply add_lt_add_of_le_of_lt
  · conv_rhs =>
      rw [A.card_verts, ← Nat.sub_one_mul,  ← Fintype.card_fin r, ← card_singleton i,
        ← card_compl, ← smul_eq_mul, ← sum_const]
      enter [2, j]
      rw [← A.card_parts j]
    apply sum_le_sum
    intros
    apply card_filter_le
  · contrapose! hs
    obtain ⟨s, hs⟩ := by
      rwa [← powersetCard_nonempty] at hs
    have hs' : s ∈  (A.parts i).val.powersetCard t := by
      apply powersetCard_mono _ hs
      exact filter_subset _ (A.parts i).val
    use ⟨s, hs'⟩
    intro w hw
    obtain ⟨_, hadj, _⟩ := by
      rw [mem_powersetCard] at hs
      apply hs.1 at hw
      rwa [mem_filter, between_adj] at hw
    exact hadj.symm

private lemma card_edgeFinset_between_verts_le (hr : 0 < r) :
    (#(G.between K Kᶜ).edgeFinset : ℝ) ≤ ((card V)-#K)*(#K-(t'-t)) + #W*(t'-t) :=
  calc (#(G.between K Kᶜ).edgeFinset : ℝ)
    _ = ∑ v ∈ Kᶜ\W, ((G.between K Kᶜ).degree v : ℝ)
          + ∑ v ∈ W, ((G.between K Kᶜ).degree v : ℝ) := by
        rw [sum_sdiff (filter_subset _ Kᶜ), eq_comm]
        exact_mod_cast isBipartiteWith_sum_degrees_eq_card_edges' (between_verts_isBipartiteWith A)
    _ ≤ ∑ _ ∈ Kᶜ\W, (#K-t'+t : ℝ) + ∑ _ ∈ W, (#K : ℝ) := by
        apply add_le_add
        · apply sum_le_sum; intro v hv
          rw [← Nat.cast_sub]
          · exact_mod_cast (degree_between_verts_lt_of_mem_sdiff A hv).le
          · rw [A.card_verts]
            apply Nat.le_mul_of_pos_left t' hr
        · apply sum_le_sum; intro v hv
          exact_mod_cast isBipartiteWith_degree_le'
            (between_verts_isBipartiteWith A) (aux_subset_verts_compl A hv)
    _ = ((card V)-#K)*(#K-(t'-t)) + #W*(t'-t) := by
        simp_rw [sum_const, card_sdiff (aux_subset_verts_compl A), nsmul_eq_mul,
          Nat.cast_sub (card_le_card (aux_subset_verts_compl A)), card_compl,
          Nat.cast_sub (card_le_univ K)]
        ring_nf

private lemma card_aux_ge (hr : 0 < r) :
    (#K*(G.minDegree-#K)-((card V)-#K)*(#K-(t'-t)) : ℝ) ≤ (#W*(t'-t) : ℝ) :=
  sub_left_le_of_le_add <| (le_card_edgeFinset_between_verts A).trans
    (card_edgeFinset_between_verts_le A hr)

/-- `#W` is arbitrarily large with respect to `card V`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
private lemma card_aux_ge_of_minDegree (hr : 0 < r)
    (hδ : G.minDegree ≥ (1-1/r+ε)*(card V))
    {x : ℕ} (hx : (x+r*t')*(t'-t) ≤ (card V)*(t'*r*ε-t)) :
    (x*(t'-t) : ℝ) ≤ (#W*(t'-t) : ℝ) := by
  calc (x*(t'-t) : ℝ)
    _ ≤ (card V)*(t'*r*ε-t)-r*t'*(t'-t) := by
        rw [← add_sub_cancel_right (x : ℝ) (r*t' : ℝ), sub_mul]
        apply sub_le_sub_right hx
    _ = #K*((1-1/r+ε)*(card V)-#K)-((card V)-#K)*(#K-(t'-t)) := by
        rw [A.card_verts]
        field_simp
        ring_nf
    _ ≤ #K*(G.minDegree-#K)-((card V)-#K)*(#K-(t'-t)) := by
        apply sub_le_sub_right
        apply mul_le_mul_of_nonneg_left _ (#K).cast_nonneg
        apply sub_le_sub_right hδ
    _ ≤ #W*(t'-t) := by
        apply sub_left_le_of_le_add
        exact (le_card_edgeFinset_between_verts A).trans
          (card_edgeFinset_between_verts_le A hr)

/-- For `w ∈ W`, there exists a `r` subets of vertices of size `t < t'` adjacent to `w`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
private noncomputable abbrev aux.Pi :
    W → Π i : Fin r, powersetCard t (A.parts i).val := by
  intro ⟨w, hw⟩ i
  rw [mem_filter] at hw
  exact (hw.2 i).choose

local notation "F" => aux.Pi A

private lemma aux.Pi_mem_val (w : W) (i : Fin r) :
    ∀ v ∈ (F w i).val, G.Adj w v := by
  have hw := w.prop
  rw [mem_filter] at hw
  exact (hw.2 i).choose_spec

/-- For `y = F ·`, there exists a complete equipartite subgraph in `r` parts of size `t < t'`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
private noncomputable abbrev aux.completeEquipartiteSubgraph
    (y : Π i : Fin r, powersetCard t (A.parts i).val) :
    G.completeEquipartiteSubgraph r t where
  parts i := by
    use (y i).val
    have hyi := mem_powersetCard.mp (y i).prop
    simpa using hyi.2
  Adj i j h v hv w hw := by
    have hyi := mem_powersetCard.mp (y i).prop
    have hyj := mem_powersetCard.mp (y j).prop
    exact A.Adj h v (hyi.1 hv) w (hyj.1 hw)

include A in
/-- If `#W` is sufficently large, then there exist at least `t` vertices adjacent to the vertices
of a complete equipartite subgraph in `r` parts each of size `t < t'`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
private lemma exists_completeEquipartiteSubgraph_powersetCard (hr : 0 < r)
    (ht_lt_t' : t < t') (hδ : G.minDegree ≥ (1-1/r+ε)*(card V))
    (hx : ((t'.choose t)^r*t+r*t')*(t'-t) ≤ (card V)*(t'*r*ε-t)) :
    ∃ (A : G.completeEquipartiteSubgraph r t) (s : univ.powersetCard t),
      ∀ v₁ ∈ s.val, ∀ i, ∀ v₂ ∈ (A.parts i).val, G.Adj v₁ v₂ := by
  have ht_sub_t'_pos :  0 < (t'-t : ℝ) := sub_pos_of_lt (mod_cast ht_lt_t')
  have ⟨y, hy⟩ : ∃ y : Π i : Fin r, powersetCard t (A.parts i).val,
      t ≤ #(univ.filter (F · = y)) := by
    haveI : Nonempty (Π i : Fin r, powersetCard t (A.parts i).val) := by
      simpa only [Fintype.card_fin, Classical.nonempty_pi, nonempty_coe_sort,
        powersetCard_nonempty, A.card_parts] using Function.const (Fin r) ht_lt_t'.le
    apply exists_le_card_fiber_of_mul_le_card
    simp_rw [Fintype.card_pi, card_coe, card_powersetCard,
      A.card_parts, prod_const, card_univ, Fintype.card_fin]
    rw [← @Nat.cast_le ℝ, ← mul_le_mul_right ht_sub_t'_pos]
    apply card_aux_ge_of_minDegree A hr hδ (mod_cast hx)
  have ⟨s', hs'⟩ := exists_subset_card_eq hy
  let s : univ.powersetCard t := by
    use s'.map (Function.Embedding.subtype (· ∈ W))
    simpa using hs'.2
  use aux.completeEquipartiteSubgraph A y, s
  intro v hv i w hw
  let v' : W := ⟨v, property_of_mem_map_subtype s' hv⟩
  have hv' : v' ∈ s' := by
    rw [Finset.mem_map] at hv
    convert hv.choose_spec.1
    rw [Subtype.ext_iff]
    exact hv.choose_spec.2.symm
  apply aux.Pi_mem_val A v' i w
  replace hv' := hs'.1 hv'
  rw [mem_filter] at hv'
  rw [hv'.2]
  exact hw

/-- If `G` has a minimal degree of at least `(1-1/r+o(1))*(card V)`, then `G` contains a copy of
a `completeEquipartiteGraph` in `r+1` parts each of size `t`.

This is the minimal-degree version of the **Erdős-Stone theorem**. -/
theorem completeEquipartiteGraph_isContained_of_minDegree {ε : ℝ} (hε : 0 < ε) (r t : ℕ) :
    ∃ n, ∀ {V : Type*} [Fintype V] [DecidableEq V], n < card V →
      ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
        G.minDegree ≥ (1-1/r+ε)*(card V)
          → completeEquipartiteGraph (r+1) t ⊑ G := by
  rcases show (r = 0 ∨ t = 0) ∨ r ≠ 0 ∧ t ≠ 0 by tauto with h | ⟨hr, ht⟩
  · rw [← Nat.le_zero_eq, ← @Nat.add_le_add_iff_right r 0 1, zero_add] at h
    use (r+1)*t
    intro _ _ _ h_card _ _ _
    rw [completeEquipartiteGraph_eq_bot_iff.mpr h, bot_isContained_iff_card_le]
    simpa using h_card.le
  · rw [← Nat.pos_iff_ne_zero] at hr ht
    -- choose `ε'` to ensure `δ(G)` is large enough
    let ε' := 1/(↑(r-1)*r) + ε
    have hε' : 0 < ε' := by positivity
    -- choose `t'` larger than `t/(r*ε)`
    let t' := ⌊t/(r*ε)⌋₊ + 1
    have ht_lt_t'rε : t < t'*r*ε := by
      rw [mul_assoc, ← div_lt_iff₀ (by positivity), Nat.cast_add_one]
      exact Nat.lt_floor_add_one (t/(r*ε))
    have ht' : 0 < t' := by positivity
    haveI : NeZero t' := ⟨ht'.ne'⟩
    have ⟨n', ih⟩ := completeEquipartiteGraph_isContained_of_minDegree hε' (r-1) t'
    -- choose `n` at least `((t'.choose t)^r*t+r*t')*(t'-t)/(t'*r*ε-t)` for pigeonhole principle
    let n := max n' ⌈((t'.choose t)^r*t+r*t')*(t'-t)/(t'*r*ε-t)⌉₊
    use n
    intro V _ _ h_cardV G _ hδ
    haveI : Nonempty V := card_pos_iff.mp (n.zero_le.trans_lt h_cardV)
    -- `r` is less than `1/ε` otherwise δ(G) = v(G)
    have hrε_lt_1 : r*ε < 1 := by
      have hδ_lt_card : (G.minDegree : ℝ) < (card V : ℝ) := mod_cast G.minDegree_lt_card
      contrapose! hδ_lt_card with h1_le_rε
      rw [← div_le_iff₀' (by positivity), ← sub_nonpos,
        ← le_sub_self_iff 1, ← sub_add] at h1_le_rε
      exact hδ.trans' (le_mul_of_one_le_left (card V).cast_nonneg h1_le_rε)
    have ht_lt_t' : t < t' := by
      rw [← @Nat.cast_lt ℝ]
      apply ht_lt_t'rε.trans
      rw [mul_assoc]
      exact mul_lt_of_lt_one_right (mod_cast ht') hrε_lt_1
    -- find `completeEquipartiteGraph` from inductive hypothesis
    replace ih : completeEquipartiteGraph r t' ⊑ G := by
      rcases eq_or_ne r 1 with hr_eq_1 | hr_ne_1
      · rw [completeEquipartiteGraph_eq_bot_iff.mpr (Or.inl hr_eq_1.le),
          bot_isContained_iff_card_le]
        simp_rw [card_prod, Fintype.card_fin, hr_eq_1, one_mul]
        apply h_cardV.le.trans'
        exact_mod_cast calc (t' : ℝ)
        _ ≤ r*t' := le_mul_of_one_le_left (by positivity) (mod_cast hr)
        _ ≤ (t'.choose t)^r*t + r*t' := le_add_of_nonneg_left (by positivity)
        _ ≤ ((t'.choose t)^r*t + r*t')*(t'-t)/(t'*r*ε-t) := by
            rw [mul_div_assoc, le_mul_iff_one_le_right (by positivity),
              one_le_div (sub_pos.mpr ht_lt_t'rε), sub_le_sub_iff_right, mul_assoc,
              mul_le_iff_le_one_right (by positivity)]
            exact hrε_lt_1.le
        _ ≤ ⌈((t'.choose t)^r*t + r*t')*(t'-t)/(t'*r*ε-t)⌉₊ := Nat.le_ceil _
        _ ≤ n := Nat.cast_le.mpr (le_max_right n' _)
      · have hδ' := calc (G.minDegree : ℝ)
          _ ≥ (1-1/(r-1)+(1/(r-1)-1/r)+ε)*(card V) := by rwa [← sub_add_sub_cancel] at hδ
          _ = (1-1/↑(r-1)+ε')*(card V) := by
              rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
                  (sub_ne_zero.mpr (mod_cast hr_ne_1)) (mod_cast hr.ne'), sub_sub_cancel, mul_one,
                one_div_mul_one_div_rev, mul_comm (r : ℝ), ← Nat.cast_pred hr, add_assoc]
        rw [← Nat.succ_pred_eq_of_pos hr]
        exact ih (h_cardV.trans_le' (le_max_left n' _)) hδ'
    obtain ⟨A⟩ := by rwa [completeEquipartiteGraph_isContained_iff] at ih
    -- find `completeEquipartiteGraph` from pigeonhole principle
    rw [completeEquipartiteGraph_succ_isContained_iff]
    obtain ⟨A', s, hs⟩ := by
      apply exists_completeEquipartiteSubgraph_powersetCard A hr ht_lt_t' hδ
      rw [← div_le_iff₀ (sub_pos.mpr ht_lt_t'rε)]
      trans (n : ℝ)
      · apply (Nat.le_ceil _).trans <| Nat.cast_le.mpr (le_max_right n' _)
      · exact_mod_cast h_cardV.le
    use A', s, hs

/-- Repeatedly remove minimal degree vertices until `(G.induce s).minDegree` is
at least `c * #s`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
private lemma exists_induced_subgraph_for_minDegree {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ s : Finset V, (s : Set V) ⊆ G.support ∧
      c*#s ≤ (G.induce s).minDegree ∧
      #(G.induce s).edgeFinset ≥ #G.edgeFinset
        -c*(card G.support^2-#s^2)/2-c*(card G.support-#s)/2 := by
  by_cases hδ : c*#G.support.toFinset ≤ (G.induce G.support.toFinset).minDegree
  · refine ⟨G.support.toFinset, by simp, hδ, ?_⟩
    suffices h_card_edges : #(G.induce G.support).edgeFinset ≥ #G.edgeFinset
        -c*(card G.support^2-#G.support.toFinset^2)/2-c*(card G.support-#G.support.toFinset)/2 by
      convert h_card_edges
      all_goals simp
    rw [card_edgeFinset_induce_support, ← Set.toFinset_card G.support]
    ring_nf; rfl
  · replace hδ : (G.induce G.support).minDegree < c*(card G.support) := by
      push_neg at hδ
      convert hδ
      all_goals simp
    have h_card_support_pos : 0 < card G.support := by
      contrapose! hδ
      rw [Nat.eq_zero_of_le_zero hδ, Nat.cast_zero, mul_zero]
      exact Nat.cast_nonneg (G.induce G.support).minDegree
    haveI : Nonempty G.support := card_pos_iff.mp h_card_support_pos
    -- delete minimal degree vertex
    have ⟨x, hδ_eq_degx⟩ := exists_minimal_degree_vertex (G.induce G.support)
    let G' := G.deleteIncidenceSet ↑x
    have ⟨s, hs', ihδ', ih_card_edges'⟩ :=
      exists_induced_subgraph_for_minDegree hc₀ hc₁ G'
    have ⟨hs, hx_not_mem⟩ : (s : Set V) ⊆ G.support ∧ ↑x ∉ (s : Set V) := by
      rw [← Set.disjoint_singleton_right, ← Set.subset_diff]
      exact hs'.trans (G.deleteIncidenceSet_support_subset ↑x)
    have ihδ : c*#s ≤ (G.induce s).minDegree := by
      simpa [← deleteIncidenceSet_induce_of_not_mem G hx_not_mem] using ihδ'
    have ih_card_edges : #(G.induce s).edgeFinset ≥ #G'.edgeFinset
        -c*((card G'.support)^2-#s^2)/2-c*((card G'.support)-#s)/2 := by
      simpa [sub_sub, Set.toFinset_card,
        ← G.deleteIncidenceSet_induce_of_not_mem hx_not_mem] using ih_card_edges'
    refine ⟨s, hs, ihδ, ?_⟩
    calc (#(G.induce s).edgeFinset : ℝ)
      _ ≥ #G'.edgeFinset-(c*((card G'.support)^2-#s^2)/2+c*(card G'.support-#s)/2) := by
          rwa [sub_sub] at ih_card_edges
      _ ≥ (#G.edgeFinset-c*(card G.support))
            -(c*((card G.support-1)^2-#s^2)/2+c*(card G.support-1-#s)/2) := by
          apply sub_le_sub
          -- exactly `G.minDegree` edges are deleted from the edge set
          · rw [G.card_edgeFinset_deleteIncidenceSet ↑x,
              Nat.cast_sub (G.degree_le_card_edgeFinset x),
              ← degree_induce_support, ← hδ_eq_degx]
            exact sub_le_sub_left hδ.le #G.edgeFinset
          -- at least 1 vertex is deleted from the support
          · rw [← add_div, ← add_div, div_le_div_iff_of_pos_right zero_lt_two]
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left _ hc₀
              rw [sub_le_sub_iff_right]
              apply pow_le_pow_left₀ (Nat.cast_nonneg (card G'.support))
              rw [← Nat.cast_pred card_pos]
              exact_mod_cast G.card_support_deleteIncidenceSet x.prop
            · apply mul_le_mul_of_nonneg_left _ hc₀
              rw [sub_le_sub_iff_right, ← Nat.cast_pred card_pos]
              exact_mod_cast G.card_support_deleteIncidenceSet x.prop
      _ ≥ #G.edgeFinset-c*((card G.support)^2-#s^2)/2-c*(card G.support-#s)/2 := by linarith
termination_by card G.support
decreasing_by
  exact (G.card_support_deleteIncidenceSet x.prop).trans_lt
    (Nat.pred_lt_of_lt h_card_support_pos)

/-- Repeatedly remove minimal degree vertices until `(G.induce s).minDegree` is
at least `c*#s` and `#s ≈ √ε * (card V)` when `c ≈ 0`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
private lemma exists_induced_subgraph_for_minDegree_for_card_sq
    {c ε : ℝ} (hc₀ : 0 ≤ c) (hε : 0 ≤ ε) (h : #G.edgeFinset ≥ (c+ε)*(card V)^2/2) :
    ∃ s : Finset V, c*#s ≤ (G.induce s).minDegree ∧ ε*(card V)^2-c*(card V) ≤ #s^2 := by
  rcases isEmpty_or_nonempty V
  · use ∅
    simp
  · have hc₁ : c ≤ 1 := by
      by_contra! hc₁
      absurd calc ((card V)^2/2 : ℝ)
        _ < (c+ε)*(card V)^2/2 := by
            apply div_lt_div_of_pos_right _ zero_lt_two
            apply lt_mul_of_one_lt_left (by positivity)
            exact hc₁.trans_le (le_add_of_nonneg_right hε)
        _ ≤ #G.edgeFinset := h
      push_neg
      calc (#G.edgeFinset : ℝ)
        _ ≤ (card V)*(card V-1)/2 := by
            rw [← Nat.cast_choose_two]
            exact_mod_cast card_edgeFinset_le_card_choose_two
        _ ≤ (card V)^2/2 := by
            rw [div_le_div_iff_of_pos_right zero_lt_two]
            nlinarith
    have ⟨s, _, hδ, hs⟩ := exists_induced_subgraph_for_minDegree hc₀ hc₁ G
    rw [ge_iff_le, sub_sub, sub_le_iff_le_add] at hs
    use s, hδ
    rw [← div_le_div_iff_of_pos_right zero_lt_two, sub_div]
    calc ε*(card V)^2/2-c*(card V)/2
      _ = (c+ε)*(card V)^2/2-(c*(card V)^2/2+c*(card V)/2) := by ring_nf
      _ ≤ (#s*(#s-1)/2+(c*((card G.support)^2-#s^2)/2+c*(card G.support-#s)/2))
            -(c*(card V)^2/2+c*card V/2) := by
          apply sub_le_sub_right
          apply h.trans
          apply hs.trans
          apply add_le_add_right
          rw [← Nat.cast_choose_two, ← card_coe s]
          exact_mod_cast card_edgeFinset_le_card_choose_two
      _ = #s^2/2-(c*((card V)^2-(card G.support)^2)/2 + c*(card V-card G.support)/2
            +c*#s^2/2+c*#s/2+#s/2) := by ring_nf
      _ ≤ #s^2/2 := by
          apply sub_le_self
          repeat apply add_nonneg
          any_goals
            apply div_nonneg _ zero_le_two
            try apply mul_nonneg hc₀
            try apply sub_nonneg_of_le
            try apply pow_le_pow_left₀
            try positivity
            try exact_mod_cast set_fintype_card_le_univ G.support

/-- If `G` has at least `(1-1/r+o(1))*(card V)^2/2` many edges, then `G` contains a copy of
a `completeEquipartiteGraph` in `r+1` parts each of size `t`.

This is the **Erdős-Stone theorem**. -/
theorem completeEquipartiteGraph_isContained_of_card_edgeFinset {ε : ℝ} (hε : 0 < ε) (r t : ℕ) :
    ∃ n, ∀ {V : Type*} [Fintype V] [DecidableEq V], n < card V →
      ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
        #G.edgeFinset ≥ (1-1/r+ε)*(card V)^2/2
        → completeEquipartiteGraph (r+1) t ⊑ G := by
  -- choose `c + ε' = (1-1/r+ε/2) + ε/2 = 1-1/r+ε`
  let ε' := ε/2
  have hε' : 0 < ε' := by positivity
  let c := 1-1/r+ε/2
  have hc : 0 < c := add_pos_of_nonneg_of_pos r.one_sub_one_div_cast_nonneg hε'
  -- minimal-degree version of Erdős-Stone theorem
  have ⟨n', ih⟩ := completeEquipartiteGraph_isContained_of_minDegree hε' r t
  use ⌊c/ε'+n'/√ε'⌋₊
  intro V _ _ h_cardV G _ h
  rw [Nat.floor_lt (by positivity)] at h_cardV
  -- prove `s` satisfies conditions for minimal-degree version
  rw [← add_halves ε, ← add_assoc] at h
  obtain ⟨s, hδ, h_cards_sq⟩ := exists_induced_subgraph_for_minDegree_for_card_sq hc.le hε'.le h
  suffices h_cards : (n'^2 : ℝ) < (#s^2 : ℝ) by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_lt,
      Nat.pow_lt_pow_iff_left two_ne_zero] at h_cards
    -- find `completeEquipartiteGraph` from minimal-degree version
    simp_rw [← card_coe, ← Finset.coe_sort_coe] at h_cards hδ
    exact (ih h_cards hδ).trans ⟨Copy.induce G s⟩
  -- `x ↦ ε'*x^2-cx` is strictly monotonic on `[c/(2*ε'), ∞)`
  have h_strictMonoOn : StrictMonoOn (fun x ↦ ε'*x^2-c*x) (Set.Ici (c/(2*ε'))) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) (Continuous.continuousOn (by continuity))
    intro x hx
    rw [deriv_sub, deriv_const_mul, deriv_pow 2, Nat.cast_two, pow_one, ← mul_assoc ε' 2 x,
      mul_comm ε' 2, deriv_const_mul, deriv_id'', mul_one, sub_pos,
      ← div_lt_iff₀' (mul_pos two_pos hε')]
    rwa [interior_Ici, Set.mem_Ioi] at hx
    all_goals
      try apply DifferentiableAt.const_mul
      try apply DifferentiableAt.pow
      exact differentiableAt_id'
  calc (#s^2 : ℝ)
    _ ≥ ε'*(card V)^2-c*(card V) := h_cards_sq
    _ > ε'*(c/ε'+n'/√ε')^2-c*(c/ε'+n'/√ε') := by
        have h_le : c/(2*ε') ≤ c/ε'+n'/√ε' := by
          trans c/ε'
          · rw [mul_comm, ← div_div, half_le_self_iff]
            exact div_nonneg hc.le hε'.le
          · rw [le_add_iff_nonneg_right]
            exact div_nonneg n'.cast_nonneg (sqrt_nonneg ε')
        exact h_strictMonoOn h_le (h_le.trans (mod_cast h_cardV.le)) h_cardV
    _ = n'^2+n'*c/sqrt ε' := by
        rw [add_pow_two, mul_add, div_pow (n' : ℝ) √ε', sq_sqrt hε'.le,
          mul_div_cancel₀ _ hε'.ne', mul_add, pow_two (c/ε'), ← mul_assoc,
          mul_comm 2 (c/ε'), mul_assoc (c/ε') 2 _, ← mul_assoc, mul_div_cancel₀ _ hε'.ne']
        ring_nf
    _ ≥ n'^2 := le_add_of_nonneg_right (by positivity)

end ErdosStone

section ErdosStoneSimonovits

/-- If `ε > 2*r/n` then a `completeEquipartiteGraph` in `r` parts each of size `⌊n/r⌋` has
more than `(1-1/r-ε)*n^2/2` edges.

This is an auxiliary definition for the **Erdős-Stone-Simonovits theorem**. -/
lemma card_edgeFinset_completeEquipartiteGraph_gt {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    ∀ ε > (2*r/n : ℝ),
      (1-1/r-ε)*n^2/2 < #(completeEquipartiteGraph r (n/r)).edgeFinset := by
  let t := n/r
  intro ε hε
  rw [gt_iff_lt, div_lt_iff₀ (by positivity)] at hε
  calc (1-1/r-ε)*n^2/2
    _ < (1-1/r)*n^2/2-r*n := by
        rw [sub_mul, sub_div, sub_lt_sub_iff_left, lt_div_iff₀ zero_lt_two,
          mul_comm, ← mul_assoc, pow_two, ← mul_assoc]
        exact mul_lt_mul_of_pos_right hε (mod_cast hn)
    _ = (1-1/r)*r^2*t^2/2-(r*n-(1-1/r)*(n*↑(n%r))+(1-1/r)*↑(n % r)^2/2) := by
        conv_lhs =>
          lhs; rw [← n.div_add_mod r, Nat.cast_add, add_sq, add_assoc, mul_add, add_div]
          lhs; rw [Nat.cast_mul, mul_pow, ← mul_assoc]
        rw [← Nat.sub_mod_eq_mul_div, Nat.cast_sub (n.mod_le r)]
        ring_nf
    _ ≤ (1-1/r)*r^2*t^2/2 := by
        apply sub_le_self
        apply add_nonneg
        · rw [sub_nonneg, ← mul_assoc, mul_comm (r : ℝ) (n : ℝ)]
          apply mul_le_mul _ (mod_cast (n.mod_lt hr).le) (n%r).cast_nonneg (mod_cast hn.le)
          rw [mul_le_iff_le_one_left (mod_cast hn)]
          exact r.one_sub_one_div_cast_le_one
        · apply div_nonneg _ zero_le_two
          exact mul_nonneg (r.one_sub_one_div_cast_nonneg) (by positivity)
    _ = #(completeEquipartiteGraph r t).edgeFinset := by
        simp_rw [card_edgeFinset_completeEquipartiteGraph,
          Nat.cast_mul, Nat.cast_pow, Nat.cast_choose_two]
        field_simp
        ring_nf

variable {W : Type*} [Fintype W] {H : SimpleGraph W}

omit [Fintype W] in
lemma lt_extremalNumber_of_not_colorable {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : 0 < r) (nhc : ¬H.Colorable r) :
    ∃ n, ∀ {V : Type*} [Fintype V] [DecidableEq V], n < card V →
      (1-1/r-ε)*(card V)^2/2 < extremalNumber (card V) H := by
  use ⌈2*r/ε⌉₊
  intro V _ _ h_cardV
  haveI : Nonempty V := by
    rw [← card_pos_iff]
    exact Nat.zero_lt_of_lt h_cardV
  have hε' : 2*r/card V < ε := by
    rw [div_lt_iff₀ (by positivity), ←div_lt_iff₀' hε]
    exact (Nat.le_ceil _).trans_lt (mod_cast h_cardV)
  let t := card V/r
  let G : SimpleGraph (Fin r × Fin t) := completeEquipartiteGraph r t
  -- `completeEquipartiteGraph` is `r`-colorable
  haveI : Nonempty (Fin r × Fin t ↪ V) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa [card_prod, Fintype.card_fin] using (card V).mul_div_le r
  let f := Classical.arbitrary (Fin r × Fin t ↪ V)
  -- `completeEquipartiteGraph` has the right amount of edges
  have h_card_edges : #G.edgeFinset > (1-1/r-ε)*(card V)^2/2 :=
    card_edgeFinset_completeEquipartiteGraph_gt hr card_pos ε hε'
  rw [← G.card_edgeFinset_map f] at h_card_edges
  apply lt_of_lt_of_le h_card_edges
  rw [Nat.cast_le]
  -- `completeEquipartiteGraph` does not contain `H`
  apply le_extremalNumber
  haveI : NeZero r := ⟨hr.ne'⟩
  exact free_of_colorable nhc (completeEquipartiteGraph_colorable.map f)

lemma extremalNumber_le_of_colorable {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hc : H.Colorable (r+1)) :
    ∃ n, ∀ {V : Type*} [Fintype V] [DecidableEq V], n < card V →
      extremalNumber (card V) H ≤ (1-1/r+ε)*(card V)^2/2 := by
  have ⟨t, h_isContained_lhs⟩ := isContained_completeEquipartiteGraph_of_colorable hc
  have ⟨n, h_isContained_rhs⟩ := completeEquipartiteGraph_isContained_of_card_edgeFinset hε r t
  use n; intro V _ _ h_cardV
  trans (extremalNumber (card V) (completeEquipartiteGraph (r+1) t) : ℝ)
  -- `completeEquipartiteGraph` contains `H`
  · exact_mod_cast extremalNumber_of_isContained h_isContained_lhs
  -- `G` contains `completeEquipartiteGraph`
  · have h : 0 ≤ (1-1/r+ε)*(card V)^2/2 := by
      apply div_nonneg _ zero_le_two
      apply mul_nonneg _ (by positivity)
      exact add_nonneg (Nat.one_sub_one_div_cast_nonneg r) hε.le
    rw [extremalNumber_le_iff_of_nonneg _ h]
    intro _ _ h
    contrapose! h
    rw [not_free]
    exact h_isContained_rhs h_cardV h.le

/-- If the chromatic number of `H` equals `r+1 > 0`, then `extremalNumber` of `H` is greater
than `(1-1/r-o(1))*(card V)^2/2` and at most `(1-1/r+o(1))*(card V)^2/2`.

This is the **Erdős-Stone-Simonovits theorem**. -/
theorem lt_extremalNumber_le_of_chromaticNumber {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : 0 < r) (hχ : H.chromaticNumber = r+1) :
    ∃ n, ∀ {V : Type*} [Fintype V] [DecidableEq V], n < card V →
      (1-1/r-ε)*(card V)^2/2 < extremalNumber (card V) H ∧
      extremalNumber (card V) H ≤ (1-1/r+ε)*(card V)^2/2 := by
  have ⟨hc, nhc⟩ := chromaticNumber_eq_iff_colorable_not_colorable.mp hχ
  have ⟨n₁, h₁⟩ := lt_extremalNumber_of_not_colorable hε hr nhc
  have ⟨n₂, h₂⟩ := extremalNumber_le_of_colorable hε hc
  use max n₁ n₂; intro V _ _ h_cardV
  have h_cardV₁ := h_cardV.trans_le' (Nat.le_max_left n₁ n₂)
  have h_cardV₂ := h_cardV.trans_le' (Nat.le_max_right n₁ n₂)
  exact ⟨h₁ h_cardV₁, h₂ h_cardV₂⟩

/-- If the chromatic number of `H` equals `r+1 > 0`, then the `extremalNumber` of `H` is equal
to `(1-1/r+o(1))*n^2/2`.

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem isLittleO_extremalNumber_of_chromaticNumber
    {r : ℕ} (hr : 0 < r) (hχ : H.chromaticNumber = r+1) :
    (fun (n : ℕ) ↦ (extremalNumber n H-(1-1/r)*n^2/2 : ℝ))
      =o[atTop] (fun (n : ℕ) ↦ (n^2 : ℝ)) := by
  rw [isLittleO_iff]
  intro ε hε
  rw [eventually_atTop]
  have ⟨n₀, h⟩ := lt_extremalNumber_le_of_chromaticNumber hε hr hχ
  use n₀ + 1; intro n (hn : n₀ < n)
  rw [← Fintype.card_fin n] at hn
  specialize h hn
  rw [Fintype.card_fin] at h
  rw [norm_eq_abs, ← abs_of_pos hε, norm_eq_abs, ← abs_mul, ← sq_le_sq]
  apply sq_le_sq'
  all_goals linarith

/-- If the chromatic number of `H` equals `r+1 > 0`, then the limit
`extremalNumber n H / n.choose 2` approaches `1-1/r` as `n → ∞`.

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem tendsto_extremalNumber_div_choose_two_of_chromaticNumber
    {r : ℕ} (hr : 0 < r) (hχ : H.chromaticNumber = r+1) :
    Tendsto (fun (n : ℕ) ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop (𝓝 (1-1/r)) := by
  have hz : ∀ᶠ (n : ℕ) in atTop, (n.choose 2 : ℝ) ≠ 0 := by
    rw [eventually_atTop]
    use 2; intro n hn
    exact_mod_cast (Nat.choose_pos hn).ne'
  have h_tendsto : Tendsto (fun (n : ℕ) ↦ ((n^2/2)/(n.choose 2) : ℝ)) atTop (𝓝 1) := by
    simpa [isEquivalent_iff_tendsto_one hz] using (isEquivalent_choose 2).symm
  have h_littleo := IsLittleO.trans_isTheta
    (isLittleO_extremalNumber_of_chromaticNumber hr hχ) (isTheta_choose 2).symm
  simpa [sub_div, ← mul_div]
    using h_littleo.tendsto_div_nhds_zero.add (h_tendsto.const_mul (1-1/r : ℝ))

/-- If the chromatic number of `H` equals `r+1 > 0`, then the Turán density of `H`
equals `1-1/r`.

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem turanDensity_eq_of_chromaticNumber
    {r : ℕ} (hr : 0 < r) (hχ : H.chromaticNumber = r+1) : turanDensity H = 1-1/r :=
  Tendsto.limUnder_eq (tendsto_extremalNumber_div_choose_two_of_chromaticNumber hr hχ)

/-- If the chromatic number of `H` equals `r+1 > 1`, then `extremalNumber n H` is
asymptotically equivalent to `(1-1/r)*(n.choose 2)` as `n → ∞`

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem isEquivalent_extremalNumber_of_chromaticNumber
    {r : ℕ} (hr : 1 < r) (hχ : H.chromaticNumber = r+1) :
    (fun (n : ℕ) ↦ (extremalNumber n H : ℝ))
      ~[atTop] (fun (n : ℕ) ↦ ((1-1/r)*(n.choose 2) : ℝ)) := by
  have hπ_eq : turanDensity H = 1-1/r := turanDensity_eq_of_chromaticNumber (by positivity) hχ
  have hπ_pos : 0 < turanDensity H := by
    rw [hπ_eq, sub_pos, one_div]
    exact inv_lt_one_of_one_lt₀ (mod_cast hr)
  simpa [hπ_eq] using isEquivalent_extremalNumber hπ_pos.ne'

end ErdosStoneSimonovits

end SimpleGraph
