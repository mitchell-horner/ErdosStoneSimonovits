import Mathlib
import ErdosStoneSimonovits.Analysis.SpecialFunctions.Choose
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Bipartite
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.CompleteEquipartite
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.TuranDensity
import ErdosStoneSimonovits.Data.Finset.Union
import ErdosStoneSimonovits.Data.Nat.Cast.Order.Field

open Asymptotics Filter Finset Fintype Real Topology

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {W : Type*} [Fintype W] {H : SimpleGraph W}

section ErdosStone

namespace ErdosStone

variable {ε : ℝ} {r t t' : ℕ} (A : G.CompleteEquipartiteSubgraph r t')

/-- `filterComplVertsAdjParts` is the set of vertices in the complement of a complete equipartite
subgraph, in `r` parts each of size `t'`, adjacent to at least `t` vertices in each part of the
complete equipartite subgraph.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
abbrev filterComplVertsAdjParts (t : ℕ) : Finset V :=
  { v ∈ A.vertsᶜ | ∀ i : Fin r, ∃ s ∈ (A.parts i).powersetCard t, ∀ w ∈ s, G.Adj v w }

theorem filterComplVertsAdjParts_subset_compl_verts : filterComplVertsAdjParts A t ⊆ A.vertsᶜ :=
  filter_subset _ A.vertsᶜ

omit [DecidableRel G.Adj] in
theorem between_verts_isBipartiteWith :
    (G.between A.verts A.vertsᶜ).IsBipartiteWith A.verts ↑A.vertsᶜ := by
  rw [coe_compl A.verts]
  exact between_isBipartiteWith (disjoint_compl_right)

lemma le_card_edgeFinset_between_verts :
    (#A.verts * (G.minDegree - #A.verts) : ℝ) ≤ #(G.between A.verts A.vertsᶜ).edgeFinset := by
  rw [← isBipartiteWith_sum_degrees_eq_card_edges (between_verts_isBipartiteWith A),
    ← nsmul_eq_mul, ← sum_const, Nat.cast_sum]
  exact sum_le_sum (fun v hv ↦ sub_le_iff_le_add.mpr <|
    mod_cast (G.minDegree_le_degree v).trans (degree_le_between_plus hv))

/-- For `v ∈ A.vertsᶜ \ filterComplVertsAdjParts`, since `v` is adjacent to fewer than `t`
vertices in at least one part of the complete equipartite subgraph, it follows that `v` is
adjacent to fewer than `#A.verts - (t' - t)` vertices in `A.verts`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
lemma degree_between_verts_lt_of_mem_sdiff
    {v : V} (hv : v ∈ A.vertsᶜ \ filterComplVertsAdjParts A t) :
    (G.between A.verts A.vertsᶜ).degree v < #A.verts - t' + t := by
  simp_rw [mem_sdiff, mem_filter, not_and_or, and_or_left, and_not_self_iff, false_or,
    not_forall, not_exists, not_and_or, not_forall, exists_prop] at hv
  obtain ⟨hv, i, hs⟩ := hv
  rw [← card_neighborFinset_eq_degree,
    isBipartiteWith_neighborFinset' (between_verts_isBipartiteWith A) hv,
    filter_disjiUnion, card_disjiUnion, sum_eq_sum_diff_singleton_add (mem_univ i)]
  apply add_lt_add_of_le_of_lt
  · conv_rhs =>
      rw [A.card_verts, ← Nat.sub_one_mul, ← Fintype.card_fin r,
        ← card_singleton i, ← card_compl, ← smul_eq_mul, ← sum_const]
      enter [2, j]
      rw [← A.card_parts j]
    exact sum_le_sum (fun _ _ ↦ card_filter_le _ _)
  · contrapose! hs
    obtain ⟨s, hs⟩ := powersetCard_nonempty.mpr hs
    have hs' : s ∈ (A.parts i).powersetCard t := powersetCard_mono (filter_subset _ _) hs
    refine ⟨s, hs', fun w hw ↦ ?_⟩
    obtain ⟨_, hadj, _⟩ := by
      rw [mem_powersetCard] at hs
      apply hs.1 at hw
      rwa [mem_filter, between_adj] at hw
    exact hadj.symm

lemma card_edgeFinset_between_verts_le (hr_pos : 0 < r) :
    (#(G.between A.verts A.vertsᶜ).edgeFinset : ℝ)
      ≤ (card V - #A.verts) * (#A.verts - (t' - t))
        + #(filterComplVertsAdjParts A t) * (t' - t) :=
  calc (#(G.between A.verts A.vertsᶜ).edgeFinset : ℝ)
    _ = ∑ v ∈ A.vertsᶜ \ filterComplVertsAdjParts A t, ((G.between A.verts A.vertsᶜ).degree v : ℝ)
      + ∑ v ∈ filterComplVertsAdjParts A t, ((G.between A.verts A.vertsᶜ).degree v : ℝ) := by
        rw [sum_sdiff (filter_subset _ A.vertsᶜ), eq_comm]
        exact_mod_cast isBipartiteWith_sum_degrees_eq_card_edges'
          (between_verts_isBipartiteWith A)
    _ ≤ ∑ _ ∈ A.vertsᶜ \ filterComplVertsAdjParts A t, (#A.verts - t' + t : ℝ)
      + ∑ _ ∈ filterComplVertsAdjParts A t, (#A.verts : ℝ) := by
        apply add_le_add <;> refine sum_le_sum (fun v hv ↦ ?_)
        · rw [← Nat.cast_sub ((Nat.le_mul_of_pos_left t' hr_pos).trans_eq A.card_verts.symm)]
          exact_mod_cast (degree_between_verts_lt_of_mem_sdiff A hv).le
        · exact_mod_cast isBipartiteWith_degree_le'
            (between_verts_isBipartiteWith A) (filterComplVertsAdjParts_subset_compl_verts A hv)
    _ = (card V - #A.verts) * (#A.verts - (t' - t))
      + #(filterComplVertsAdjParts A t) * (t' - t) := by
        rw [sum_const, nsmul_eq_mul, card_sdiff (filterComplVertsAdjParts_subset_compl_verts A),
          Nat.cast_sub (card_le_card (filterComplVertsAdjParts_subset_compl_verts A)), card_compl,
          Nat.cast_sub (card_le_univ A.verts), sum_const, nsmul_eq_mul, sub_mul,
          sub_add (#A.verts : ℝ) _ _, mul_sub (#(filterComplVertsAdjParts A t) : ℝ) _ _,
          ← sub_add, sub_add_eq_add_sub, sub_add_cancel]

/-- `#filterComplVertsAdjParts` is arbitrarily large with respect to `card V`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
theorem mul_le_card_filterComplVertsAdjParts_mul
    (hr_pos : 0 < r) (hδ : G.minDegree ≥ (1 - 1 / r + ε) * card V)
    {N : ℕ} (hN : (N + r * t') * (t' - t) ≤ card V * (r * t' * ε - t)) :
    (N * (t' - t) : ℝ) ≤ (#(filterComplVertsAdjParts A t) * (t' - t) : ℝ) :=
  calc (N * (t' - t) : ℝ)
    _ ≤ card V * (r * t' * ε - t) - r * t' * (t' - t) := by
        rw [← add_sub_cancel_right (N : ℝ) (r * t' : ℝ), sub_mul]
        exact sub_le_sub_right hN _
    _ = #A.verts * ((1 - 1 / r + ε) * card V - #A.verts)
      - (card V - #A.verts) * (#A.verts - (t' - t)) := by
        conv_rhs => rw [sub_eq_add_neg, ← neg_mul, neg_sub, sub_mul, mul_sub, ← add_sub_assoc,
          mul_sub, ← add_sub_assoc, sub_add_cancel, sub_right_comm, ← mul_assoc, ← mul_rotate,
          mul_assoc, ← mul_sub, mul_add, mul_sub (#A.verts : ℝ) _ _, mul_one,
          sub_add_eq_add_sub, add_sub_assoc, add_sub_sub_cancel, A.card_verts, Nat.cast_mul,
          mul_one_div, mul_div_cancel_left₀ (t' : ℝ) (mod_cast hr_pos.ne'), sub_add_sub_cancel]
    _ ≤ #A.verts * (G.minDegree - #A.verts) - (card V - #A.verts) * (#A.verts - (t' - t)) :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left
          (sub_le_sub_right hδ _) (#A.verts).cast_nonneg) _
    _ ≤ #(filterComplVertsAdjParts A t) * (t' - t) :=
        sub_left_le_of_le_add <|
          (le_card_edgeFinset_between_verts A).trans (card_edgeFinset_between_verts_le A hr_pos)

/-- For `w ∈ filterComplVertsAdjParts`, there exists a `r` subets of vertices of size `t < t'`
adjacent to `w`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
noncomputable abbrev filterComplVertsAdjParts.pi :
    filterComplVertsAdjParts A t → Π i : Fin r, (A.parts i).powersetCard t :=
  fun ⟨_, h⟩ i ↦
    let s := Multiset.of_mem_filter h i
    ⟨s.choose, s.choose_spec.1⟩

theorem filterComplVertsAdjParts.pi.mem_val (w : filterComplVertsAdjParts A t) (i : Fin r) :
    ∀ v ∈ (filterComplVertsAdjParts.pi A w i).val, G.Adj w v :=
  let s := Multiset.of_mem_filter w.prop i
  s.choose_spec.right

/-- If `#filterComplVertsAdjParts` is sufficently large, then there exist a `y` such that there
are least `t` vertices in the fiber `filterComplVertsAdjParts.pi A · = y`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
theorem filterComplVertsAdjParts.pi.exists_le_card_fiber
    (hr_pos : 0 < r) (ht_lt_t' : t < t') (hδ : G.minDegree ≥ (1 - 1 / r + ε) * card V)
    (hN : (t'.choose t ^ r * t + r * t') * (t' - t) ≤ card V * (r * t' * ε - t)) :
    ∃ y : Π i : Fin r, (A.parts i).powersetCard t,
      t ≤ #{ w | filterComplVertsAdjParts.pi A w = y } := by
  have : Nonempty (Π i : Fin r, (A.parts i).powersetCard t) := by
    simp_rw [Classical.nonempty_pi, nonempty_coe_sort, powersetCard_nonempty,
      A.card_parts, ht_lt_t'.le, implies_true]
  apply exists_le_card_fiber_of_mul_le_card
  simp_rw [Fintype.card_pi, card_coe, card_powersetCard, A.card_parts,
    prod_const, card_univ, Fintype.card_fin, ← @Nat.cast_le ℝ]
  apply le_of_mul_le_mul_right
  · exact mul_le_card_filterComplVertsAdjParts_mul A hr_pos hδ (mod_cast hN)
  · rwa [← @Nat.cast_lt ℝ, ← sub_pos] at ht_lt_t'

end ErdosStone

/-- If `G` has a minimal degree of at least `(1 - 1 / r + o(1)) * card V`, then `G` contains a
copy of a `completeEquipartiteGraph` in `r + 1` parts each of size `t`.

This is the minimal-degree version of the **Erdős-Stone theorem**. -/
theorem completeEquipartiteGraph_isContained_of_minDegree
    {ε : ℝ} (hε : 0 < ε) (r t : ℕ) :
    ∃ N, ∀ {V : Type*} [Fintype V], N ≤ card V →
      ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
        G.minDegree ≥ (1 - 1 / r + ε) * card V
          → completeEquipartiteGraph (r + 1) t ⊑ G := by
  rcases show (r = 0 ∨ t = 0) ∨ r ≠ 0 ∧ t ≠ 0 by tauto with h0 | ⟨hr_pos, ht_pos⟩
  · rw [← Nat.le_zero_eq, ← @Nat.add_le_add_iff_right r 0 1, zero_add] at h0
    refine ⟨(r + 1) * t, fun {V} _ hcardV {G} _ _ ↦ ?_⟩
    rw [completeEquipartiteGraph_eq_bot_iff.mpr h0, bot_isContained_iff_card_le,
      card_prod, Fintype.card_fin, Fintype.card_fin]
    exact hcardV
  · rw [← Nat.pos_iff_ne_zero] at hr_pos ht_pos
    -- choose `ε'` to ensure `G.minDegree` is large enough
    let ε' := 1 / (↑(r - 1) * r) + ε
    have hε' : 0 < ε' := by positivity
    -- choose `t'` larger than `t / (r * ε)`
    let t' := ⌊t / (r * ε)⌋₊ + 1
    have ht_lt_rt'ε : t < r * t' * ε := by
      rw [mul_comm (r : ℝ) (t' : ℝ), mul_assoc, ← div_lt_iff₀ (by positivity), Nat.cast_add_one]
      exact Nat.lt_floor_add_one (t / (r * ε))
    have ht' : 0 < t' := by positivity
    have ⟨N', ih⟩ := completeEquipartiteGraph_isContained_of_minDegree hε' (r - 1) t'
    -- choose `N` at least `(t'.choose t ^ r * t + r * t') * (t '- t) / (r * t' * ε - t)` to
    -- satisfy the pigeonhole principle
    let N := max (max 1 N') ⌈(t'.choose t ^ r * t + r * t') * (t' - t) / (r * t' * ε - t)⌉₊
    refine ⟨N, fun {V} _ hcardV {G} _ hδ ↦ ?_⟩
    have : Nonempty V := card_pos_iff.mp <| hcardV.trans_lt' <|
      lt_max_of_lt_left (lt_max_of_lt_left zero_lt_one)
    -- `r` is less than `1 / ε` otherwise `G.minDegree = card V`
    have hrε_lt_1 : r * ε < 1 := by
      have hδ_lt_card : (G.minDegree : ℝ) < (card V : ℝ) := mod_cast G.minDegree_lt_card
      contrapose! hδ_lt_card with h1_le_rε
      rw [← div_le_iff₀' (by positivity), ← sub_nonpos,
        ← le_sub_self_iff 1, ← sub_add] at h1_le_rε
      exact hδ.trans' (le_mul_of_one_le_left (card V).cast_nonneg h1_le_rε)
    have ht_lt_t' : t < t' := by
      rw [mul_comm (r : ℝ) (t' : ℝ), mul_assoc] at ht_lt_rt'ε
      exact_mod_cast ht_lt_rt'ε.trans_le (mul_le_of_le_one_right (mod_cast ht'.le) hrε_lt_1.le)
    -- identify a `completeEquipartiteGraph r t'` in `G` from the inductive hypothesis
    replace ih : completeEquipartiteGraph r t' ⊑ G := by
      rcases eq_or_ne r 1 with hr_eq_1 | hr_ne_1
      -- if `r = 1` then `completeEquipartiteGraph r t' = ⊥`
      · have h0 : r ≤ 1 ∨ t' = 0 := Or.inl hr_eq_1.le
        rw [completeEquipartiteGraph_eq_bot_iff.mpr h0, bot_isContained_iff_card_le,
          card_prod, Fintype.card_fin, Fintype.card_fin, hr_eq_1, one_mul]
        apply hcardV.trans'
        exact_mod_cast calc (t' : ℝ)
          _ ≤ r * t' := le_mul_of_one_le_left (by positivity) (mod_cast hr_pos)
          _ ≤ t'.choose t ^ r * t + r * t' := le_add_of_nonneg_left (by positivity)
          _ ≤ (t'.choose t ^ r * t + r * t') * (t' - t) / (r * t' * ε - t) := by
            rw [mul_div_assoc, le_mul_iff_one_le_right (by positivity),
              one_le_div (sub_pos.mpr ht_lt_rt'ε), sub_le_sub_iff_right,
              mul_comm (r : ℝ) (t' : ℝ),  mul_assoc, mul_le_iff_le_one_right (by positivity)]
            exact hrε_lt_1.le
          _ ≤ ⌈(t'.choose t ^ r * t + r * t') * (t' - t) / (r * t' * ε - t)⌉₊ := Nat.le_ceil _
          _ ≤ N := Nat.cast_le.mpr (le_max_right _ _)
      -- if `r > 1` then `G` satisfies the inductive hypothesis
      · have hδ' := calc (G.minDegree : ℝ)
          _ ≥ (1 - 1 / (r - 1) + (1 / (r - 1) - 1 / r) + ε) * card V := by
              rwa [← sub_add_sub_cancel _ (1 / (r - 1) : ℝ) _] at hδ
          _ = (1 - 1 / ↑(r - 1) + ε') * card V := by
              rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
                (sub_ne_zero_of_ne (mod_cast hr_ne_1)) (mod_cast hr_pos.ne'),
                sub_sub_cancel, mul_one, one_div_mul_one_div_rev, mul_comm (r : ℝ) _,
                ← Nat.cast_pred hr_pos, add_assoc]
        rw [← Nat.succ_pred_eq_of_pos hr_pos]
        exact ih (hcardV.trans' (le_max_of_le_left (le_max_right 1 N'))) hδ'
    obtain ⟨A⟩ := completeEquipartiteGraph_isContained_iff.mp ih
    -- find `t` vertices not in `A` adjacent to `t` vertices in each `A.parts` using the
    -- pigeonhole principle
    obtain ⟨y, hy⟩ := by classical
      apply ErdosStone.filterComplVertsAdjParts.pi.exists_le_card_fiber A hr_pos ht_lt_t' hδ
      rw [← div_le_iff₀ (sub_pos_of_lt ht_lt_rt'ε)]
      trans (N : ℝ)
      · exact (Nat.le_ceil _).trans (Nat.cast_le.mpr <| le_max_right _ _)
      · exact_mod_cast hcardV
    have ⟨s, hs_subset, hcards⟩ := exists_subset_card_eq hy
    -- identify the `t` vertices in each `A.parts` as a `completeEquipartiteSubgraph r t` in `A`
    let A' : G.CompleteEquipartiteSubgraph r t := by
      refine ⟨fun i ↦ (y i).val, fun i ↦ (mem_powersetCard.mp (y i).prop).right,
        fun i j h v hv w hw ↦ ?_⟩
      have hyi := mem_powersetCard.mp (y i).prop
      have hyj := mem_powersetCard.mp (y j).prop
      exact A.Adj h v (hyi.1 hv) w (hyj.1 hw)
    -- identify the `t` vertices not in `A` and the `completeEquipartiteSubgraph r t` in `A`
    -- as a `completeEquipartiteSubgraph (r + 1) t` in `G`
    refine completeEquipartiteGraph_succ_isContained_iff.mpr
      ⟨A', s.map (.subtype _), by rwa [← card_map] at hcards, fun v hv i w hw ↦ ?_⟩
    obtain ⟨v', hv', hv⟩ := Finset.mem_map.mp hv
    apply hs_subset at hv'
    classical rw [mem_filter] at hv'
    rw [show A'.parts i = y i by rfl, ← hv'.2] at hw
    rw [← hv, Function.Embedding.coe_subtype]
    classical exact ErdosStone.filterComplVertsAdjParts.pi.mem_val A v' i w hw

/-- Repeatedly remove minimal degree vertices until `(G.induce s).minDegree` is at least `c * #s`
and count the edges removed in the process.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
lemma exists_induce_minDegree_ge_and_card_edgeFinset_ge
    {c : ℝ} (hc_nonneg : 0 ≤ c) (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ s : Finset V, ↑s ⊆ G.support ∧ c * #s ≤ (G.induce s).minDegree ∧
      #(G.induce s).edgeFinset ≥ #G.edgeFinset - c * (card G.support ^ 2 - #s ^ 2) / 2
        - c * (card G.support - #s) / 2 := by
  rcases le_or_lt (c * #G.support.toFinset) (G.induce G.support.toFinset).minDegree with hδ | hδ
  -- if `minDegree` is already at least `c * card G.support`
  · refine ⟨G.support.toFinset, G.support.coe_toFinset.subset, hδ, ?_⟩
    suffices hcard_edges : #(G.induce G.support).edgeFinset ≥ #G.edgeFinset
        - c * (card G.support ^ 2 - #G.support.toFinset ^ 2) / 2
        - c * (card G.support - #G.support.toFinset) / 2 by
      convert hcard_edges
      all_goals exact G.support.coe_toFinset
    rw [card_edgeFinset_induce_support, ← G.support.toFinset_card,
      sub_self, mul_zero,  zero_div, sub_zero, sub_self, mul_zero, zero_div, sub_zero]
  -- if `minDegree` is less than `c * card G.support`
  · replace hδ : (G.induce G.support).minDegree < c * (card G.support) := by
      rw [G.support.toFinset_card] at hδ
      convert hδ
      all_goals exact G.support.coe_toFinset.symm
    have hcard_support_pos : 0 < card G.support := by
      contrapose! hδ
      rw [Nat.eq_zero_of_le_zero hδ, Nat.cast_zero, mul_zero]
      exact Nat.cast_nonneg (G.induce G.support).minDegree
    have : Nonempty G.support := card_pos_iff.mp hcard_support_pos
    -- delete a minimal degree vertex
    have ⟨x, hδ_eq_degx⟩ := exists_minimal_degree_vertex (G.induce G.support)
    let G' := G.deleteIncidenceSet ↑x
    -- repeat the process
    have ⟨s, hs', ihδ', ih_card_edges'⟩ :=
      exists_induce_minDegree_ge_and_card_edgeFinset_ge hc_nonneg G'
    have ⟨hs, hx_not_mem⟩ : ↑s ⊆ G.support ∧ ↑x ∉ (s : Set V) := by
      rw [← Set.disjoint_singleton_right, ← Set.subset_diff]
      exact hs'.trans (G.support_deleteIncidenceSet_subset ↑x)
    have ihδ : c * #s ≤ (G.induce s).minDegree := by
      simpa [← induce_deleteIncidenceSet_of_not_mem G hx_not_mem] using ihδ'
    have ih_card_edges : #(G.induce s).edgeFinset ≥ #G'.edgeFinset
        - c * (card G'.support ^ 2 - #s ^ 2) / 2 - c * (card G'.support - #s) / 2 := by
      simpa [← G.induce_deleteIncidenceSet_of_not_mem hx_not_mem] using ih_card_edges'
    -- use the `s` found at the end of the process
    refine ⟨s, hs, ihδ, ?_⟩
    calc (#(G.induce s).edgeFinset : ℝ)
      _ ≥ #G'.edgeFinset - (c * (card G'.support ^ 2 - #s ^ 2) / 2
        + c * (card G'.support - #s) / 2) := by rwa [sub_sub] at ih_card_edges
      _ ≥ (#G.edgeFinset - c * card G.support) - (c * ((card G.support - 1) ^ 2 - #s ^ 2) / 2
        + c * (card G.support - 1 - #s) / 2) := by
          apply sub_le_sub
          -- exactly `G.minDegree` edges are deleted from the edge set
          · rw [G.card_edgeFinset_deleteIncidenceSet ↑x,
              Nat.cast_sub (G.degree_le_card_edgeFinset x), ← degree_induce_support, ← hδ_eq_degx]
            exact sub_le_sub_left hδ.le #G.edgeFinset
          -- at least one vertex is deleted from the support
          · rw [← add_div, ← add_div, div_le_div_iff_of_pos_right zero_lt_two,
              ← Nat.cast_pred card_pos, ← mul_add, sub_add_sub_comm, ← mul_add, sub_add_sub_comm,
              ← Nat.cast_pow (card G'.support) 2, ← Nat.cast_pow (card G.support - 1) 2]
            apply mul_le_mul_of_nonneg_left _ hc_nonneg
            apply sub_le_sub (add_le_add _ _) le_rfl
            · exact_mod_cast Nat.pow_le_pow_left (G.card_support_deleteIncidenceSet x.prop) 2
            · exact_mod_cast G.card_support_deleteIncidenceSet x.prop
      _ ≥ #G.edgeFinset - c * (card G.support ^ 2 - #s ^ 2) / 2
        - c * (card G.support - #s) / 2 := by linarith
termination_by card G.support
decreasing_by
  exact (G.card_support_deleteIncidenceSet x.prop).trans_lt (Nat.pred_lt_of_lt hcard_support_pos)

/-- Repeatedly remove minimal degree vertices until `(G.induce s).minDegree` is at least `c * #s`
and `#s ^ 2 ≥ ε * card V ^ 2 - c * card V`, that is, `#s ≈ √ε * card V` when `c ≈ 0`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
lemma exists_induce_minDegree_ge_and_card_sq_ge
    {c : ℝ} (hc_nonneg : 0 ≤ c) {ε : ℝ} (h : #G.edgeFinset ≥ (c + ε) * card V ^ 2 / 2) :
    ∃ s : Finset V, c * #s ≤ (G.induce s).minDegree ∧ ε * card V ^ 2 - c * card V ≤ #s ^ 2 := by
  rcases isEmpty_or_nonempty V
  · exact ⟨∅, by simp⟩
  · have ⟨s, _, hδ, hs⟩ := exists_induce_minDegree_ge_and_card_edgeFinset_ge hc_nonneg G
    rw [ge_iff_le, sub_sub, sub_le_iff_le_add] at hs
    refine ⟨s, hδ, ?_⟩
    rw [← div_le_div_iff_of_pos_right zero_lt_two, sub_div]
    -- use `#G.edgeFinset ≥ (c + ε) * card V ^ 2 / 2` to bound `#s ^ 2`
    calc ε * card V ^ 2 / 2 - c * card V / 2
      _ = (c + ε) * card V ^ 2 / 2 - (c * card V ^ 2 / 2 + c * card V / 2) := by ring_nf
      _ ≤ #s * (#s - 1) / 2 + (c * (card G.support ^ 2 - #s ^ 2) / 2
        + c * (card G.support - #s) / 2) - (c * card V ^ 2 / 2 + c * card V / 2) := by
          apply sub_le_sub_right
          apply (h.trans hs).trans
          apply add_le_add_right
          rw [← Nat.cast_choose_two, ← card_coe s]
          exact_mod_cast card_edgeFinset_le_card_choose_two
      _ = #s ^ 2 / 2 - (c * (card V ^ 2 - card G.support ^ 2) / 2
        + c * (card V - card G.support) / 2 + c * #s ^ 2 / 2 + c * #s / 2 + #s / 2) := by ring_nf
      _ ≤ #s ^ 2 / 2 := by
          apply sub_le_self
          repeat apply add_nonneg
          any_goals apply div_nonneg _ zero_le_two
          any_goals apply mul_nonneg hc_nonneg
          any_goals apply sub_nonneg_of_le
          any_goals apply pow_le_pow_left₀
          all_goals first | positivity | exact_mod_cast set_fintype_card_le_univ G.support

/-- If `G` has at least `(1 - 1 / r + o(1)) * card V ^ 2 / 2` many edges, then `G` contains a
copy of a `completeEquipartiteGraph (r + 1) t`.

This is the **Erdős-Stone theorem**. -/
theorem completeEquipartiteGraph_isContained_of_card_edgeFinset
    {ε : ℝ} (hε_pos : 0 < ε) (r t : ℕ) :
    ∃ N, ∀ {V : Type*} [Fintype V], N ≤ card V →
      ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
        #G.edgeFinset ≥ (1 - 1 / r + ε) * card V ^ 2 / 2
        → completeEquipartiteGraph (r + 1) t ⊑ G := by
  -- choose `c + ε' = (1 - 1 / r + ε / 2) + ε / 2 = 1 - 1 / r + ε`
  let ε' := ε / 2
  have hε' : 0 < ε' := by positivity
  let c := 1 - 1 / r + ε / 2
  have hc : 0 < c := add_pos_of_nonneg_of_pos r.one_sub_one_div_cast_nonneg hε'
  -- find `N' > card V` sufficent for the minimal-degree version of the Erdős-Stone theorem
  have ⟨N', ih⟩ := completeEquipartiteGraph_isContained_of_minDegree hε' r t
  refine ⟨⌈c / ε' + N' / √ε'⌉₊, fun {V} _ hcardV {G} _ h ↦ ?_⟩
  rw [Nat.ceil_le] at hcardV
  -- find `s` such that `G.induce s` has appropriate minimal-degree
  rw [← add_halves ε, ← add_assoc] at h
  classical obtain ⟨s, hδ, hcards_sq⟩ := exists_induce_minDegree_ge_and_card_sq_ge hc.le h
  -- assume `#s` is sufficently large
  suffices hcards_sq : (N' ^ 2 : ℝ) ≤ (#s ^ 2 : ℝ) by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_le,
      Nat.pow_le_pow_iff_left two_ne_zero] at hcards_sq
    -- find `completeEquipartiteGraph` from minimal-degree version of the Erdős-Stone theorem
    simp_rw [← card_coe, ← Finset.coe_sort_coe] at hcards_sq hδ
    exact (ih hcards_sq hδ).trans ⟨Copy.induce G s⟩
  -- `x ↦ ε' * x ^ 2 - c * x` is strictly monotonic on `[c / (2 * ε'), ∞)`
  have hMonoOn : MonotoneOn (fun x ↦ ε' * x ^ 2 - c * x) (Set.Ici (c / (2 * ε'))) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ (fun x hx ↦ ?_)
    · apply Continuous.continuousOn
      exact (continuous_const.mul (continuous_id'.pow 2)).sub (continuous_mul_left c)
    · apply Differentiable.differentiableOn
      exact ((differentiable_const ε').mul (differentiable_id'.pow 2)).sub
        (differentiable_id'.const_mul c)
    · rw [deriv_sub ((differentiableAt_id'.pow 2).const_mul ε') (differentiableAt_id'.const_mul c),
        deriv_const_mul _ (differentiableAt_id'.pow 2), deriv_pow 2, Nat.cast_two, pow_one,
        ← mul_assoc ε' 2 x, mul_comm ε' 2, deriv_const_mul _ differentiableAt_id', deriv_id'',
        mul_one, sub_nonneg, ← div_le_iff₀' (mul_pos two_pos hε')]
      rw [interior_Ici, Set.mem_Ioi] at hx
      exact hx.le
  -- prove `#s` is sufficently large
  calc (#s ^ 2 : ℝ)
    _ ≥ ε'* card V ^ 2 - c * card V := hcards_sq
    _ ≥ ε' * (c / ε' + N' / √ε') ^ 2 - c * (c / ε' + N' / √ε') := by
        have hle : c / (2 * ε') ≤ c / ε' + N' / √ε' := by
          trans c / ε'
          · rw [mul_comm, ← div_div, half_le_self_iff]
            exact div_nonneg hc.le hε'.le
          · rw [le_add_iff_nonneg_right]
            exact div_nonneg N'.cast_nonneg (sqrt_nonneg ε')
        exact hMonoOn hle (hle.trans hcardV) hcardV
    _ = N' ^ 2 + N' * c / sqrt ε' := by
        rw [add_pow_two, mul_add ε', div_pow _ √ε', sq_sqrt hε'.le,
          mul_div_cancel₀ _ hε'.ne', add_comm _ (N' ^ 2 : ℝ), add_sub_assoc, add_right_inj,
          mul_add ε' _ _, mul_add c _ _, add_sub_add_comm, div_pow c ε' 2, pow_two ε',
          ← mul_div_assoc ε' _ _, mul_div_mul_left _ _ hε'.ne', ← mul_div_assoc c c ε',
          ← pow_two c, sub_self, zero_add, mul_comm ε' _, mul_assoc _ _ ε', mul_mul_mul_comm,
          div_mul_cancel₀ _ hε'.ne', mul_assoc 2 _ c, ← mul_div_right_comm _ c √ε',
          ← mul_div_assoc c _ √ε', mul_comm c _, two_mul, add_sub_assoc, sub_self, add_zero]
    _ ≥ N' ^ 2 := le_add_of_nonneg_right (by positivity)

/-- If `G` has at least `(1 - 1 / r + o(1)) * card V ^ 2 / 2` many edges, then `G` contains a
copy of any `r + 1`-colorable graph.

This is a corollary of the **Erdős-Stone theorem**. -/
theorem isContained_of_card_edgeFinset_of_colorable
    {r : ℕ} (hc : H.Colorable (r + 1)) {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ N, ∀ {V : Type*} [Fintype V], N ≤ card V →
      ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
        #G.edgeFinset ≥ (1 - 1 / r + ε) * card V ^ 2 / 2 → H ⊑ G := by
  obtain ⟨C⟩ := hc
  let f := fun c ↦ card (C.colorClass c)
  have hH : H ⊑ completeEquipartiteGraph (r + 1) (univ.sup f) := by
    refine isContained_completeEquipartiteGraph_of_colorable C (univ.sup f) (fun c ↦ ?_)
    rw [show card (C.colorClass c) = f c from rfl]
    exact le_sup (mem_univ c)
  have ⟨N, ih⟩ := completeEquipartiteGraph_isContained_of_card_edgeFinset hε_pos r (univ.sup f)
  exact ⟨N, fun {V} _ hcardV {G} _ h ↦ hH.trans (ih hcardV h)⟩

end ErdosStone

section ErdosStoneSimonovits

namespace ErdosStoneSimonovits

/-- If the `H` is `r`-colorable then `extremalNumber n H` is at most
`(1 - 1 / r + o(1)) * n ^ 2 / 2`.

This is an auxiliary definition for the **Erdős-Stone-Simonovits theorem**. -/
lemma extremalNumber_le_of_colorable
    {r : ℕ} (hc : H.Colorable (r + 1)) {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ N, ∀ n > N, extremalNumber n H ≤ (1 - 1 / r + ε) * n ^ 2 / 2 := by
  obtain ⟨N, h⟩ := isContained_of_card_edgeFinset_of_colorable hc hε_pos
  have hpos : 0 ≤ 1 - 1 / r + ε := add_nonneg r.one_sub_one_div_cast_nonneg hε_pos.le
  conv =>
    enter [1, N, n, hn]
    rw [← Fintype.card_fin n, extremalNumber_le_iff_of_nonneg _ (by positivity)]
  refine ⟨N, fun n hn {G} _ hfree ↦ ?_⟩
  rw [← Fintype.card_fin n] at hn
  contrapose! hfree with hcard_edges
  rw [not_free]
  exact h hn.le hcard_edges.le

omit [Fintype W] in
/-- If the `H` is not `r`-colorable and `r > 0`, then `extremalNumber n H` is greater than
`(1 - 1 / r - o(1)) * n ^ 2 / 2`.

This is an auxiliary definition for the **Erdős-Stone-Simonovits theorem**. -/
lemma lt_extremalNumber_of_not_colorable
    {r : ℕ} (hr_pos : 0 < r) (nhc : ¬H.Colorable r) {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ N, ∀ n > N, (1 - 1 / r - ε) * n ^ 2 / 2 < extremalNumber n H := by
  refine ⟨⌊2 * r / ε⌋₊, fun n hn_lt ↦ ?_⟩
  have hn_pos : 0 < n := Nat.zero_lt_of_lt hn_lt
  let G := completeEquipartiteGraph r (n / r)
  -- `completeEquipartiteGraph` is `r`-colorable
  have : Nonempty (Fin r × Fin (n / r) ↪ Fin n) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    exact Nat.mul_div_le n r
  let f := Classical.arbitrary (Fin r × Fin (n / r) ↪ Fin n)
  -- `completeEquipartiteGraph` has sufficently many edges
  have hcard_edges : #G.edgeFinset > (1 - 1 / r - ε) * n ^ 2 / 2 := by
    calc (1 - 1 / r - ε) * n ^ 2 / 2
      _ < (1 - 1 / r) * n ^ 2 / 2 - r * n := by
          rw [sub_mul, sub_div, sub_lt_sub_iff_left, lt_div_iff₀ zero_lt_two,
            mul_comm, ← mul_assoc, pow_two, ← mul_assoc]
          have h2r_lt_εn : 2 * r < ε * n := by
            rwa [gt_iff_lt, Nat.floor_lt (by positivity), div_lt_iff₀' hε_pos] at hn_lt
          exact mul_lt_mul_of_pos_right h2r_lt_εn (mod_cast hn_pos)
      _ = (1 - 1 / r) * r ^ 2 * (n / r : ℕ) ^ 2 / 2
        + (1 - 1 / r) * (n * ↑(n % r)) - (1 - 1 / r) * ↑(n % r) ^ 2 / 2 - r * n := by
          conv in (1 - 1 / r) * (n : ℝ) ^ 2 / 2 =>
            rw [← Nat.div_add_mod n r, Nat.cast_add, add_sq, add_assoc, mul_add, add_div,
              Nat.cast_mul, mul_pow, ← mul_assoc]
          rw [sub_left_inj, add_sub_assoc, add_right_inj, ← Nat.cast_mul, ← Nat.sub_eq_of_eq_add
            (Nat.div_add_mod n r).symm, Nat.cast_sub (Nat.mod_le n r), mul_add, add_div,
            mul_assoc 2 _ _, mul_comm 2 _, ← mul_assoc _ _ 2, sub_mul (n : ℝ) _ _,
            mul_div_cancel_right₀ _ two_ne_zero, mul_sub, ← pow_two, sub_add, sub_half]
      _ ≤ (1 - 1 / r) * r ^ 2 * (n / r : ℕ) ^ 2 / 2 := by
          rw [add_sub_assoc, add_sub_assoc, add_le_iff_nonpos_right, sub_sub, sub_nonpos,
            ← mul_assoc, mul_comm (r : ℝ) (n : ℝ), ← zero_add ((1 - 1 / r) * n * ↑(n % r) : ℝ)]
          apply add_le_add
          · apply div_nonneg _ zero_le_two
            exact mul_nonneg (r.one_sub_one_div_cast_nonneg) (by positivity)
          · apply mul_le_mul _ (mod_cast (n.mod_lt hr_pos).le)
              (n % r).cast_nonneg (mod_cast hn_pos.le)
            exact mul_le_of_le_one_left (mod_cast hn_pos.le) r.one_sub_one_div_cast_le_one
      _ = #(completeEquipartiteGraph r (n / r)).edgeFinset := by
          rw [card_edgeFinset_completeEquipartiteGraph, Nat.cast_mul, Nat.cast_pow,
            Nat.cast_choose_two, div_mul_eq_mul_div, sub_mul, div_mul_eq_mul_div, pow_two,
            ← mul_assoc, mul_div_assoc _ (r : ℝ) (r : ℝ), ← mul_sub, one_mul,
            div_self (mod_cast hr_pos.ne')]
  rw [← G.card_edgeFinset_map f] at hcard_edges
  apply lt_of_lt_of_le hcard_edges
  -- `H` is not contained in `completeEquipartiteGraph`
  conv_rhs => rw [← Fintype.card_fin n]
  refine mod_cast card_edgeFinset_le_extremalNumber ?_
  have : NeZero r := ⟨hr_pos.ne'⟩
  exact free_of_colorable nhc (completeEquipartiteGraph_colorable.map f)

end ErdosStoneSimonovits

/-- If the chromatic number of `H` equals `r + 1 > 0`, then `extremalNumber (card V) H` is greater
than `(1 - 1 / r - o(1)) * card V ^ 2 / 2` and at most `(1 - 1 / r + o(1)) * card V ^ 2 / 2`.

This is the **Erdős-Stone-Simonovits theorem**. -/
theorem lt_extremalNumber_le_of_chromaticNumber {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) :
    ∃ N, ∀ n > N, (1 - 1 / r - ε) * n ^ 2 / 2 < extremalNumber n H ∧
      extremalNumber n H ≤ (1 - 1 / r + ε) * n ^ 2 / 2 := by
  have ⟨hc, nhc⟩ := chromaticNumber_eq_iff_colorable_not_colorable.mp hχ
  have ⟨N₁, h₁⟩ := ErdosStoneSimonovits.extremalNumber_le_of_colorable hc hε
  have ⟨N₂, h₂⟩ := ErdosStoneSimonovits.lt_extremalNumber_of_not_colorable hr_pos nhc hε
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hn₁ := hn.trans_le' (Nat.le_max_left N₁ N₂)
  have hn₂ := hn.trans_le' (Nat.le_max_right N₁ N₂)
  exact ⟨h₂ n hn₂, h₁ n hn₁⟩

/-- If the chromatic number of `H` equals `r + 1 > 0`, then the `extremalNumber` of `H` is equal
to `(1 - 1 / r + o(1)) * n ^ 2 / 2`.

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem isLittleO_extremalNumber_of_chromaticNumber
    {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) :
    (fun (n : ℕ) ↦ (extremalNumber n H - (1 - 1 / r) * n ^ 2 / 2 : ℝ))
      =o[atTop] (fun (n : ℕ) ↦ (n ^ 2 : ℝ)) := by
  simp_rw [isLittleO_iff, eventually_atTop]
  intro ε hε
  have ⟨n₀, h⟩ := lt_extremalNumber_le_of_chromaticNumber hε hr_pos hχ
  refine ⟨n₀ + 1, fun n (hn : n₀ < n) ↦ ?_⟩
  specialize h n hn
  rw [norm_eq_abs, ← abs_of_pos hε, norm_eq_abs, ← abs_mul]
  apply abs_le_abs
  all_goals linarith

/-- If the chromatic number of `H` equals `r + 1 > 0`, then the limit
`extremalNumber n H / n.choose 2` approaches `1 - 1 / r` as `n → ∞`.

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem tendsto_extremalNumber_div_choose_two_of_chromaticNumber
    {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) :
    Tendsto (fun (n : ℕ) ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop (𝓝 (1 - 1 / r)) := by
  have hlittleo := IsLittleO.trans_isTheta
    (isLittleO_extremalNumber_of_chromaticNumber hr_pos hχ) (isTheta_choose 2).symm
  have htendsto : Tendsto (fun (n : ℕ) ↦ (n ^ 2 / 2 / n.choose 2 : ℝ)) atTop (𝓝 1) := by
    have hz : ∀ᶠ (n : ℕ) in atTop, (n.choose 2 : ℝ) ≠ 0 :=
      eventually_atTop.mpr ⟨2, fun _ h ↦ mod_cast (Nat.choose_pos h).ne'⟩
    simpa only [isEquivalent_iff_tendsto_one hz] using (isEquivalent_choose 2).symm
  simpa [sub_div, ← mul_div]
    using hlittleo.tendsto_div_nhds_zero.add <| htendsto.const_mul (1 - 1 / r : ℝ)

/-- If the chromatic number of `H` equals `r + 1 > 0`, then the Turán density of `H`
equals `1 - 1 / r`.

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem turanDensity_eq_of_chromaticNumber
    {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) : turanDensity H = 1 - 1 / r :=
  (tendsto_extremalNumber_div_choose_two_of_chromaticNumber hr_pos hχ).limUnder_eq

/-- If the chromatic number of `H` equals `r + 1 > 1`, then `extremalNumber n H` is
asymptotically equivalent to `(1 - 1 / r) * n.choose 2` as `n → ∞`

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem isEquivalent_extremalNumber_of_chromaticNumber
    {r : ℕ} (hr : 1 < r) (hχ : H.chromaticNumber = r + 1) :
    (fun (n : ℕ) ↦ (extremalNumber n H : ℝ))
      ~[atTop] (fun (n : ℕ) ↦ ((1 - 1 / r) * n.choose 2 : ℝ)) := by
  have hπ_eq : turanDensity H = 1 - 1 / r :=
    turanDensity_eq_of_chromaticNumber (by positivity) hχ
  have hπ_pos : 0 < turanDensity H := by
    rw [hπ_eq, sub_pos, one_div]
    exact inv_lt_one_of_one_lt₀ (mod_cast hr)
  rw [← hπ_eq]
  exact isEquivalent_extremalNumber hπ_pos.ne'

/-- If `G` has at least `(1 - 1 / r + o(1)) * (card V).choose 2` many edges, then `G`
contains a copy of `H`.

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem isContained_of_card_edgeFinset_of_chromaticNumber
    {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ N, ∀ {V : Type*} [Fintype V], N ≤ card V →
      ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
        #G.edgeFinset ≥ (1 - 1 / r + ε) * (card V).choose 2 → H ⊑ G := by
  rw [← turanDensity_eq_of_chromaticNumber hr_pos hχ]
  exact isContained_of_card_edgeFinset H hε_pos

end ErdosStoneSimonovits

end SimpleGraph
