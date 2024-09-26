import Mathlib

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The degree of a vertex is positive if and only if the vertex is contained
in the support. -/
lemma degree_pos_iff (v : V)
    [Fintype (G.neighborSet v)] : 0 < G.degree v ↔ v ∈ G.support :=
  degree_pos_iff_exists_adj G v

/-- The degree of a vertex is zero if and only if the vertex is not contained
in the support. -/
lemma degree_eq_zero_iff (v : V)
  [Fintype (G.neighborSet v)] : G.degree v = 0 ↔ v ∉ G.support := by
  rw [←not_iff_not, ←Nat.le_zero]
  push_neg
  exact degree_pos_iff G v

/-- The cardinality of the support is at most the number of vertices. -/
lemma card_support_le [Fintype G.support] [Fintype V] :
    Fintype.card G.support ≤ Fintype.card V :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

lemma incidenceFinset_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq V] [Fintype V] (x : V) :
    G.incidenceFinset x ⊆ G.edgeFinset := by
  rw [Set.subset_toFinset, incidenceFinset, Set.coe_toFinset]
  exact incidenceSet_subset G x

/-- The degree of a vertex is at most the number of edges. -/
theorem degree_le_card_edgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq V] [Fintype V] (x : V) :
    G.degree x ≤ G.edgeFinset.card := by
  rw [←card_incidenceFinset_eq_degree]
  apply Finset.card_le_card
  exact incidenceFinset_subset G x

variable [Fintype V] [DecidableRel G.Adj]

/-- The product of the number of vertices and the minimal degree is at most
twice the number of edges of a simple graph. -/
theorem card_mul_minDegree_le_twice_card_edgeFinset
     (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Fintype.card V)*G.minDegree ≤ 2*G.edgeFinset.card := by
  rw [←sum_degrees_eq_twice_card_edges]
  trans ∑ _ : V, G.minDegree
  . rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
  . apply Finset.sum_le_sum
    intro i _
    exact minDegree_le_degree G i

/-- The minimal degree is less than the number of vertices in a simple graph
with a nonempty vertex type. -/
theorem minDegree_lt_card [Nonempty V] :
    G.minDegree < Fintype.card V := by
  by_contra! h
  have h_card_sq_le_card_edgeFinset :
      (Fintype.card V)^2 ≤ 2*G.edgeFinset.card :=
    calc 2*G.edgeFinset.card
      _ ≥ (Fintype.card V)*G.minDegree :=
          card_mul_minDegree_le_twice_card_edgeFinset G
      _ ≥ (Fintype.card V)^2 := by
          rw [pow_two]
          exact Nat.mul_le_mul_left (Fintype.card V) h
  absurd h_card_sq_le_card_edgeFinset
  push_neg
  calc 2*G.edgeFinset.card
    _ ≤ 2*((Fintype.card V).choose 2) :=
        Nat.mul_le_mul_left _ card_edgeFinset_le_card_choose_two
    _ ≤ (Fintype.card V)*(Fintype.card V-1) := by
        rw [Nat.choose_two_right]
        exact Nat.mul_div_le _ _
    _ < (Fintype.card V)^2 := by
        rw [pow_two]
        apply Nat.mul_lt_mul_of_le_of_lt
        . exact le_refl (Fintype.card V)
        . exact Nat.sub_lt_self zero_lt_one Fintype.card_pos
        . exact Fintype.card_pos

/-- The number of vertices is at least the minimal degree in a simple graph. -/
theorem minDegree_le_card :
    G.minDegree ≤ Fintype.card V := by
  by_cases h : Nonempty V
  . exact le_of_lt (minDegree_lt_card G)
  . rw [not_nonempty_iff] at h
    have h_card : Fintype.card V = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact h
    rw [minDegree, Finset.univ_eq_empty, Finset.image_empty, Finset.min_empty,
      WithTop.untop'_top, h_card]

/-- The minimal degree of isomorphic simple graphs are equal. -/
theorem Iso.minDegree_eq {α β : Type*} [Fintype α] [Fintype β]
    {A : SimpleGraph α} [DecidableRel A.Adj]
    {B : SimpleGraph β} [DecidableRel B.Adj] (f : A ≃g B) :
    A.minDegree = B.minDegree := by
  by_cases h : IsEmpty α
  . haveI : IsEmpty β := by
      by_contra nh
      absurd h
      rw [not_isEmpty_iff] at nh ⊢
      have ⟨x⟩ := nh
      exact ⟨f.symm x⟩
    simp [minDegree]
  haveI : Nonempty α := by
    rwa [not_isEmpty_iff] at h
  have ⟨x, hx⟩ := exists_minimal_degree_vertex A
  haveI : Nonempty β := ⟨f x⟩
  have ⟨x', hx'⟩ := exists_minimal_degree_vertex B
  apply eq_of_le_of_not_lt
  . rw [hx', ←card_neighborSet_eq_degree,
      Fintype.card_congr ((f.symm).mapNeighborSet x'),
      card_neighborSet_eq_degree]
    exact minDegree_le_degree A (f.symm x')
  . apply not_lt_of_le
    rw [hx, ←card_neighborSet_eq_degree,
      Fintype.card_congr (f.mapNeighborSet x),
      card_neighborSet_eq_degree]
    exact minDegree_le_degree B (f x)
