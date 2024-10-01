import Mathlib

import ErdosStoneSimonovits.Restrict
import ErdosStoneSimonovits.Extremal

namespace SimpleGraph

section CompleteEquipartiteGraph

variable {V α β : Type*} {G : SimpleGraph V} {A : SimpleGraph α}

/-- The `completeEquipartiteGraph α β` on the product type `α × β` is the
blow-up of the `completeGraph α` on the type `α` by the type `β`. -/
abbrev completeEquipartiteGraph (α β : Type*) :
  SimpleGraph (α × β) := SimpleGraph.comap Prod.fst ⊤

theorem completeEquipartiteGraph_adj :
  (completeEquipartiteGraph α β).Adj i j ↔ i.1 ≠ j.1 := by rfl

theorem neighborSet_completeEquipartiteGraph (v : α × β) :
    (completeEquipartiteGraph α β).neighborSet v
      = {v.1}ᶜ ×ˢ Set.univ := by
  ext; simp [ne_comm]

lemma neighborFinset_completeEquipartiteGraph
    [Fintype α] [DecidableEq α] [Fintype β] (v : α × β) :
    (completeEquipartiteGraph α β).neighborFinset v
      = {v.1}ᶜ ×ˢ Finset.univ := by
  ext; simp [ne_comm]

theorem degree_completeEquipartiteGraph
    [Fintype α] [DecidableEq α] [Fintype β] (v : α × β) :
    (completeEquipartiteGraph α β).degree v
      = ((Fintype.card α)-1)*(Fintype.card β) := by
  rw [←card_neighborFinset_eq_degree,
    neighborFinset_completeEquipartiteGraph v, Finset.card_product,
    Finset.card_compl, Finset.card_singleton, Finset.card_univ]

theorem card_edgeFinset_completeEquipartiteGraph
    [Fintype α] [DecidableEq α] [Fintype β] :
    (completeEquipartiteGraph α β).edgeFinset.card
      = ((Fintype.card α).choose 2)*(Fintype.card β)^2 := by
  rw [←mul_right_inj' two_ne_zero, ←sum_degrees_eq_twice_card_edges]
  conv_lhs =>
    rhs; intro v
    rw [degree_completeEquipartiteGraph]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_prod]
  conv_rhs =>
    rw [←Nat.mul_assoc, Nat.choose_two_right,
      Nat.mul_div_cancel' (Nat.even_mul_pred_self (Fintype.card α)).two_dvd]
  ring_nf

/-- The construction of a subgraph isomorphism of
`completeEquipartiteGraph α β`. -/
theorem isIsoSubgraph_completeEquipartiteGraph_iff
    [Fintype β] [Nonempty β] [Fintype V] :
    (completeEquipartiteGraph α β).IsIsoSubgraph G
      ↔ ∃ A : α → Finset.univ.powersetCard (Fintype.card β),
          ∀ a₁ a₂, a₁ ≠ a₂ →
            ∀ v₁ ∈ (A a₁).val, ∀ v₂ ∈ (A a₂).val, G.Adj v₁ v₂ := by
  constructor
  . intro ⟨f⟩
    let fₐ (a : α) : β ↪ V := by
      use fun b ↦ f (a, b)
      intro b₁ b₂ hb
      apply f.injective at hb
      rw [Prod.mk.injEq] at hb
      exact hb.2
    let A (a : α) :
        Finset.univ.powersetCard (Fintype.card β) := by
      use Finset.univ.map (fₐ a)
      simp
    use A
    . intro a₁ a₂ ha v₁ hv₁ v₂ hv₂
      rw [Finset.mem_map] at hv₁ hv₂
      have ⟨b₁, _, hb₁⟩ := hv₁
      have ⟨b₂, _, hb₂⟩ := hv₂
      rw [←hb₁, ←hb₂]
      exact f.toHom.map_adj ha
  . intro ⟨A, h⟩
    let fₐ (a : α) : β ↪ A a := by
      have ha := (A a).prop
      rw [Finset.mem_powersetCard, ←Fintype.card_coe] at ha
      exact (Fintype.equivOfCardEq ha.2).symm.toEmbedding
    let f : α × β ↪ V := by
      use fun (a, b) ↦ ↑(fₐ a b)
      intro (a₁, b₁) (a₂, b₂) h_eq
      rw [Prod.mk.injEq]
      contrapose! h_eq
      by_cases ha : a₁ = a₂
      . rw [ha]
        replace h_eq := h_eq ha
        contrapose! h_eq
        apply (fₐ a₂).injective
        rw [Subtype.ext_iff]
        exact h_eq
      . exact (h a₁ a₂ ha _ (fₐ a₁ b₁).prop _ (fₐ a₂ b₂).prop).ne
    use ⟨f, ?_⟩
    . exact f.injective
    . intro (a₁, b₁) (a₂, b₂) ha
      rw [completeEquipartiteGraph_adj] at ha
      exact h a₁ a₂ ha _ (fₐ a₁ b₁).prop _ (fₐ a₂ b₂).prop

/-- The construction of a subgraph isomorphism of
`completeEquipartiteGraph (Fin (n+1)) β` from a subgraph isomorphism of
`completeEquipartiteGraph (Fin n) β`. -/
theorem isIsoSubgraph_completeEquipartiteGraph_succ_iff
    [Fintype β] [Nonempty β] [Fintype V] :
  (completeEquipartiteGraph (Fin (n+1)) β).IsIsoSubgraph G
    ↔ ∃ A : (Fin n) → Finset.univ.powersetCard (Fintype.card β),
        (∀ a₁ a₂, a₁ ≠ a₂ →
          ∀ v₁ ∈ (A a₁).val, ∀ v₂ ∈ (A a₂).val, G.Adj v₁ v₂) ∧
        (∃ s : Finset.univ.powersetCard (Fintype.card β),
          ∀ v₁ ∈ s.val, ∀ a, ∀ v₂ ∈ (A a).val, G.Adj v₁ v₂) := by
  rw [isIsoSubgraph_completeEquipartiteGraph_iff]
  constructor
  . intro ⟨A', h⟩
    use fun i ↦ A' (Fin.castSucc i)
    constructor
    . intro i₁ i₂ ha v₁ hv₁ v₂ hv₂
      apply h i₁ i₂
      . simp [ha]
      . rw [Fin.coe_eq_castSucc]
        exact hv₁
      . rw [Fin.coe_eq_castSucc]
        exact hv₂
    . use A' (Fin.last n)
      intro v₁ hv₁ i v₂ hv₂
      apply adj_symm
      apply h i (Fin.last n)
      . rw [←Fin.exists_castSucc_eq, Fin.coe_eq_castSucc]
        use i
      . rw [Fin.coe_eq_castSucc]
        exact hv₂
      . exact hv₁
  . intro ⟨A, h, s, hs⟩
    haveI : Nonempty s := by
      have hs_mem := s.prop
      rw [Finset.mem_powersetCard] at hs_mem
      rw [←Fintype.card_pos_iff, Fintype.card_coe, hs_mem.2]
      exact Fintype.card_pos
    use fun i ↦ if hi : ↑i < n then A ⟨i, hi⟩ else s
    intro i₁ i₂ hi v₁ hv₁ v₂ hv₂
    by_cases hi₁ : ↑i₁ < n <;> by_cases hi₂ : ↑i₂ < n
    all_goals simp [hi₁, hi₂] at hi hv₁ hv₂ ⊢
    . apply h ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ _ v₁ hv₁ v₂ hv₂
      rw [ne_eq, Fin.mk.injEq, ←Fin.ext_iff]
      exact hi
    . apply adj_symm
      exact hs v₂ hv₂ ⟨i₁, hi₁⟩ v₁ hv₁
    . exact hs v₁ hv₁ ⟨i₂, hi₂⟩ v₂ hv₂
    . absurd hi
      apply Fin.eq_of_val_eq
      push_neg at hi₁ hi₂
      rw [Nat.eq_of_le_of_lt_succ hi₁ i₁.isLt,
          Nat.eq_of_le_of_lt_succ hi₂ i₂.isLt]

/-- An `α`-coloring of `completeEquipartiteGraph α β` -/
def completeEquipartiteGraphColoring :
  (completeEquipartiteGraph α β).Coloring α := ⟨Prod.fst, id⟩

/-- The `completeEquipartiteGraph α β` is `Fintype.card α`-colorable. -/
theorem completeEquipartiteGraph_colorable [Fintype α] :
    (completeEquipartiteGraph α β).Colorable (Fintype.card α) :=
  Coloring.colorable completeEquipartiteGraphColoring

/-- The `completeEquipartiteGraph α β` is `Fintype.card α`-colorable. -/
theorem completeEquipartiteGraph_colorable_of_fin :
    (completeEquipartiteGraph (Fin n) β).Colorable n := by
  conv_rhs =>
    rw [←Fintype.card_fin n]
  exact completeEquipartiteGraph_colorable

/-- The generalization of `Colorable.mono_left` to isomorphic subgraphs. -/
lemma Colorable.mono_of_isIsoSubgraph {n : ℕ} (h : A.IsIsoSubgraph B) :
  B.Colorable n → A.Colorable n := fun ⟨C⟩ ↦ ⟨C.comp h.some⟩

/-- If `A` is not `n`-colorable and `G` is `n`-colorable, `G` does not contain
`A` as an isomorphic subgraph. -/
lemma not_isIsoSubgraph_of_colorable (nh_col : ¬A.Colorable n)
    (h_col : G.Colorable n) : ¬A.IsIsoSubgraph G := by
  contrapose! nh_col
  exact Colorable.mono_of_isIsoSubgraph nh_col h_col

/-- If `G` is not `n`-colorable then `completeEquipartiteGraph (Fin n) β`
cannot contain `G` as an isomorphic subgraph. -/
theorem not_isIsoSubgraph_completeEquipartiteGraph_of_not_colorable
    {n : ℕ} (h : ¬G.Colorable n) :
    ¬G.IsIsoSubgraph (completeEquipartiteGraph (Fin n) β) := by
  apply not_isIsoSubgraph_of_colorable h
  conv_rhs =>
    rw [←Fintype.card_fin n]
  exact completeEquipartiteGraph_colorable

instance [DecidableEq α] {C : Coloring G α} {c : α} :
    DecidablePred (· ∈ C.colorClass c) := by
  conv_rhs =>
    intro; rw [Coloring.colorClass, Set.mem_setOf_eq]
  infer_instance

/-- If `G` is `n`-colorable then `completeEquipartiteGraph (Fin n) β`
contains `G` as an isomorphic subgraph for sufficently large `β`. -/
theorem isIsoSubgraph_completeEquipartiteGraph_of_colorable [Fintype V]
    (h : G.Colorable n) :
    ∃ b, ∀ {β : Type*} [Fintype β],
      b ≤ Fintype.card β →
        G.IsIsoSubgraph (completeEquipartiteGraph (Fin n) β) := by
  let C := Classical.choice h
  use Finset.univ.sup fun c ↦ Fintype.card (C.colorClass c)
  intro β _ hcardβ
  haveI (c) : Nonempty (C.colorClass c ↪ β) :=
    Function.Embedding.nonempty_of_card_le
      ((Finset.le_sup (Finset.mem_univ c)).trans hcardβ)
  have ι (c) := Classical.arbitrary (C.colorClass c ↪ β)
  use ⟨fun v ↦ (C v, ι (C v) ⟨v, C.mem_colorClass v⟩), fun h ↦ C.valid h⟩
  intro v w hvw
  obtain ⟨hC_eq : C v = C w,
      hιCvv_eq_ιCww : ι (C v) ⟨v, _⟩ = ι (C w) ⟨w, _⟩⟩ := by
    rwa [Prod.mk.injEq] at hvw
  have hv_mem_Cw : v ∈ C.colorClass (C w) := by
    rw [Coloring.colorClass, Set.mem_setOf]
    exact hC_eq
  have hιCvv_eq_ιCwv :
      ι (C v) ⟨v, C.mem_colorClass v⟩ = ι (C w) ⟨v, hv_mem_Cw⟩ := by
    apply congr_heq
    . rw [hC_eq]
    . rw [Subtype.heq_iff_coe_eq]
      intro _
      rw [hC_eq]
  rw [hιCvv_eq_ιCwv] at hιCvv_eq_ιCww
  rw [←Subtype.mk.injEq]
  exact (ι (C w)).injective hιCvv_eq_ιCww

variable [Nonempty V] [Fintype V] [DecidableEq β]

noncomputable def Hom.map (G : SimpleGraph V) (f : V ↪ β) : G.map f →g G where
  toFun := fun b ↦
    if h : ∃ v, f v = b then h.choose else Classical.arbitrary V
  map_rel' := by
    intro x y hadj
    have ⟨hadj', hx', hy'⟩ := hadj.choose_spec.choose_spec
    by_cases hx : ∃ v, f v = x <;> by_cases hy : ∃ v, f v = y
    all_goals simp [hx, hy]
    . have hx_choice : hx.choose = hadj.choose := by
        apply f.injective
        rw [hx.choose_spec, hadj.choose_spec.choose_spec.2.1]
      have hy_choice : hy.choose = hadj.choose_spec.choose := by
        apply f.injective
        rw [hy.choose_spec, hadj.choose_spec.choose_spec.2.2]
      rw [hx_choice, hy_choice]
      exact hadj'
    all_goals
      try absurd hy; exact ⟨_, hy'⟩
      try absurd hx; exact ⟨_, hx'⟩

/-- Given an injective function `f`, if `G` is `n`-colorable then the mapped
simple graph `G.map f` is also `n`-colorable. -/
theorem Colorable.map (f : V ↪ β) :
  G.Colorable n → (G.map f).Colorable n := fun ⟨C⟩ ↦ ⟨C.comp (Hom.map G f)⟩

variable [DecidableEq V] [Fintype β] [DecidableRel G.Adj]
  {R : Type*} [LinearOrderedSemiring R] {x : R}

/-- If `A` is not `n`-colorable and `G` is `n`-colorable on vertex type
`|V| ≤ |β|`, the simple graph `B` constructed by mapping `G` via an embedding
`V ↪ β` does not contain `A` as an isomorphic subgraph. -/
theorem lt_extremalNumber_of_colorable
    (h_card_le : Fintype.card V ≤ Fintype.card β)
    (nh_col : ¬A.Colorable n) (h_col : G.Colorable n)
    (h : x < G.edgeFinset.card) : x < extremalNumber β A := by
  haveI : Nonempty (V ↪ β) := Function.Embedding.nonempty_of_card_le h_card_le
  let f := Classical.arbitrary (V ↪ β)
  let B := G.map f
  have h_le : B.edgeFinset.card ≤ extremalNumber β A := by
    apply le_extremalNumber
    have h_col' := Colorable.map f h_col
    exact not_isIsoSubgraph_of_colorable nh_col h_col'
  rw [←card_edgeFinset_map G f] at h
  apply lt_of_lt_of_le h
  rw [Nat.cast_le]
  exact h_le

end CompleteEquipartiteGraph
