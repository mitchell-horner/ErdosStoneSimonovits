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

/-- The `completeEquipartiteGraph α β` has no edges iff `α` contains at most
one element or `β` is empty. -/
theorem isEmpty_completeEquipartiteGraph_edgeSet_iff :
    IsEmpty (completeEquipartiteGraph α β).edgeSet
      ↔ Subsingleton α ∨ IsEmpty β := by
  rw [←not_iff_not, not_or, not_isEmpty_iff, not_subsingleton_iff_nontrivial,
    not_isEmpty_iff]
  constructor
  . intro ⟨e, he⟩
    rw [show e = s(e.out.1, e.out.2) by simp, mem_edgeSet,
      completeEquipartiteGraph_adj] at he
    exact ⟨⟨e.out.1.1, e.out.2.1, he⟩, ⟨e.out.1.2⟩⟩
  . intro ⟨h_nontrivial, h_nonempty⟩
    have ⟨a₁, a₂, ha⟩ := h_nontrivial
    have ⟨b⟩ := h_nonempty
    let e : (completeEquipartiteGraph α β).edgeSet := by
      use s((a₁, b), (a₂, b))
      rw [mem_edgeSet, completeEquipartiteGraph_adj]
      exact ha
    exact ⟨e⟩

instance isEmpty_completeEquipartiteGraph_edgeSet_of_subsingleton
    [Subsingleton α] : IsEmpty (completeEquipartiteGraph α β).edgeSet := by
  rw [isEmpty_completeEquipartiteGraph_edgeSet_iff]
  left
  infer_instance

instance isEmpty_completeEquipartiteGraph_edgeSet_of_isEmpty
    [IsEmpty β] : IsEmpty (completeEquipartiteGraph α β).edgeSet := by
  rw [isEmpty_completeEquipartiteGraph_edgeSet_iff]
  right
  infer_instance

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

/-- If `A` is not `n`-colorable and `G` is `n`-colorable, `G` is `A`-free. -/
lemma free_of_colorable (nh_col : ¬A.Colorable n)
    (h_col : G.Colorable n) : A.Free G := by
  contrapose! nh_col
  rw [not_not] at nh_col
  exact Colorable.mono_of_isIsoSubgraph nh_col h_col

/-- If `G` is not `n`-colorable then `completeEquipartiteGraph (Fin n) β` is
`G`-free. -/
theorem completeEquipartiteGraph_free_of_not_colorable
    {n : ℕ} (h : ¬G.Colorable n) :
    G.Free (completeEquipartiteGraph (Fin n) β) := by
  apply free_of_colorable h
  conv_rhs =>
    rw [←Fintype.card_fin n]
  exact completeEquipartiteGraph_colorable

instance [DecidableEq α] {C : Coloring G α} {c : α} :
    DecidablePred (· ∈ C.colorClass c) := by
  conv_rhs =>
    intro; rw [Coloring.colorClass, Set.mem_setOf_eq]
  infer_instance

/-- If `G` is `n`-colorable then `completeEquipartiteGraph (Fin n) β`
contains `G` for sufficently large `β`. -/
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
  obtain ⟨hC_eq : C v = C w, hι_eq : ι (C v) ⟨v, _⟩ = ι (C w) ⟨w, _⟩⟩ := by
    rwa [Prod.mk.injEq] at hvw
  have hv_mem : v ∈ C.colorClass (C w) := by
    rw [Coloring.colorClass, Set.mem_setOf]
    exact hC_eq
  have hι_eq' : ι (C v) ⟨v, C.mem_colorClass v⟩ = ι (C w) ⟨v, hv_mem⟩ := by
    apply congr_heq
    . rw [hC_eq]
    . rw [Subtype.heq_iff_coe_eq]
      intro _
      rw [hC_eq]
  rw [hι_eq'] at hι_eq
  rw [←Subtype.mk.injEq]
  exact (ι (C w)).injective hι_eq

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
`V ↪ β` is `A`-free. -/
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
    exact free_of_colorable nh_col h_col'
  rw [←card_edgeFinset_map G f] at h
  apply lt_of_lt_of_le h
  rw [Nat.cast_le]
  exact h_le

end CompleteEquipartiteGraph

section CompleteBipartiteGraph

/-- The construction of a subgraph isomorphism of
`completeBipartiteGraph α β`. -/
theorem isIsoSubgraph_completeBipartiteGraph_iff
    [Fintype α] [Fintype β] [Fintype V] {G : SimpleGraph V}:
    (completeBipartiteGraph α β).IsIsoSubgraph G
      ↔ ∃ (A : Finset.univ.powersetCard (Fintype.card α))
        (B : Finset.univ.powersetCard (Fintype.card β)),
          ∀ v₁ ∈ A.val, ∀ v₂ ∈ B.val, G.Adj v₁ v₂ := by
  constructor
  . intro ⟨f⟩
    let A := Finset.univ.map ⟨f ∘ Sum.inl, f.injective.comp Sum.inl_injective⟩
    have hA : A ∈ Finset.univ.powersetCard (Fintype.card α) := by
      rw [Finset.mem_powersetCard_univ, Finset.card_map, Finset.card_univ]
    use ⟨A, hA⟩
    let B := Finset.univ.map ⟨f ∘ Sum.inr, f.injective.comp Sum.inr_injective⟩
    have hB : B ∈ Finset.univ.powersetCard (Fintype.card β) := by
      rw [Finset.mem_powersetCard_univ, Finset.card_map, Finset.card_univ]
    use ⟨B, hB⟩
    intro v₁ hv₁ v₂ hv₂
    rw [Finset.mem_map] at hv₁ hv₂
    have ⟨a, _, ha⟩ := hv₁
    have ⟨b, _, hb⟩ := hv₂
    rw [←ha, ←hb]
    apply f.toHom.map_adj
    simp
  . intro ⟨⟨A, hA⟩, ⟨B, hB⟩, h⟩
    rw [Finset.mem_powersetCard_univ] at hA hB
    haveI : Nonempty (α ↪ A) := by
      apply Function.Embedding.nonempty_of_card_le
      rw [Fintype.card_coe]
      exact ge_of_eq hA
    let fa : α ↪ A := Classical.arbitrary (α ↪ A)
    haveI : Nonempty (β ↪ B) := by
      apply Function.Embedding.nonempty_of_card_le
      rw [Fintype.card_coe]
      exact ge_of_eq hB
    let fb : β ↪ B := Classical.arbitrary (β ↪ B)
    let f : α ⊕ β ↪ V := by
      use Sum.elim (Subtype.val ∘ fa) (Subtype.val ∘ fb)
      intro ab₁ ab₂
      match ab₁, ab₂ with
      | Sum.inl a₁, Sum.inl a₂ =>
        simp [←Subtype.ext_iff, fa.injective]
      | Sum.inr b₁, Sum.inl a₂ =>
        suffices h : (fb b₁ : V) ≠ (fa a₂ : V) by
          simp [h]
        apply ne_of_adj
        apply adj_symm
        exact h (fa a₂) (fa a₂).prop (fb b₁) (fb b₁).prop
      | Sum.inl a₁, Sum.inr b₂ =>
        suffices h : (fa a₁ : V) ≠ (fb b₂ : V) by
          simp [h]
        apply ne_of_adj
        exact h (fa a₁) (fa a₁).prop (fb b₂) (fb b₂).prop
      | Sum.inr b₁, Sum.inr b₂ =>
        simp [←Subtype.ext_iff, fa.injective]
    use ⟨f.toFun, ?_⟩
    . exact f.injective
    . intro ab₁ ab₂ hab
      rw [completeBipartiteGraph_adj] at hab
      cases hab with
      | inl hab =>
        conv_lhs => rw [←Sum.inl_getLeft ab₁ hab.1]
        conv_rhs => rw [←Sum.inr_getRight ab₂ hab.2]
        simp_rw [Sum.elim_inl, Sum.elim_inr]
        apply h (fa _) _ (fb _) _
        all_goals simp_rw [Finset.coe_mem]
      | inr hab =>
        conv_lhs => rw [←Sum.inr_getRight ab₁ hab.1]
        conv_rhs => rw [←Sum.inl_getLeft ab₂ hab.2]
        simp_rw [Sum.elim_inl, Sum.elim_inr]
        apply adj_symm
        apply h (fa _) _ (fb _) _
        all_goals simp_rw [Finset.coe_mem]

end CompleteBipartiteGraph

section CompleteGraph

/-- A simple graph does not contain `completeGraph (Fin n)` if and only if it
has no `n`-cliques. -/
theorem completeGraph_free_iff_cliqueFree {n : ℕ} :
    (completeGraph (Fin n)).Free G ↔ G.CliqueFree n := by
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

end CompleteGraph
