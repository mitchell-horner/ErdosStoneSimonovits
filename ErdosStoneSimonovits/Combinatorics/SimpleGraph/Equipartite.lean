import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Coloring
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.Basic

open Fintype Finset

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

section CompleteEquipartiteGraph

variable {α β : Type*}

/-- The **complete equipartite graph** in types `α`, `β` is the simple graph whoes vertices are
copies of `β` indexed by `α`. The vertices of a `completeEquipartiteGraph` are adjacent if and only
if the indexes are equal. -/
abbrev completeEquipartiteGraph (α β : Type*) : SimpleGraph (α × β) :=
  SimpleGraph.comap Prod.fst ⊤

/-- A `completeEquipartiteGraph` is isomorphic to a corresponding `completeMultipartiteGraph`. The
difference is that the former vertices are a product type whereas the latter vertices are a
dependent product type. -/
def completeEquipartiteGraph.completeMultipartiteGraph :
    completeEquipartiteGraph α β ≃g completeMultipartiteGraph (Function.const α β) where
  toFun v := by use v.1, v.2
  invFun v := by use v.1, v.2
  left_inv v := by simp
  right_inv v := by simp
  map_rel_iff' := by simp

@[simp]
lemma completeEquipartiteGraph_adj {v w : α × β} :
    (completeEquipartiteGraph α β).Adj v w ↔ v.1 ≠ w.1 := by rfl

instance [DecidableEq α] : DecidableRel (completeEquipartiteGraph α β).Adj := by
  intro v w
  rw [completeEquipartiteGraph_adj]
  infer_instance

/-- The `completeEquipartiteGraph α β` contains no edges when `α` contains at most `1` element or
`β` is empty. -/
lemma completeEquipartiteGraph_eq_bot_iff :
    completeEquipartiteGraph α β = ⊥ ↔ Subsingleton α ∨ IsEmpty β := by
  rw [← not_iff_not, not_or, ← ne_eq, ← edgeSet_nonempty,
    not_isEmpty_iff, not_subsingleton_iff_nontrivial]
  constructor
  · intro ⟨e, he⟩
    induction' e with v w
    rw [mem_edgeSet, completeEquipartiteGraph_adj] at he
    exact ⟨⟨v.1, w.1, he⟩, ⟨v.2⟩⟩
  · intro ⟨⟨a₁, a₂, ha⟩, ⟨b⟩⟩
    use s((a₁, b), (a₂, b))
    rw [mem_edgeSet, completeEquipartiteGraph_adj]
    exact ha

theorem completeEquipartiteGraph_eq_bot_of_subsingleton [Subsingleton α] :
    completeEquipartiteGraph α β = ⊥ := by
  rw [completeEquipartiteGraph_eq_bot_iff]
  exact Or.inl inferInstance

theorem completeEquipartiteGraph_eq_bot_of_isEmpty [IsEmpty β] :
    completeEquipartiteGraph α β = ⊥ := by
  rw [completeEquipartiteGraph_eq_bot_iff]
  exact Or.inr inferInstance

theorem neighborSet_completeEquipartiteGraph (v : α × β) :
    (completeEquipartiteGraph α β).neighborSet v = {v.1}ᶜ ×ˢ Set.univ := by
  ext; simp [ne_comm]

lemma neighborFinset_completeEquipartiteGraph [DecidableEq α] [Fintype α] [Fintype β] (v : α × β) :
    (completeEquipartiteGraph α β).neighborFinset v = {v.1}ᶜ ×ˢ univ := by
  ext; simp [ne_comm]

theorem degree_completeEquipartiteGraph [DecidableEq α] [Fintype α] [Fintype β] (v : α × β) :
    (completeEquipartiteGraph α β).degree v = ((card α)-1)*(card β) := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_completeEquipartiteGraph v,
    card_product, card_compl, card_singleton, card_univ]

theorem card_edgeFinset_completeEquipartiteGraph [DecidableEq α] [Fintype α] [Fintype β] :
    #(completeEquipartiteGraph α β).edgeFinset = ((card α).choose 2)*(Fintype.card β)^2 := by
  rw [← mul_right_inj' two_ne_zero, ← sum_degrees_eq_twice_card_edges,]
  conv_lhs =>
    rhs; intro v
    rw [degree_completeEquipartiteGraph v]
  rw [sum_const, smul_eq_mul, card_univ, card_prod]
  conv_rhs =>
    rw [← Nat.mul_assoc, Nat.choose_two_right,
      Nat.mul_div_cancel' (card α).even_mul_pred_self.two_dvd]
  rw [← mul_assoc, mul_comm (card α) _, mul_assoc (card β) _ _,
    mul_comm (card β), mul_assoc _ (card β), ← pow_two]

section Coloring

/-- The injection `(a, b) ↦ a` is always a `α`-coloring of a `completeEquipartiteGraph α ·`. -/
def Coloring.completeEquipartiteGraph :
  (completeEquipartiteGraph α β).Coloring α := ⟨Prod.fst, id⟩

theorem completeEquipartiteGraph_colorable [Fintype α] :
    (completeEquipartiteGraph α β).Colorable (card α) :=
  Coloring.colorable Coloring.completeEquipartiteGraph

/-- The `completeEquipartiteGraph (Fin n) ·` is always `n`-colorable. -/
theorem completeEquipartiteGraph_colorable_overFin {n : ℕ} :
    (completeEquipartiteGraph (Fin n) β).Colorable n := by
  conv_rhs =>
    rw [← Fintype.card_fin n]
  exact completeEquipartiteGraph_colorable

/-- Every `n`-colorable graph is contained in the `completeEquipartiteGraph` in `n` parts (as long
  as the parts are at least as large as the largest color class). -/
theorem isContained_completeEquipartiteGraph_of_colorable [Fintype V]
    {n : ℕ} (h : G.Colorable n) :
    ∃ b, ∀ {β : Type*} [Fintype β], b ≤ card β → G ⊑ completeEquipartiteGraph (Fin n) β := by
  let C := h.some
  use univ.sup fun c ↦ card (C.colorClass c)
  intro β _ hcardβ
  haveI (c) : Nonempty (C.colorClass c ↪ β) := Function.Embedding.nonempty_of_card_le <|
      hcardβ.trans' <| le_sup (f := fun c ↦ card (C.colorClass c)) (mem_univ c)
  have ι (c) := Classical.arbitrary (C.colorClass c ↪ β)
  have hι_ceq {c₁ c₂} {v} {w} (hc_eq : c₁ = c₂) (hι_eq : ι c₁ v = ι c₂ w) : v.val = w.val := by
    let v' : C.colorClass c₂ := by
      use v
      rw [← hc_eq]
      exact v.prop
    have hι_eq' : ι c₁ v = ι c₂ v' := by
      apply congr_heq
      · rw [hc_eq]
      · rw [Subtype.heq_iff_coe_eq]
        simp [hc_eq]
    rw [hι_eq'] at hι_eq
    simpa [Subtype.ext_iff] using (ι c₂).injective hι_eq
  use ⟨fun v ↦ (C v, ι (C v) ⟨v, C.mem_colorClass v⟩), C.valid⟩
  intro _ _ h_eq
  rw [Prod.mk.injEq] at h_eq
  exact hι_ceq h_eq.1 h_eq.2

end Coloring

end CompleteEquipartiteGraph

section CompleteEquipartiteSubgraph

variable [Fintype V]

/-- A complete equipartite subgraph in `α` parts each of size `card β` in `G` is `card α` subsets
of vertices each of size `card β` such that vertices in distinct subsets are adjacent. -/
structure completeEquipartiteSubgraph (G : SimpleGraph V) (α β : Type*) [Fintype β] where
  parts : α → @univ.powersetCard V (Fintype.card β)
  Adj : ∀ ⦃a₁ a₂⦄, a₁ ≠ a₂ → ∀ v ∈ (parts a₁).val, ∀ w ∈ (parts a₂).val, G.Adj v w

variable {α β : Type*} [Fintype α] [Fintype β] (A : G.completeEquipartiteSubgraph α β)

namespace completeEquipartiteSubgraph

omit [Fintype α] in
/-- The size of any part of a `G.completeEquipartiteSubgraph α β` is `card β`. -/
theorem card_parts (a : α) : #(A.parts a).val = card β := by
  have hmem := (A.parts a).prop
  rw [mem_powersetCard] at hmem
  exact hmem.2

/-- The parts in a `G.completeEquipartiteSubgraph α β` are pairwise disjoint. -/
theorem pairwiseDisjoint_parts :
    univ.toSet.PairwiseDisjoint (Subtype.val ∘ A.parts) := by
  intro _ _ _ _ h
  rw [Function.onFun_apply, disjoint_left]
  intro v h₁
  have nhadj : ¬G.Adj v v := G.loopless v
  contrapose! nhadj with h₂
  exact A.Adj h v h₁ v h₂

/-- The finset of vertices in a `G.completeEquipartiteSubgraph r t`. -/
abbrev verts : Finset V := univ.disjiUnion (Subtype.val ∘ A.parts) A.pairwiseDisjoint_parts

/-- There are `r*t` vertices in a `G.completeEquipartiteSubgraph r t`. -/
theorem card_verts : #A.verts = (card α)*(card β) := by
  simp [card_disjiUnion, Function.comp_apply, card_parts]

noncomputable def toCopy : Copy (completeEquipartiteGraph α β) G := by
  have h_cardEq {a : α} : card (A.parts a) = card β := by
    simpa [card_coe] using A.card_parts a
  let fₐ (a : α) : β ↪ A.parts a := (Fintype.equivOfCardEq h_cardEq).symm.toEmbedding
  let f : α × β ↪ V := by
    use fun (a, b) ↦ fₐ a b
    intro (a₁, b₁) (a₂, b₂) heq
    rw [Prod.mk.injEq]
    contrapose! heq with hne
    rcases eq_or_ne a₁ a₂ with heq | hne
    · rw [heq, ← Subtype.ext_iff_val.ne]
      exact (fₐ a₂).injective.ne (hne heq)
    · exact (A.Adj hne _ (fₐ a₁ b₁).prop _ (fₐ a₂ b₂).prop).ne
  use ⟨f, ?_⟩, f.injective
  intro (a₁, b₁) (a₂, b₂) ha
  exact A.Adj ha _ (fₐ a₁ b₁).prop _ (fₐ a₂ b₂).prop

def ofCopy (f : Copy (completeEquipartiteGraph α β) G) : G.completeEquipartiteSubgraph α β where
  parts a := by
    let fₐ (a : α) : β ↪ V := by
      use fun b ↦ f (a, b)
      intro _ _ h
      simpa using f.injective h
    use univ.map (fₐ a), by simp
  Adj := by
    intro _ _ hne _ hv₁ _ hv₂
    rw [mem_map] at hv₁ hv₂
    obtain ⟨_, _, hb₁⟩ := hv₁
    obtain ⟨_, _, hb₂⟩ := hv₂
    rw [← hb₁, ← hb₂]
    exact f.toHom.map_adj hne

end completeEquipartiteSubgraph

omit [Fintype α] in
/-- Simple graphs contain a copy of a `completeEquipartiteGraph α β` iff the type of
`G.completeEquipartiteSubgraph α β` are nonempty. -/
theorem completeEquipartiteGraph_isContained_iff :
    completeEquipartiteGraph α β ⊑ G ↔ Nonempty (G.completeEquipartiteSubgraph α β) :=
  ⟨fun ⟨f⟩ ↦ ⟨completeEquipartiteSubgraph.ofCopy f⟩, fun ⟨A⟩ ↦ ⟨A.toCopy⟩⟩

/-- Simple graphs contain a copy of a `completeEquipartiteGraph (Fin (n+1)) β` iff there exists
`s : univ.powersetCard (card β)` and `A : G.completeEquipartiteSubgraph (Fin n) β` such that the
vertices in `s` are adjacent to the vertices in `A`. -/
theorem completeEquipartiteGraph_succ_isContained_iff {n : ℕ} [Nonempty β] :
  completeEquipartiteGraph (Fin (n+1)) β ⊑ G
    ↔ ∃ (A : G.completeEquipartiteSubgraph (Fin n) β) (s : univ.powersetCard (Fintype.card β)),
        ∀ v₁ ∈ s.val, ∀ i, ∀ v₂ ∈ (A.parts i).val, G.Adj v₁ v₂ := by
  rw [completeEquipartiteGraph_isContained_iff]
  constructor
  · intro ⟨A'⟩
    let A : G.completeEquipartiteSubgraph (Fin n) β := by
      use fun i ↦ A'.parts i.castSucc
      intro i j hne v₁ hv₁ v₂ hv₂
      rw [← Fin.castSucc_inj.ne] at hne
      exact A'.Adj hne v₁ hv₁ v₂ hv₂
    let s : (univ : Finset V).powersetCard (Fintype.card β) := by
      use A'.parts (Fin.last n)
      rw [mem_powersetCard_univ]
      exact A'.card_parts (Fin.last n)
    use A, s
    intro v₁ hv₁ i v₂ hv₂
    have hne : i.castSucc ≠ Fin.last n := Fin.exists_castSucc_eq.mp ⟨i, rfl⟩
    exact (A'.Adj hne v₂ hv₂ v₁ hv₁).symm
  · intro ⟨A, s, hs⟩
    use fun i ↦ if hi : ↑i < n then A.parts ⟨i, hi⟩ else s
    intro i j hne v₁ hv₁ v₂ hv₂
    by_cases hi : ↑i < n <;> by_cases hj : ↑j < n
    all_goals simp only [hi, hj, ↓reduceDIte] at hne hv₁ hv₂ ⊢
    · have hne : i.castLT hi ≠ j.castLT hj := by rwa [Fin.ext_iff.ne] at hne ⊢
      exact A.Adj hne v₁ hv₁ v₂ hv₂
    · exact (hs v₂ hv₂ ⟨i, hi⟩ v₁ hv₁).symm
    · exact hs v₁ hv₁ ⟨j, hj⟩ v₂ hv₂
    · absurd hne
      rw [Fin.ext_iff, Nat.eq_of_le_of_lt_succ (le_of_not_lt hi) i.isLt,
        Nat.eq_of_le_of_lt_succ (le_of_not_lt hj) j.isLt]

end CompleteEquipartiteSubgraph

end SimpleGraph
