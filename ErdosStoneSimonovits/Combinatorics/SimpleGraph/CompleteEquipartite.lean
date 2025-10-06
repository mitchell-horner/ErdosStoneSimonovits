import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Coloring
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.Turan

open Fintype Finset Function

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

section CompleteEquipartiteGraph

variable {r t : ℕ}

/-- The **complete equipartite graph** in `r` parts each of *equal* size `t` such that two
vertices are adjacent if and only if they are in different parts, often denoted $K_r(t)$.

This is isomorphic to a corresponding `completeMultipartiteGraph` and `turanGraph`. The difference
is that the former vertices are a product type.

See `completeEquipartiteGraph.completeMultipartiteGraph`, `completeEquipartiteGraph.turanGraph`. -/
abbrev completeEquipartiteGraph (r t : ℕ) : SimpleGraph (Fin r × Fin t) :=
  SimpleGraph.comap Prod.fst ⊤

/-- A `completeEquipartiteGraph` is isomorphic to a corresponding `completeMultipartiteGraph`.

The difference is that the former vertices are a product type whereas the latter vertices are a
*dependent* product type. -/
def completeEquipartiteGraph.completeMultipartiteGraph :
    completeEquipartiteGraph r t ≃g completeMultipartiteGraph (const (Fin r) (Fin t)) :=
  { (Equiv.sigmaEquivProd (Fin r) (Fin t)).symm with map_rel_iff' := by simp }

lemma completeEquipartiteGraph_adj {v w} :
  (completeEquipartiteGraph r t).Adj v w ↔ v.1 ≠ w.1 := by rfl

/-- A `completeEquipartiteGraph` is isomorphic to a corresponding `turanGraph`.

The difference is that the former vertices are a product type whereas the latter vertices are
not. -/
def completeEquipartiteGraph.turanGraph :
    completeEquipartiteGraph r t ≃g turanGraph (r * t) r where
  toFun := by
    refine fun v ↦ ⟨v.2 * r + v.1, ?_⟩
    conv_rhs =>
      rw [← Nat.sub_one_add_one_eq_of_pos v.2.pos, Nat.mul_add_one, mul_comm r (t - 1)]
    exact add_lt_add_of_le_of_lt (Nat.mul_le_mul_right r (Nat.le_pred_of_lt v.2.prop)) v.1.prop
  invFun := by
    refine fun v ↦ (⟨v % r, ?_⟩, ⟨v / r, ?_⟩)
    · have ⟨hr, _⟩ := CanonicallyOrderedCommSemiring.mul_pos.mp v.pos
      exact Nat.mod_lt v hr
    · exact Nat.div_lt_of_lt_mul v.prop
  left_inv v := by
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · conv =>
        enter [1, 1, 1, 1, 1]
        rw [Nat.mul_add_mod_self_right]
      exact Nat.mod_eq_of_lt v.1.prop
    · apply le_antisymm
      · rw [Nat.div_le_iff_le_mul_add_pred v.1.pos, mul_comm r ↑v.2]
        exact Nat.add_le_add_left (Nat.le_pred_of_lt v.1.prop) (↑v.2 * r)
      · rw [Nat.le_div_iff_mul_le v.1.pos]
        exact Nat.le_add_right (↑v.2 * r) ↑v.1
  right_inv v := Fin.ext (Nat.div_add_mod' v r)
  map_rel_iff' {v w} := by
    rw [turanGraph_adj, Equiv.coe_fn_mk, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt v.1.prop,
      Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt w.1.prop, ← Fin.ext_iff.ne,
      ← completeEquipartiteGraph_adj]

/-- `completeEquipartiteGraph r t` contains no edges when `r ≤ 1` or `t = 0`. -/
lemma completeEquipartiteGraph_eq_bot_iff :
    completeEquipartiteGraph r t = ⊥ ↔ r ≤ 1 ∨ t = 0 := by
  rw [← not_iff_not, not_or, ← ne_eq, ← edgeSet_nonempty, not_le, ← Nat.succ_le_iff,
    ← Fin.nontrivial_iff_two_le, ← ne_eq, ← Nat.pos_iff_ne_zero, Fin.pos_iff_nonempty]
  refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨⟨i₁, i₂, hv⟩, ⟨x⟩⟩ ↦ ?_⟩
  · induction' e with v₁ v₂
    rw [mem_edgeSet, completeEquipartiteGraph_adj] at he
    exact ⟨⟨v₁.1, v₂.1, he⟩, ⟨v₁.2⟩⟩
  · use s((i₁, x), (i₂, x))
    rw [mem_edgeSet, completeEquipartiteGraph_adj]
    exact hv

theorem neighborSet_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).neighborSet v = {v.1}ᶜ ×ˢ Set.univ := by
  ext; simp [ne_comm]

theorem neighborFinset_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).neighborFinset v = {v.1}ᶜ ×ˢ univ := by
  ext; simp [ne_comm]

theorem degree_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).degree v = (r - 1) * t := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_completeEquipartiteGraph v,
    card_product, card_compl, card_singleton, Fintype.card_fin, card_univ, Fintype.card_fin]

theorem card_edgeFinset_completeEquipartiteGraph :
    #(completeEquipartiteGraph r t).edgeFinset = r.choose 2 * t ^ 2 := by
  rw [← mul_right_inj' two_ne_zero, ← sum_degrees_eq_twice_card_edges]
  conv_lhs =>
    rhs; intro v
    rw [degree_completeEquipartiteGraph v]
  rw [sum_const, smul_eq_mul, card_univ, card_prod, Fintype.card_fin, Fintype.card_fin]
  conv_rhs =>
    rw [← Nat.mul_assoc, Nat.choose_two_right, Nat.mul_div_cancel' r.even_mul_pred_self.two_dvd]
  rw [← mul_assoc, mul_comm r _, mul_assoc t _ _, mul_comm t, mul_assoc _ t, ← pow_two]

section Coloring

/-- The injection `(x₁, x₂) ↦ x₁` is always a `r`-coloring of a `completeEquipartiteGraph r ·`. -/
def Coloring.completeEquipartiteGraph :
  (completeEquipartiteGraph r t).Coloring (Fin r) := ⟨Prod.fst, id⟩

/-- The `completeEquipartiteGraph r t` is always `r`-colorable. -/
theorem completeEquipartiteGraph_colorable :
  (completeEquipartiteGraph r t).Colorable r := ⟨Coloring.completeEquipartiteGraph⟩

variable [Fintype V]

/-- Every `n`-colorable graph is contained in a `completeEquipartiteGraph` in `n` parts (as long
  as the parts are at least as large as the largest color class). -/
theorem isContained_completeEquipartiteGraph_of_colorable {n : ℕ} (C : G.Coloring (Fin n))
    (t : ℕ) (h : ∀ c, card (C.colorClass c) ≤ t) : G ⊑ completeEquipartiteGraph n t := by
  have (c : Fin n) : Nonempty (C.colorClass c ↪ Fin t) := by
    rw [Embedding.nonempty_iff_card_le, Fintype.card_fin]
    exact h c
  have F (c : Fin n) := Classical.arbitrary (C.colorClass c ↪ Fin t)
  have hF {c₁ c₂ v₁ v₂} (hc : c₁ = c₂) (hv : F c₁ v₁ = F c₂ v₂) : v₁.val = v₂.val := by
    let v₁' : C.colorClass c₂ := ⟨v₁, by simp [← hc]⟩
    have hv' : F c₁ v₁ = F c₂ v₁' := by
      apply congr_heq
      · rw [hc]
      · rw [Subtype.heq_iff_coe_eq]
        simp [hc]
    rw [hv'] at hv
    simpa [Subtype.ext_iff] using (F c₂).injective hv
  use ⟨fun v ↦ (C v, F (C v) ⟨v, C.mem_colorClass v⟩), C.valid⟩
  intro v w h
  rw [Prod.mk.injEq] at h
  exact hF h.1 h.2

end Coloring

end CompleteEquipartiteGraph

section IsCompleteMultipartiteBetween

variable {ι : Type*} {parts : ι → Set V}

def IsCompleteMultipartiteBetween (G : SimpleGraph V) (parts : ι → Set V) :=
  Pairwise fun ⦃i₁ i₂⦄ ↦
    ∀ ⦃v₁⦄, v₁ ∈ parts i₁ → ∀ ⦃v₂⦄, v₂ ∈ parts i₂ → G.Adj v₁ v₂

theorem IsCompleteMultipartiteBetween.pairwise_disjoint
    (h : G.IsCompleteMultipartiteBetween parts) : Pairwise (Disjoint on parts) :=
  fun _ _ hne ↦ Set.disjoint_left.mpr fun v hv₁ hv₂ ↦ (G.loopless v) (h hne hv₁ hv₂)

end IsCompleteMultipartiteBetween

section CompleteEquipartiteSubgraph

/-- A complete equipartite subgraph in `r` parts each of size `t` in `G` is `r` subsets
of vertices each of size `t` such that vertices in distinct subsets are adjacent. -/
structure CompleteEquipartiteSubgraph (G : SimpleGraph V) (r t : ℕ) where
  /-- The `r` parts. -/
  parts : Fin r → Finset V
  /-- Each part is size `t`. -/
  card_parts (i : Fin r) : #(parts i) = t
  /-- Vertices in distinct parts are adjacent. -/
  isCompleteMulitpartiteBetween : G.IsCompleteMultipartiteBetween (toSet ∘ parts)

variable {r t : ℕ} (K : G.CompleteEquipartiteSubgraph r t)

namespace CompleteEquipartiteSubgraph

/-- The parts in a complete equipartite subgraph are pairwise disjoint. -/
theorem pairwise_disjoint_on_parts : Pairwise (Disjoint on K.parts) := by
  simpa [Pairwise, onFun] using K.isCompleteMulitpartiteBetween.pairwise_disjoint

/-- The finset of vertices in a complete equipartite subgraph. -/
abbrev verts : Finset V :=
  univ.disjiUnion K.parts (K.pairwise_disjoint_on_parts.set_pairwise univ.toSet)

/-- There are `r * t` vertices in a complete equipartite subgraph with `r` parts of size `t`. -/
theorem card_verts : #K.verts = r * t := by simp [verts, card_parts]

/-- A complete equipartite subgraph gives rise to a copy of a complete equipartite graph. -/
noncomputable def toCopy : Copy (completeEquipartiteGraph r t) G := by
  have (i : Fin r) : Nonempty (Fin t ↪ K.parts i) := by
    rw [Embedding.nonempty_iff_card_le, Fintype.card_fin, card_coe, K.card_parts i]
  have fᵣ (i : Fin r) : Fin t ↪ K.parts i := Classical.arbitrary (Fin t ↪ K.parts i)
  let f : (Fin r) × (Fin t) ↪ V := by
    use fun (i, x) ↦ fᵣ i x
    intro (i₁, x₁) (i₂, x₂) heq
    rw [Prod.mk.injEq]
    contrapose! heq with hne
    rcases eq_or_ne i₁ i₂ with heq | hne
    · rw [heq, ← Subtype.ext_iff.ne]
      exact (fᵣ i₂).injective.ne (hne heq)
    · exact (K.isCompleteMulitpartiteBetween hne (fᵣ i₁ x₁).prop (fᵣ i₂ x₂).prop).ne
  use ⟨f, ?_⟩, f.injective
  intro (i₁, x₁) (i₂, x₂) hne
  exact K.isCompleteMulitpartiteBetween hne (fᵣ i₁ x₁).prop (fᵣ i₂ x₂).prop

/-- A copy of a complete equipartite graph identifies a complete equipartite subgraph. -/
def ofCopy (f : Copy (completeEquipartiteGraph r t) G) : G.CompleteEquipartiteSubgraph r t where
  parts i := by
    let fᵣ (i : Fin r) : Fin t ↪ V := by
      use fun x ↦ f (i, x)
      intro _ _ h
      simpa using f.injective h
    exact univ.map (fᵣ i)
  card_parts i := by simp
  isCompleteMulitpartiteBetween _ _ hne _ h₁ _ h₂ := by
    simp_rw [comp_apply, mem_coe, mem_map] at h₁ h₂
    obtain ⟨_, _, h₁⟩ := h₁
    obtain ⟨_, _, h₂⟩ := h₂
    rw [← h₁, ← h₂]
    exact f.toHom.map_adj hne

end CompleteEquipartiteSubgraph

/-- Simple graphs contain a copy of a `completeEquipartiteGraph r t` iff the type
`G.CompleteEquipartiteSubgraph r t` is nonempty. -/
theorem completeEquipartiteGraph_isContained_iff :
    completeEquipartiteGraph r t ⊑ G ↔ Nonempty (G.CompleteEquipartiteSubgraph r t) :=
  ⟨fun ⟨f⟩ ↦ ⟨CompleteEquipartiteSubgraph.ofCopy f⟩, fun ⟨K⟩ ↦ ⟨K.toCopy⟩⟩

/-- Simple graphs contain a copy of a `completeEquipartiteGraph (n + 1) t` iff there exists
`s : Finset V` of size `#s = t` and `A : G.CompleteEquipartiteSubgraph n t` such that the
vertices in `s` are adjacent to the vertices in `A`. -/
theorem completeEquipartiteGraph_succ_isContained_iff {n : ℕ} :
  completeEquipartiteGraph (n + 1) t ⊑ G
    ↔ ∃ᵉ (K : G.CompleteEquipartiteSubgraph n t) (s : Finset V),
      #s = t ∧ ∀ ⦃v₁⦄, v₁ ∈ s → ∀ i, ∀ ⦃v₂⦄, v₂ ∈ K.parts i → G.Adj v₁ v₂ := by
  rw [completeEquipartiteGraph_isContained_iff]
  refine ⟨fun ⟨K'⟩ ↦ ?_, fun ⟨K, s, hs, hadj⟩ ↦ ?_⟩
  · let K : G.CompleteEquipartiteSubgraph n t := by
      refine ⟨fun i ↦ K'.parts i.castSucc, fun i ↦ K'.card_parts i.castSucc, ?_⟩
      intro i₁ i₂ hne v₁ hv₁ v₂ hv₂
      rw [← Fin.castSucc_inj.ne] at hne
      exact K'.isCompleteMulitpartiteBetween hne hv₁ hv₂
    refine ⟨K, K'.parts (Fin.last n), K'.card_parts (Fin.last n), fun v₁ hv₁ i v₂ hv₂ ↦ ?_⟩
    have hne : i.castSucc ≠ Fin.last n := Fin.exists_castSucc_eq.mp ⟨i, rfl⟩
    exact (K'.isCompleteMulitpartiteBetween hne hv₂ hv₁).symm
  · refine ⟨fun i ↦ if hi : ↑i < n then K.parts ⟨i, hi⟩ else s, fun i ↦ ?_,
      fun i₁ i₂ hne v₁ hv₁ v₂ hv₂ ↦ ?_⟩
    · by_cases hi : ↑i < n
      · simp [hi, K.card_parts ⟨i, hi⟩]
      · simp [hi, hs]
    · by_cases hi₁ : ↑i₁ < n <;> by_cases hi₂ : ↑i₂ < n
        <;> simp [hi₁, hi₂] at hne hv₁ hv₂ ⊢
      · have hne : i₁.castLT hi₁ ≠ i₂.castLT hi₂ := by
          simp [Fin.ext_iff, Fin.val_ne_of_ne hne]
        exact K.isCompleteMulitpartiteBetween hne hv₁ hv₂
      · exact (hadj hv₂ ⟨i₁, hi₁⟩ hv₁).symm
      · exact hadj hv₁ ⟨i₂, hi₂⟩ hv₂
      · absurd hne
        rw [Fin.ext_iff, Nat.eq_of_le_of_lt_succ (le_of_not_gt hi₁) i₁.isLt,
          Nat.eq_of_le_of_lt_succ (le_of_not_gt hi₂) i₂.isLt]

end CompleteEquipartiteSubgraph

end SimpleGraph
