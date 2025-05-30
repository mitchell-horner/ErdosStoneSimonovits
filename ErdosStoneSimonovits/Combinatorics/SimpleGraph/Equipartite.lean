import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Coloring
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.Basic

open Fintype Finset

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

section CompleteEquipartiteGraph

variable {r t : ℕ}

/-- The **complete equipartite graph** in types `r`, `t` is the simple graph whoes vertices are
copies of `t` indexed by `r`. The vertices of a `completeEquipartiteGraph` are adjacent if and only
if the indexes are equal. -/
abbrev completeEquipartiteGraph (r t : ℕ) : SimpleGraph ((Fin r) × (Fin t)) :=
  (⊤ : SimpleGraph (Fin r)).comap Prod.fst

/-- A `completeEquipartiteGraph` is isomorphic to a corresponding `completeMultipartiteGraph`.

The difference is that the former vertices are a product type whereas the latter vertices are a
dependent product type. -/
def completeEquipartiteGraph.completeMultipartiteGraph :
    completeEquipartiteGraph r t ≃g completeMultipartiteGraph (Function.const (Fin r) (Fin t)) where
  toFun := fun (v₁, v₂) ↦ by
    use v₁, v₂, v₂.is_lt
  invFun := fun ⟨v₁, v₂⟩ ↦ by
    rw [Function.const_apply] at v₂
    use v₁, v₂, v₂.is_lt
  left_inv v := by simp
  right_inv v := by simp
  map_rel_iff' := by simp

@[simp]
lemma completeEquipartiteGraph_adj {v w} :
    (completeEquipartiteGraph r t).Adj v w ↔ v.1 ≠ w.1 := by rfl

/-- The `completeEquipartiteGraph r t` contains no edges when `r ≤ 1` or `t = 0`. -/
lemma completeEquipartiteGraph_eq_bot_iff :
    completeEquipartiteGraph r t = ⊥ ↔ r ≤ 1 ∨ t = 0 := by
  rw [← not_iff_not, not_or, ← ne_eq, ← edgeSet_nonempty, not_le, ← Nat.succ_le_iff,
    ← Fin.nontrivial_iff_two_le, ← ne_eq, ← Nat.pos_iff_ne_zero, Fin.pos_iff_nonempty]
  constructor
  · intro ⟨e, he⟩
    induction' e with v₁ v₂
    rw [mem_edgeSet, completeEquipartiteGraph_adj] at he
    exact ⟨⟨v₁.1, v₂.1, he⟩, ⟨v₁.2⟩⟩
  · intro ⟨⟨i₁, i₂, hv⟩, ⟨x⟩⟩
    use s((i₁, x), (i₂, x))
    rw [mem_edgeSet, completeEquipartiteGraph_adj]
    exact hv

theorem neighborSet_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).neighborSet v = {v.1}ᶜ ×ˢ Set.univ := by
  ext; simp [ne_comm]

lemma neighborFinset_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).neighborFinset v = {v.1}ᶜ ×ˢ univ := by
  ext; simp [ne_comm]

theorem degree_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).degree v = (r-1) * t := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_completeEquipartiteGraph v,
    card_product, card_compl, card_singleton, Fintype.card_fin, card_univ, Fintype.card_fin]

theorem card_edgeFinset_completeEquipartiteGraph :
    #(completeEquipartiteGraph r t).edgeFinset = (r.choose 2) * t^2 := by
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

/-- Every `n`-colorable graph is contained in the `completeEquipartiteGraph` in `n` parts (as long
  as the parts are at least as large as the largest color class). -/
theorem isContained_completeEquipartiteGraph_of_colorable [Fintype V]
    {n : ℕ} (h : G.Colorable n) : ∃ t, G ⊑ completeEquipartiteGraph n t := by
  let C := h.some
  let t := univ.sup (fun c ↦ card (C.colorClass c))
  use t
  haveI (c) : Nonempty (C.colorClass c ↪ (Fin t)) := by
    rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_fin]
    apply @le_sup _ _ _ _ _ (fun c ↦ card (C.colorClass c)) c (mem_univ c)
  have ι (c) := Classical.arbitrary (C.colorClass c ↪ (Fin t))
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

/-- The complete equipartite subgraphs in `r` parts each of size `t` in `G` are the `r` subsets
of vertices each of size `t` such that vertices in distinct subsets are adjacent. -/
structure completeEquipartiteSubgraph (G : SimpleGraph V) (r t : ℕ) where
  parts : Fin r → @univ.powersetCard V t
  Adj : ∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → ∀ v ∈ (parts i₁).val, ∀ w ∈ (parts i₂).val, G.Adj v w

variable {r t : ℕ} (A : G.completeEquipartiteSubgraph r t)

namespace completeEquipartiteSubgraph

/-- The size of any part of a `G.completeEquipartiteSubgraph r t` is `t`. -/
theorem card_parts (i : Fin r) : #(A.parts i).val = t := by
  have hmem := (A.parts i).prop
  rw [mem_powersetCard] at hmem
  exact hmem.2

/-- The parts in a `G.completeEquipartiteSubgraph r t` are pairwise disjoint. -/
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
theorem card_verts : #A.verts = r * t := by
  simp [card_disjiUnion, Function.comp_apply, card_parts]

noncomputable def toCopy : Copy (completeEquipartiteGraph r t) G := by
  have h_card_eq {i} : card (A.parts i) = t := by
    simpa [card_coe] using A.card_parts i
  haveI (i) : Nonempty (Fin t ↪ A.parts i) := by
    rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_fin, h_card_eq]
  have fᵣ (i) : Fin t ↪ A.parts i := Classical.arbitrary (Fin t ↪ A.parts i)
  let f : (Fin r) × (Fin t) ↪ V := by
    use fun (i, x) ↦ fᵣ i x
    intro (i₁, x₁) (i₂, x₂) heq
    rw [Prod.mk.injEq]
    contrapose! heq with hne
    rcases eq_or_ne i₁ i₂ with heq | hne
    · rw [heq, ← Subtype.ext_iff_val.ne]
      exact (fᵣ i₂).injective.ne (hne heq)
    · exact (A.Adj hne _ (fᵣ i₁ x₁).prop _ (fᵣ i₂ x₂).prop).ne
  use ⟨f, ?_⟩, f.injective
  intro (i₁, x₁) (i₂, x₂) hr
  exact A.Adj hr _ (fᵣ i₁ x₁).prop _ (fᵣ i₂ x₂).prop

def ofCopy (f : Copy (completeEquipartiteGraph r t) G) : G.completeEquipartiteSubgraph r t where
  parts a := by
    let fᵣ (i : Fin r) : Fin t ↪ V := by
      use fun x ↦ f (i, x)
      intro _ _ h
      simpa using f.injective h
    use univ.map (fᵣ a), by simp
  Adj := by
    intro _ _ hne _ hv₁ _ hv₂
    rw [mem_map] at hv₁ hv₂
    obtain ⟨_, _, hb₁⟩ := hv₁
    obtain ⟨_, _, hb₂⟩ := hv₂
    rw [← hb₁, ← hb₂]
    exact f.toHom.map_adj hne

end completeEquipartiteSubgraph

/-- Simple graphs contain a copy of a `completeEquipartiteGraph r t` iff the type of
`G.completeEquipartiteSubgraph r t` are nonempty. -/
theorem completeEquipartiteGraph_isContained_iff :
    completeEquipartiteGraph r t ⊑ G ↔ Nonempty (G.completeEquipartiteSubgraph r t) :=
  ⟨fun ⟨f⟩ ↦ ⟨completeEquipartiteSubgraph.ofCopy f⟩, fun ⟨A⟩ ↦ ⟨A.toCopy⟩⟩

/-- Simple graphs contain a copy of a `completeEquipartiteGraph (n+1) t` iff there exists
`s : univ.powersetCard t` and `A : G.completeEquipartiteSubgraph n t` such that the vertices
in `s` are adjacent to the vertices in `A`. -/
theorem completeEquipartiteGraph_succ_isContained_iff {n : ℕ} :
  completeEquipartiteGraph (n+1) t ⊑ G
    ↔ ∃ (A : G.completeEquipartiteSubgraph n t) (s : univ.powersetCard t),
        ∀ v₁ ∈ s.val, ∀ i, ∀ v₂ ∈ (A.parts i).val, G.Adj v₁ v₂ := by
  rw [completeEquipartiteGraph_isContained_iff]
  constructor
  · intro ⟨A'⟩
    let A : G.completeEquipartiteSubgraph n t := by
      use fun i ↦ A'.parts i.castSucc
      intro i₁ i₂ hne v₁ hv₁ v₂ hv₂
      rw [← Fin.castSucc_inj.ne] at hne
      exact A'.Adj hne v₁ hv₁ v₂ hv₂
    let s : (univ : Finset V).powersetCard t := by
      use A'.parts (Fin.last n)
      rw [mem_powersetCard_univ]
      exact A'.card_parts (Fin.last n)
    use A, s
    intro v₁ hv₁ i v₂ hv₂
    have hne : i.castSucc ≠ Fin.last n := Fin.exists_castSucc_eq.mp ⟨i, rfl⟩
    exact (A'.Adj hne v₂ hv₂ v₁ hv₁).symm
  · intro ⟨A, s, hs⟩
    use fun i ↦ if hi : ↑i < n then A.parts ⟨i, hi⟩ else s
    intro i₁ i₂ hne v₁ hv₁ v₂ hv₂
    by_cases hi₁ : ↑i₁ < n <;> by_cases hi₂ : ↑i₂ < n
    all_goals simp only [hi₁, hi₂, ↓reduceDIte] at hne hv₁ hv₂ ⊢
    · have hne : i₁.castLT hi₁ ≠ i₂.castLT hi₂ := by rwa [Fin.ext_iff.ne] at hne ⊢
      exact A.Adj hne v₁ hv₁ v₂ hv₂
    · exact (hs v₂ hv₂ ⟨i₁, hi₁⟩ v₁ hv₁).symm
    · exact hs v₁ hv₁ ⟨i₂, hi₂⟩ v₂ hv₂
    · absurd hne
      rw [Fin.ext_iff, Nat.eq_of_le_of_lt_succ (le_of_not_lt hi₁) i₁.isLt,
        Nat.eq_of_le_of_lt_succ (le_of_not_lt hi₂) i₂.isLt]

end CompleteEquipartiteSubgraph

end SimpleGraph
