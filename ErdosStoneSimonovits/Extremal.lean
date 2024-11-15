import Mathlib

namespace SimpleGraph

variable {V α β γ : Type*} {G : SimpleGraph V}
  {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

section SubgraphIso

/-- A subgraph isomorphism is an injective homomorphism.

The notation `G ≲g G'` represents the type of subgrah isomorphisms. -/
abbrev SubgraphIso (A : SimpleGraph α) (B : SimpleGraph β) :=
  { f : A →g B // Function.Injective f}

@[inherit_doc] infixl:50 " ≲g " => SubgraphIso

/-- An injective homomorphism is a subgraph isomorphisms. -/
abbrev Hom.toSubgraphIso (f : A →g B) (h : Function.Injective f) :
  A ≲g B := ⟨f, h⟩

/-- An embedding gives rise to a subgraph isomorphisms. -/
abbrev Embedding.toSubgraphIso (f : A ↪g B) :
  A ≲g B := Hom.toSubgraphIso f.toHom f.injective

/-- An isomorphism gives rise to a subgraph isomorphisms. -/
abbrev Iso.toSubgraphIso (f : A ≃g B) :
  A ≲g B := Embedding.toSubgraphIso f.toEmbedding

namespace SubgraphIso

abbrev toHom : A ≲g B → A →g B := Subtype.val

abbrev injective : (f : A ≲g B) → (Function.Injective f.toHom) := Subtype.prop

instance : FunLike (A ≲g B) α β where
  coe f := DFunLike.coe f.toHom
  coe_injective' _ _ h := Subtype.val_injective (DFunLike.coe_injective h)

instance : EmbeddingLike (A ≲g B) α β where
  injective' f := f.injective

/-- A subgraph isomorphism of simple graphs gives rise to an embedding of
vertex types. -/
abbrev asEmbedding (f : A ≲g B) : α ↪ β := ⟨f, EmbeddingLike.injective f⟩

instance : CoeOut (A ≲g B) (α ↪ β) where
  coe f := f.asEmbedding

/-- A subgraph isomorphism induces an embedding of edge sets. -/
def mapEdgeSet (f : A ≲g B) : A.edgeSet ↪ B.edgeSet where
  toFun := Hom.mapEdgeSet f.toHom
  inj' := Hom.mapEdgeSet.injective f.toHom f.injective

/-- A subgraph isomorphism induces an embedding of neighbor sets. -/
def mapNeighborSet (f : A ≲g B) (a : α) :
    A.neighborSet a ↪ B.neighborSet (f a) where
  toFun v := ⟨f v, f.toHom.apply_mem_neighborSet v.prop⟩
  inj' _ _ h := by
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.injective h

/-- The identity subgraph isomorphism from a simple graph to itself. -/
abbrev refl (G : SimpleGraph V) :
  G ≲g G := ⟨Hom.id, Function.injective_id⟩

/-- The subgraph isomorphism from a subgraph to the supergraph. -/
abbrev ofLE {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) :
  G₁ ≲g G₂ := ⟨Hom.ofLE h, Function.injective_id⟩

/-- The subgraph isomorphism from an induced subgraph to the original simple
graph. -/
abbrev induce (G : SimpleGraph V) (s : Set V) :
  (G.induce s) ≲g G := (Embedding.induce s).toSubgraphIso

/-- The composition of subgraph isomorphisms. -/
abbrev comp (g : B ≲g C) (f : A ≲g B) : A ≲g C := by
  use g.toHom.comp f.toHom
  rw [Hom.coe_comp]
  exact Function.Injective.comp g.injective f.injective

theorem comp_apply (g : B ≲g C) (f : A ≲g B) (a : α) :
  g.comp f a = g (f a) := RelHom.comp_apply g.toHom f.toHom a

end SubgraphIso

end SubgraphIso

section IsoSubgraph

/-- The relation that one `SimpleGraph` is an isomorphic subgraph of another.

The `IsIsoSubgraph` relation is a generalization of the `IsSubgraph` relation
to that of simple graphs of different types. -/
abbrev IsIsoSubgraph (A : SimpleGraph α) (B : SimpleGraph β) :=
  Nonempty (A ≲g B)

/-- A simple graph is an isomorphic subgraph of itself. -/
theorem isIsoSubgraph_refl (G : SimpleGraph V) :
  G.IsIsoSubgraph G := ⟨SubgraphIso.refl G⟩

/-- A subgraph is an isomorphic subgraph of the supergraph. -/
theorem isIsoSubgraph_of_le {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) :
  G₁.IsIsoSubgraph G₂ := ⟨SubgraphIso.ofLE h⟩

/-- The relation `IsIsoSubgraph` is transitive. -/
theorem isIsoSubgraph_trans :
    A.IsIsoSubgraph B → B.IsIsoSubgraph C → A.IsIsoSubgraph C :=
  fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩

alias IsIsoSubgraph.trans := isIsoSubgraph_trans

theorem isIsoSubgraph_trans' :
    B.IsIsoSubgraph C → A.IsIsoSubgraph B → A.IsIsoSubgraph C :=
  flip isIsoSubgraph_trans

alias IsIsoSubgraph.trans' := isIsoSubgraph_trans'

/-- The simple graph with no vertices is an isomorphic subgraph of any simple
graph. -/
theorem isIsoSubgraph_of_isEmpty [IsEmpty α] :
    A.IsIsoSubgraph B := by
  let ι : α ↪ β := Function.Embedding.ofIsEmpty
  let f : A →g B := ⟨ι, by simp⟩
  exact ⟨f.toSubgraphIso ι.injective⟩

/-- The simple graph with no edges is an isomorphic subgraph of any simple
graph with sufficently many vertices. -/
theorem isIsoSubgraph_of_isEmpty_edgeSet [IsEmpty A.edgeSet]
    [Fintype α] [Fintype β] (h_card_le : Fintype.card α ≤ Fintype.card β) :
    A.IsIsoSubgraph B := by
  haveI : Nonempty (α ↪ β) :=
    Function.Embedding.nonempty_of_card_le h_card_le
  let ι : α ↪ β := Classical.arbitrary (α ↪ β)
  let f : A →g B := by
    use ι
    intro a₁ a₂ hadj
    let e : A.edgeSet := by
      use s(a₁, a₂)
      rw [mem_edgeSet]
      exact hadj
    exact isEmptyElim e
  exact ⟨f.toSubgraphIso ι.injective⟩

/-- `⊥ : SimpleGraph α` is an isomorphic subgraph of any simple graph on
the vertex type `β` if and only if `α` embeds into `β`. -/
theorem bot_isIsoSubgraph_iff :
    (⊥ : SimpleGraph α).IsIsoSubgraph B ↔ Nonempty (α ↪ β) :=
  ⟨fun ⟨f⟩ ↦ ⟨f.asEmbedding⟩, fun ⟨f⟩ ↦ ⟨⟨f, by simp⟩, f.injective⟩⟩

/-- If `A ≃g B`, then `A` is an isomorphic subgraph of `C` if and only if `B`
is an isomorphic subgraph of `C`. -/
lemma isIsoSubgraph_iff_of_iso (f : A ≃g B) :
    A.IsIsoSubgraph C ↔ B.IsIsoSubgraph C :=
  ⟨IsIsoSubgraph.trans ⟨f.symm.toSubgraphIso⟩,
    IsIsoSubgraph.trans ⟨f.toSubgraphIso⟩⟩

section ExtremalNumber

open Classical in
/-- The extremal number of a finite type `β` and a simple graph `A` is the
maximal number of edges in a simple graph on the vertex type `β` that does not
contain `A` as an isomorphic subgraph.

Note that if `A` is an isomorphic subgraph of any simple graph on the vertex
type `β` then this is `0`. -/
noncomputable def extremalNumber
    (β : Type*) [Fintype β] (A : SimpleGraph α) : ℕ :=
  Finset.sup (Finset.univ.filter (¬A.IsIsoSubgraph ·) : Finset (SimpleGraph β))
    (·.edgeFinset.card : SimpleGraph β → ℕ)

open Classical in
theorem extremalNumber_eq_sup
    (β : Type*) [Fintype β] (A : SimpleGraph α) : extremalNumber β A =
  Finset.sup (Finset.univ.filter (¬A.IsIsoSubgraph ·) : Finset (SimpleGraph β))
    (·.edgeFinset.card : SimpleGraph β → ℕ) := by rfl

open Classical in
theorem le_extremalNumber [Fintype β] [DecidableRel B.Adj]
    (h : ¬A.IsIsoSubgraph B) :
    B.edgeFinset.card ≤ extremalNumber β A := by
  let s := (Finset.univ.filter (¬A.IsIsoSubgraph ·) : Finset (SimpleGraph β))
  let f := (·.edgeFinset.card : SimpleGraph β → ℕ)
  suffices h : f B ≤ s.sup f by convert h
  apply Finset.le_sup
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ B, h⟩

theorem extremalNumber_lt [Fintype β] [DecidableRel B.Adj]
    (h : extremalNumber β A < B.edgeFinset.card) :
    A.IsIsoSubgraph B := by
  contrapose! h
  exact le_extremalNumber h

theorem extremalNumber_le_iff
    (β : Type*) [Fintype β] (A : SimpleGraph α) (x : ℕ) :
    extremalNumber β A ≤ x ↔ ∀ (B : SimpleGraph β) [DecidableRel B.Adj],
      ¬A.IsIsoSubgraph B → B.edgeFinset.card ≤ x := by
  simp_rw [extremalNumber_eq_sup, Finset.sup_le_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨fun h B _ hB ↦ by convert h B hB, fun h B hB ↦ by convert h B hB⟩

open Classical in
theorem lt_extremalNumber_iff
    (β : Type*) [Fintype β] (A : SimpleGraph α) (x : ℕ) :
    x < extremalNumber β A ↔ ∃ B : SimpleGraph β,
      ¬A.IsIsoSubgraph B ∧ x < B.edgeFinset.card := by
  rw [extremalNumber_eq_sup]; simp

variable {R : Type*} [LinearOrderedSemiring R] [FloorSemiring R] {x : R}

theorem extremalNumber_le_iff_of_nonneg
    (β : Type*) [Fintype β] (A : SimpleGraph α) (hx_nonneg : 0 ≤ x) :
    ↑(extremalNumber β A) ≤ x ↔ ∀ (B : SimpleGraph β) [DecidableRel B.Adj],
      ¬A.IsIsoSubgraph B → ↑B.edgeFinset.card ≤ x := by
  simp_rw [←Nat.le_floor_iff hx_nonneg]
  exact extremalNumber_le_iff β A ⌊x⌋₊

open Classical in
theorem lt_extremalNumber_iff_of_nonneg
    (β : Type*) [Fintype β] (A : SimpleGraph α) (hx_nonneg : 0 ≤ x) :
    x < ↑(extremalNumber β A) ↔ ∃ B : SimpleGraph β,
      ¬A.IsIsoSubgraph B ∧ x < ↑B.edgeFinset.card := by
  simp_rw [←Nat.floor_lt hx_nonneg]
  exact lt_extremalNumber_iff β A ⌊x⌋₊

/-- The extremal numbers of `A` are less than the number of edges in the
complete graph on the vertex type. -/
theorem extremalNumber_le_choose_two
    (β : Type*) [Fintype β] (A : SimpleGraph α) :
    extremalNumber β A ≤ (Fintype.card β).choose 2 := by
  rw [extremalNumber_le_iff]
  intros; exact card_edgeFinset_le_card_choose_two

/-- The extremal numbers of `A` are at most the the extremal numbers of any
simple graph that contains `A` as an isomorphic subgraph. -/
theorem extremalNumber_le_extremalNumber_of_isIsoSubgraph [Fintype β]
    (h : A.IsIsoSubgraph C) :
    extremalNumber β A ≤ extremalNumber β C := by
  rw [extremalNumber_le_iff]
  intro B
  contrapose
  push_neg
  intro h_lt
  exact h.trans (extremalNumber_lt h_lt)

/-- The extremal numbers of isomorphic graphs `A ≃g B` on the isomorphic
types `β ≃ V` are equal. -/
theorem extremalNumber_eq_of_iso
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (f : A ≃g B) (g : V ≃ W) : extremalNumber V A = extremalNumber W B := by
  rw [eq_iff_le_not_lt]
  push_neg
  constructor
  all_goals
    rw [extremalNumber_le_iff]
    intro H _ h
  let F := Iso.map g H
  let G := f.toSubgraphIso
  swap
  let F := Iso.map g.symm H
  let G := f.symm.toSubgraphIso
  all_goals
    rw [Iso.card_edgeFinset_eq F]
    apply le_extremalNumber
    contrapose! h
    apply IsIsoSubgraph.trans ⟨G⟩
    exact h.trans ⟨F.symm.toSubgraphIso⟩

/-- The extremal numbers of `⊥` equal zero. -/
theorem extremalNumber_bot [DecidableEq β] [Fintype β] (h : Nonempty (V ↪ β)) :
    extremalNumber β (⊥ : SimpleGraph V) = 0 := by
  classical
  simp_rw [extremalNumber_eq_sup, bot_isIsoSubgraph_iff, h, not_true,
    Finset.filter_False, Finset.sup_empty]
  exact bot_eq_zero

/-- The extremal numbers of `Fintype.card β ≤ 1` equal zero. -/
theorem extremalNumber_of_card_le_one
    [DecidableEq β] [Fintype β] (h : Fintype.card β ≤ 1) :
    extremalNumber β A = 0 := by
  haveI : Subsingleton β := by
    rwa [Fintype.card_le_one_iff_subsingleton] at h
  simp_rw [extremalNumber_eq_sup, Finset.univ_unique,
    Finset.filter_singleton, instInhabited_default]
  by_cases h : ¬A.IsIsoSubgraph (⊥ : SimpleGraph β)
  all_goals simp [h, -not_nonempty_iff, -nonempty_subtype, -Set.toFinset_card]

open Classical in
/-- There exist extremal graphs on vertex type `V` satisfying the predicate
`p` provided that at least one simple graph on vertex type `V` satisfies the
predicate `p`. -/
theorem exists_extremal_graph [Fintype V]
    (p : SimpleGraph V → Prop) (h : ∃ G, p G) :
    ∃ E : SimpleGraph V, p E ∧
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        p G → G.edgeFinset.card ≤ E.edgeFinset.card := by
  let s := (Finset.univ.filter (p ·) : Finset (SimpleGraph V))
  suffices h : ∃ E ∈ s, ∀ G ∈ s, G.edgeFinset.card ≤ E.edgeFinset.card by
    conv at h =>
      rhs; intro
      rw [Finset.mem_filter]
      rhs; intro
      rw [Finset.mem_filter]
    simp_rw [Finset.mem_univ, true_and] at h
    convert h
    exact ⟨fun h ↦ by convert h, fun h _ ↦ by convert h⟩
  apply Finset.exists_max_image s
  rw [Finset.filter_nonempty_iff]
  convert h
  simp

lemma not_isIsoSubgraph_bot (h : G.edgeSet.Nonempty) :
    ¬G.IsIsoSubgraph (⊥ : SimpleGraph β) := by
  intro ⟨f, _⟩
  rw [←ne_self_iff_false, ←edgeSet_nonempty]
  let ⟨e, he⟩ := h
  exact ⟨e.map f, Hom.map_mem_edgeSet f he⟩

open Classical in
/-- There exist extremal graphs on vertex type `β` that do not contain `A` as
an isomorphic subgraph provided that `A` has at least one edge. -/
theorem exists_extremal_graph_not_isIsoSubgraph [Fintype β]
    (h : A.edgeSet.Nonempty) :
    ∃ E : SimpleGraph β, ¬A.IsIsoSubgraph E ∧
      ∀ (B : SimpleGraph β) [DecidableRel B.Adj],
        ¬A.IsIsoSubgraph B → B.edgeFinset.card ≤ E.edgeFinset.card := by
  let p  := ((¬A.IsIsoSubgraph ·) : SimpleGraph β → Prop)
  have hp : ∃ B, p B := ⟨⊥, not_isIsoSubgraph_bot h⟩
  exact exists_extremal_graph p hp

/-- The extremal graphs on vertex type `β` that do not contain `A` as an
isomorphic subgraph have `extremalNumber β A` number of edges. -/
theorem card_edgeFinset_eq_extremalNumber [Fintype β] {E : SimpleGraph β}
    (h : ¬A.IsIsoSubgraph E)
    (h_extremal : ∀ B : SimpleGraph β,
        ¬A.IsIsoSubgraph B → B.edgeFinset.card ≤ E.edgeFinset.card) :
    E.edgeFinset.card = extremalNumber β A := by
  by_contra! nh
  have h_lt : E.edgeFinset.card < extremalNumber β A := by
    rw [ne_iff_lt_or_gt, or_iff_left] at nh
    exact nh
    push_neg
    apply le_extremalNumber h
  have h_le : extremalNumber β A ≤ E.edgeFinset.card := by
    rw [extremalNumber_le_iff]
    intro B h
    exact h_extremal B h
  absurd lt_of_le_of_lt h_le h_lt
  rw [lt_self_iff_false, not_false_eq_true]
  trivial

end ExtremalNumber
