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

section IsIsoSubgraph

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
theorem bot_isIsoSubgraph_iff (B : SimpleGraph β) :
    (⊥ : SimpleGraph α).IsIsoSubgraph B ↔ Nonempty (α ↪ β) :=
  ⟨fun ⟨f⟩ ↦ ⟨f.asEmbedding⟩, fun ⟨f⟩ ↦ ⟨⟨f, by simp⟩, f.injective⟩⟩

/-- If `A ≃g B`, then `A` is an isomorphic subgraph of `C` if and only if `B`
is an isomorphic subgraph of `C`. -/
lemma isIsoSubgraph_iff_of_iso (f : A ≃g B) :
    A.IsIsoSubgraph C ↔ B.IsIsoSubgraph C :=
  ⟨IsIsoSubgraph.trans ⟨f.symm.toSubgraphIso⟩,
    IsIsoSubgraph.trans ⟨f.toSubgraphIso⟩⟩

end IsIsoSubgraph

section Free

/-- The relation that a `SimpleGraph` does not contain a copy of another
`SimpleGraph`. -/
abbrev Free (A : SimpleGraph α) (B : SimpleGraph β) := ¬A.IsIsoSubgraph B

/-- If `A ≃g B`, then `C` is `A`-free if `C` is `B`-free. -/
lemma free_iff_of_iso (f : A ≃g B) :
    A.Free C ↔ B.Free C := by
  rw [not_iff_not]
  exact isIsoSubgraph_iff_of_iso f

end Free

section ExtremalNumber

open Classical in
/-- The extremal number of a finite type `β` and a simple graph `A` is the
maximal number of edges in a `A`-free simple graph on the vertex type `β`.

Note that if `A` is an isomorphic subgraph of any simple graph on the vertex
type `β` then this is `0`. -/
noncomputable def extremalNumber
    (β : Type*) [Fintype β] (A : SimpleGraph α) : ℕ :=
  Finset.sup (Finset.univ.filter A.Free : Finset (SimpleGraph β))
    (·.edgeFinset.card : SimpleGraph β → ℕ)

theorem le_extremalNumber [Fintype β] [DecidableRel B.Adj]
    (h : A.Free B) :
    B.edgeFinset.card ≤ extremalNumber β A := by
  classical
  let s := (Finset.univ.filter A.Free : Finset (SimpleGraph β))
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
      A.Free B → B.edgeFinset.card ≤ x := by
  simp_rw [extremalNumber, Finset.sup_le_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨fun h B _ hB ↦ by convert h B hB, fun h B hB ↦ by convert h B hB⟩

theorem lt_extremalNumber_iff
    (β : Type*) [Fintype β] (A : SimpleGraph α) (x : ℕ) :
    x < extremalNumber β A ↔ ∃ B : SimpleGraph β, ∃ _ : DecidableRel B.Adj,
      A.Free B ∧ x < B.edgeFinset.card := by
  simp_rw [extremalNumber, Finset.lt_sup_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨fun ⟨B, h₁, h₂⟩ ↦ ⟨B, _, h₁, h₂⟩,
    fun ⟨B, _, h₁, h₂⟩ ↦ ⟨B, h₁, by convert h₂⟩⟩

variable {R : Type*} [LinearOrderedSemiring R] [FloorSemiring R] {x : R}

theorem extremalNumber_le_iff_of_nonneg
    (β : Type*) [Fintype β] (A : SimpleGraph α) (hx_nonneg : 0 ≤ x) :
    ↑(extremalNumber β A) ≤ x ↔ ∀ (B : SimpleGraph β) [DecidableRel B.Adj],
      A.Free B → ↑B.edgeFinset.card ≤ x := by
  simp_rw [←Nat.le_floor_iff hx_nonneg]
  exact extremalNumber_le_iff β A ⌊x⌋₊

theorem lt_extremalNumber_iff_of_nonneg
    (β : Type*) [Fintype β] (A : SimpleGraph α) (hx_nonneg : 0 ≤ x) :
    x < ↑(extremalNumber β A) ↔ ∃ B : SimpleGraph β, ∃ _ : DecidableRel B.Adj,
      A.Free B ∧ x < ↑B.edgeFinset.card := by
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
simple graph that contains `A`. -/
theorem extremalNumber_le_extremalNumber_of_isIsoSubgraph [Fintype β]
    (h : A.IsIsoSubgraph C) :
    extremalNumber β A ≤ extremalNumber β C := by
  rw [extremalNumber_le_iff]
  intro B
  contrapose
  push_neg
  intro h_lt
  rw [not_not]
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
    rw [not_not] at h ⊢
    apply IsIsoSubgraph.trans ⟨G⟩
    exact h.trans ⟨F.symm.toSubgraphIso⟩

/-- The extremal numbers of `⊥` equal zero. -/
theorem extremalNumber_bot [DecidableEq β] [Fintype β] (h : Nonempty (V ↪ β)) :
    extremalNumber β (⊥ : SimpleGraph V) = 0 := by
  rw [←Nat.le_zero, extremalNumber_le_iff]
  intro B _ hB
  absurd hB
  rwa [←bot_isIsoSubgraph_iff B] at h

/-- The extremal numbers of `Fintype.card β ≤ 1` equal zero. -/
theorem extremalNumber_of_card_le_one
    [DecidableEq β] [Fintype β] (h : Fintype.card β ≤ 1) :
    extremalNumber β A = 0 := by
  haveI : Subsingleton β := by
    rwa [Fintype.card_le_one_iff_subsingleton] at h
  simp_rw [extremalNumber, Finset.univ_unique,
    Finset.filter_singleton, instInhabited_default]
  by_cases h : A.Free (⊥ : SimpleGraph β)
  all_goals simp [h, -not_nonempty_iff, -nonempty_subtype, -Set.toFinset_card]

end ExtremalNumber

section IsExtremal

/-- A simple graph `G` is an extremal graph satisfying the predicate `p` if
`G` has the maximum number of edges of any simple graph satisfying `p`. -/
abbrev IsExtremal {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : SimpleGraph V → Prop) :=
  p G ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    p H → H.edgeFinset.card ≤ G.edgeFinset.card

/-- There exist extremal graphs satisfying the predicate `p` provided that at
least one simple graph satisfies the predicate `p`. -/
theorem exists_extremal_graph [Fintype V] [DecidableEq V]
    (p : SimpleGraph V → Prop) [DecidablePred p] (h : ∃ G, p G) :
    ∃ E : SimpleGraph V, ∃ _ : DecidableRel E.Adj, E.IsExtremal p := by
  classical
  let s := (Finset.univ.filter (p ·) : Finset (SimpleGraph V))
  have hs : s.Nonempty := by
    use Exists.choose h
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Exists.choose_spec h⟩
  obtain ⟨E, hp, h_extremal⟩ :=
    Finset.exists_max_image s (·.edgeFinset.card) hs
  use E, by infer_instance
  rw [Finset.mem_filter] at hp
  conv at h_extremal =>
    intro G; rw [Finset.mem_filter]
  refine ⟨hp.2, ?_⟩
  intro G _ hp'
  convert h_extremal G ⟨Finset.mem_univ G, hp'⟩

lemma free_bot (h : G.edgeSet.Nonempty) :
    G.Free (⊥ : SimpleGraph β) := by
  intro ⟨f, _⟩
  rw [←ne_self_iff_false, ←edgeSet_nonempty]
  let ⟨e, he⟩ := h
  exact ⟨e.map f, Hom.map_mem_edgeSet f he⟩

/-- There exist extremal graphs on vertex type `β` that are `A`-free if `A` has
at least one edge. -/
theorem exists_extremal_graph_of_free [Fintype α] [DecidableEq α]
    (h : A.edgeSet.Nonempty) [Fintype β] [DecidableEq β] :
    ∃ E : SimpleGraph β, ∃ _ : DecidableRel E.Adj, E.IsExtremal A.Free := by
  haveI : DecidablePred (A.Free : SimpleGraph β → Prop) := by
    intro B; unfold Free IsIsoSubgraph SubgraphIso
    rw [not_nonempty_iff, isEmpty_subtype]
    haveI : Fintype (A →g B) := Fintype.ofFinite _
    infer_instance
  let p  := (A.Free : SimpleGraph β → Prop)
  have hp : ∃ B, p B := ⟨⊥, free_bot h⟩
  exact exists_extremal_graph p hp

/-- The extremal graphs on vertex type `β` that are `A`-free have
`extremalNumber β A` number of edges. -/
theorem card_edgeFinset_eq_extremalNumber_iff
    [Fintype β] {E : SimpleGraph β} [DecidableRel E.Adj] :
    (A.Free E) ∧ E.edgeFinset.card = extremalNumber β A
      ↔ E.IsExtremal A.Free := by
  rw [IsExtremal, and_congr_right_iff]
  intro h_free
  constructor
  . intro h_eq
    rw [h_eq]
    intro _ _ h_free'
    exact le_extremalNumber h_free'
  . intro h_extremal
    apply eq_of_le_of_le (le_extremalNumber h_free)
    rwa [←extremalNumber_le_iff] at h_extremal

end IsExtremal
