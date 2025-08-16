import Mathlib

namespace Finset

variable {α β : Type*}

section DisjiUnion

variable {s : Finset α} {t : Finset β} {f : α → β}

lemma pairwiseDisjoint_filter {f : α → Finset β} (h : Set.PairwiseDisjoint ↑s f)
    (p : β → Prop) [DecidablePred p] : Set.PairwiseDisjoint ↑s fun a ↦ (f a).filter p :=
  fun _ h₁ _ h₂ hne ↦ Finset.disjoint_filter_filter (h h₁ h₂ hne)

theorem filter_disjiUnion (s : Finset α) (f : α → Finset β) (h) (p : β → Prop) [DecidablePred p] :
    (s.disjiUnion f h).filter p
      = s.disjiUnion (fun a ↦ (f a).filter p) (pairwiseDisjoint_filter h p) := by
  ext; simp [← exists_and_right, and_assoc]

end DisjiUnion

end Finset
