import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.Basic

open Fintype Function

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

instance {α : Type*} [DecidableEq α] {C : Coloring G α} {c : α} :
    DecidablePred (· ∈ C.colorClass c) :=
  inferInstanceAs <| DecidablePred (· ∈ { v | C v = c })

lemma free_of_colorable {α : Type*} {A : SimpleGraph α}
    (nhc : ¬A.Colorable n) (hc : G.Colorable n) : A.Free G := by
  contrapose! nhc with hc'
  rw [not_not] at hc'
  exact ⟨hc.some.comp hc'.some⟩

lemma Colorable.map {β : Type*} (f : V ↪ β) [NeZero n] (hc : G.Colorable n) :
    (G.map f).Colorable n := by
  letI := Classical.propDecidable
  use fun b ↦ if h : ∃ v, f v = b then hc.some h.choose else default
  intro b₁ b₂ hadj'
  obtain ⟨v₁, v₂, hadj, hv₁, hv₂⟩ := by
    rwa [map_adj] at hadj'
  have hb₁ : ∃ v, f v = b₁ := ⟨v₁, hv₁⟩
  have hb₁_choose : hb₁.choose = v₁ := by
    apply f.injective
    rw [hv₁]
    exact hb₁.choose_spec
  have hb₂ : ∃ v, f v = b₂ := ⟨v₂, hv₂⟩
  have hb₂_choose : hb₂.choose = v₂ := by
    apply f.injective
    rw [hv₂]
    exact hb₂.choose_spec
  have hne := hc.some.valid hadj
  rw [← hb₁_choose, ← hb₂_choose] at hne
  simpa [hb₁, hb₂, hb₁_choose, hb₂_choose] using hc.some.valid hadj

lemma chromaticNumber_eq_iff_colorable_not_colorable :
    G.chromaticNumber = n+1 ↔ G.Colorable (n+1) ∧ ¬G.Colorable n := by
  rw [eq_iff_le_not_lt, not_lt, ENat.add_one_le_iff (ENat.coe_ne_top n), ← not_le,
    chromaticNumber_le_iff_colorable, ← Nat.cast_add_one, chromaticNumber_le_iff_colorable]

end SimpleGraph
