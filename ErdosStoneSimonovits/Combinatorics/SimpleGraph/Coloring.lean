import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.Basic

open Fintype Function

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

instance {α : Type*} [DecidableEq α] {C : Coloring G α} {c : α} :
    DecidablePred (· ∈ C.colorClass c) :=
  inferInstanceAs <| DecidablePred (· ∈ { v | C v = c })

/-- If `H` is not `n`-colorable and `G` is `n`-colorable, then `G` is `H.Free`. -/
theorem free_of_colorable {α : Type*} {A : SimpleGraph α}
    (nhc : ¬A.Colorable n) (hc : G.Colorable n) : A.Free G := by
  contrapose! nhc with hc'
  rw [not_not] at hc'
  exact ⟨hc.some.comp hc'.some⟩

/-- If `G` is `n`-colorable, then mapping the vertices of `G` produces an  `n`-colorable simple
graph. -/
theorem Colorable.map {β : Type*} (f : V ↪ β) [NeZero n] (hc : G.Colorable n) :
    (G.map f).Colorable n := by
  obtain ⟨C⟩ := hc
  use extend f C (const β default)
  intro a b ⟨_, _, hadj, ha, hb⟩
  rw [← ha, Injective.extend_apply f.injective, ← hb, Injective.extend_apply f.injective]
  exact C.valid hadj

/-- If the chromatic number of `G` is `n + 1`, then `G` is colorable in no fewer than `n + 1`
colors. -/
theorem chromaticNumber_eq_iff_colorable_not_colorable :
    G.chromaticNumber = n + 1 ↔ G.Colorable (n + 1) ∧ ¬G.Colorable n := by
  rw [eq_iff_le_not_lt, not_lt, ENat.add_one_le_iff (ENat.coe_ne_top n), ← not_le,
    chromaticNumber_le_iff_colorable, ← Nat.cast_add_one, chromaticNumber_le_iff_colorable]

end SimpleGraph
