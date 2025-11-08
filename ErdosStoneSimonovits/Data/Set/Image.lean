import Mathlib

open Function Set

namespace Set

section Range

theorem range_add_nat_eq_image_nat_Ici {α : Type*} {f : ℕ → α} {k : ℕ} :
    range (fun x ↦ f (x + k)) = f '' Ici k := by
  refine Set.ext fun x ↦ ⟨fun ⟨y, hfy⟩ ↦ ⟨y + k, Nat.le_add_left k y, hfy⟩,
    fun ⟨y, hy, hfy⟩ ↦ ⟨y - k, ?_⟩⟩
  rwa [← Nat.sub_add_cancel hy] at hfy

end Range

end Set
