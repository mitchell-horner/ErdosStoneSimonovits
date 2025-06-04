import Mathlib

open Function OrderDual

section Preorder

variable {α : Type*} [Preorder α]

theorem monotone_add_nat_of_le_succ {f : ℕ → α} {k : ℕ} (hf : ∀ n ≥ k, f n ≤ f (n + 1)) :
    Monotone (fun n ↦ f (n + k)) :=
  fun _ _ hle ↦ Nat.rel_of_forall_rel_succ_of_le_of_le (· ≤ ·) hf
    (Nat.le_add_left k _) (Nat.add_le_add_iff_right.mpr hle)

theorem monotoneOn_nat_Ici_of_le_succ {f : ℕ → α} {k : ℕ} (hf : ∀ n ≥ k, f n ≤ f (n + 1)) :
    MonotoneOn f (Set.Ici k) :=
  fun _ hab _ _ hle ↦ Nat.rel_of_forall_rel_succ_of_le_of_le (· ≤ ·) hf hab hle

theorem monotone_add_nat_iff_monotoneOn_nat_Ici {f : ℕ → α} {k : ℕ} :
    Monotone (fun n ↦ f (n + k)) ↔ MonotoneOn f (Set.Ici k) := by
  refine ⟨fun h x hx y hy hle ↦ ?_, fun h x y hle ↦ ?_⟩
  · rw [← Nat.sub_add_cancel hx, ← Nat.sub_add_cancel hy]
    rw [← Nat.sub_le_sub_iff_right hy] at hle
    exact h hle
  · rw [← Nat.add_le_add_iff_right] at hle
    exact h (Nat.le_add_left k x) (Nat.le_add_left k y) hle

theorem antitone_add_nat_of_succ_le {f : ℕ → α} {k : ℕ} (hf : ∀ n ≥ k, f (n + 1) ≤ f n) :
    Antitone (fun n ↦ f (n + k)) :=
  @monotone_add_nat_of_le_succ αᵒᵈ _ f k hf

theorem antitoneOn_nat_Ici_of_succ_le {f : ℕ → α} {k : ℕ} (hf : ∀ n ≥ k, f (n + 1) ≤ f n) :
    AntitoneOn f (Set.Ici k) :=
  @monotoneOn_nat_Ici_of_le_succ αᵒᵈ _ f k hf

theorem antitone_add_nat_iff_antitoneOn_nat_Ici {f : ℕ → α} {k : ℕ} :
    Antitone (fun n ↦ f (n + k)) ↔ AntitoneOn f (Set.Ici k) :=
  @monotone_add_nat_iff_monotoneOn_nat_Ici αᵒᵈ _ f k

end Preorder
