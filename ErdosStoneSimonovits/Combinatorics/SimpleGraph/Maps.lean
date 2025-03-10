import Mathlib

open Function

namespace SimpleGraph

variable {V W : Type*} (G : SimpleGraph V)

theorem support_map_eq_image (f : V ↪ W): (G.map f).support = f '' G.support := by
  ext; simp [mem_support]; tauto

end SimpleGraph
