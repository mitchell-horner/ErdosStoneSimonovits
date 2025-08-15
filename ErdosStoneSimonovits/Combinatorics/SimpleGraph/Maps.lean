import Mathlib

open Function

namespace SimpleGraph

variable {V W : Type*} (G : SimpleGraph V)

theorem edgeSet_map_eq_image (f : V ↪ W) (G : SimpleGraph V) :
    (G.map f).edgeSet = f.sym2Map '' G.edgeSet := by
  ext v
  induction v
  rw [mem_edgeSet, map_adj, Set.mem_image]
  constructor
  · intro ⟨a, b, hadj, ha, hb⟩
    use s(a, b), hadj
    rw [Embedding.sym2Map_apply, Sym2.map_pair_eq, ha, hb]
  · intro ⟨e, hadj, he⟩
    induction e
    rw [Embedding.sym2Map_apply, Sym2.map_pair_eq, Sym2.eq_iff] at he
    exact he.elim (fun ⟨h, h'⟩ ↦ ⟨_, _, hadj, h, h'⟩) (fun ⟨h', h⟩ ↦ ⟨_, _, hadj.symm, h, h'⟩)

theorem support_map_eq_image (f : V ↪ W) : (G.map f).support = f '' G.support := by
  ext; simp [mem_support]; tauto

end SimpleGraph
