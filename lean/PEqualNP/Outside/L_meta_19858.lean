import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19858_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 15]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.and, [0, 18]⟩,
    ⟨.or, [12, 17]⟩,
    ⟨.and, [1, 20]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.and, [2, 22]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [24, 14]⟩,
    ⟨.and, [3, 25]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [27, 12]⟩,
    ⟨.and, [4, 28]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [30, 14]⟩,
    ⟨.and, [5, 31]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [33, 15]⟩,
    ⟨.and, [6, 34]⟩,
    ⟨.or, [11, 16]⟩,
    ⟨.and, [7, 36]⟩,
    ⟨.or, [19, 21]⟩,
    ⟨.or, [38, 23]⟩,
    ⟨.or, [39, 26]⟩,
    ⟨.or, [40, 29]⟩,
    ⟨.or, [41, 32]⟩,
    ⟨.or, [42, 35]⟩,
    ⟨.or, [43, 37]⟩], 44⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19858_aux

theorem PEqualNP.Outside.L_meta_19858 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9917578511873611425 : ℕ).testBit (8 * u.val + v.val)) 29 := by
  exact ⟨PEqualNP.Outside.L_meta_19858_aux.circuit, PEqualNP.Outside.L_meta_19858_aux.mono,
    by decide, by decide +kernel⟩
