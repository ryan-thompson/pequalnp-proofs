import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19730_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [9, 14]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [21, 17]⟩,
    ⟨.and, [0, 22]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [24, 16]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [27, 16]⟩,
    ⟨.and, [2, 28]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.and, [3, 30]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [4, 32]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [34, 17]⟩,
    ⟨.and, [5, 35]⟩,
    ⟨.or, [9, 20]⟩,
    ⟨.and, [6, 37]⟩,
    ⟨.or, [10, 20]⟩,
    ⟨.and, [7, 39]⟩,
    ⟨.or, [23, 26]⟩,
    ⟨.or, [41, 29]⟩,
    ⟨.or, [42, 31]⟩,
    ⟨.or, [43, 33]⟩,
    ⟨.or, [44, 36]⟩,
    ⟨.or, [45, 38]⟩,
    ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19730_aux

theorem PEqualNP.Outside.L_meta_19730 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10778182828540224060 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  exact ⟨PEqualNP.Outside.L_meta_19730_aux.circuit, PEqualNP.Outside.L_meta_19730_aux.mono,
    by decide, by decide +kernel⟩
