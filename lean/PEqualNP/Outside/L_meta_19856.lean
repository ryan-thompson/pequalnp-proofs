import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19856_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 15]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.or, [10, 17]⟩,
    ⟨.or, [11, 18]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [22, 15]⟩,
    ⟨.or, [23, 17]⟩,
    ⟨.and, [0, 24]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [26, 20]⟩,
    ⟨.and, [1, 27]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [2, 29]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [31, 21]⟩,
    ⟨.and, [3, 32]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.and, [4, 34]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.and, [5, 36]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [38, 19]⟩,
    ⟨.and, [6, 39]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.and, [7, 41]⟩,
    ⟨.or, [25, 28]⟩,
    ⟨.or, [43, 30]⟩,
    ⟨.or, [44, 33]⟩,
    ⟨.or, [45, 35]⟩,
    ⟨.or, [46, 37]⟩,
    ⟨.or, [47, 40]⟩,
    ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19856_aux

theorem PEqualNP.Outside.L_meta_19856 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8547244839380926170 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  exact ⟨PEqualNP.Outside.L_meta_19856_aux.circuit, PEqualNP.Outside.L_meta_19856_aux.mono,
    by decide, by decide +kernel⟩
