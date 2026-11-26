import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19735_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [0, 20]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [22, 18]⟩,
    ⟨.and, [1, 23]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.and, [2, 25]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [27, 16]⟩,
    ⟨.and, [3, 28]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [30, 16]⟩,
    ⟨.and, [4, 31]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.and, [5, 33]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [35, 13]⟩,
    ⟨.or, [36, 14]⟩,
    ⟨.and, [6, 37]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.and, [7, 39]⟩,
    ⟨.or, [21, 24]⟩,
    ⟨.or, [41, 26]⟩,
    ⟨.or, [42, 29]⟩,
    ⟨.or, [43, 32]⟩,
    ⟨.or, [44, 34]⟩,
    ⟨.or, [45, 38]⟩,
    ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19735_aux

theorem PEqualNP.Outside.L_meta_19735 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1110766810026783180 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  exact ⟨PEqualNP.Outside.L_meta_19735_aux.circuit, PEqualNP.Outside.L_meta_19735_aux.mono,
    by decide, by decide +kernel⟩
