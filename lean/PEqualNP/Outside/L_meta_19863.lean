import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19863_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 13]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [0, 18]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [20, 14]⟩,
    ⟨.and, [1, 21]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [23, 13]⟩,
    ⟨.and, [2, 24]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [26, 15]⟩,
    ⟨.and, [3, 27]⟩,
    ⟨.or, [9, 17]⟩,
    ⟨.and, [4, 29]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [31, 15]⟩,
    ⟨.and, [5, 32]⟩,
    ⟨.or, [12, 17]⟩,
    ⟨.and, [6, 34]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.and, [7, 36]⟩,
    ⟨.or, [19, 22]⟩,
    ⟨.or, [38, 25]⟩,
    ⟨.or, [39, 28]⟩,
    ⟨.or, [40, 30]⟩,
    ⟨.or, [41, 33]⟩,
    ⟨.or, [42, 35]⟩,
    ⟨.or, [43, 37]⟩], 44⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19863_aux

theorem PEqualNP.Outside.L_meta_19863 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2691051730525901985 : ℕ).testBit (8 * u.val + v.val)) 29 := by
  exact ⟨PEqualNP.Outside.L_meta_19863_aux.circuit, PEqualNP.Outside.L_meta_19863_aux.mono,
    by decide, by decide +kernel⟩
