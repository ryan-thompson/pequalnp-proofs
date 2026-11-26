import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19724_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 12]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.and, [0, 21]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [23, 16]⟩,
    ⟨.and, [1, 24]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [26, 13]⟩,
    ⟨.or, [27, 15]⟩,
    ⟨.and, [2, 28]⟩,
    ⟨.or, [9, 20]⟩,
    ⟨.and, [3, 30]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [32, 17]⟩,
    ⟨.and, [4, 33]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [5, 35]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.and, [6, 37]⟩,
    ⟨.or, [10, 20]⟩,
    ⟨.and, [7, 39]⟩,
    ⟨.or, [22, 25]⟩,
    ⟨.or, [41, 29]⟩,
    ⟨.or, [42, 31]⟩,
    ⟨.or, [43, 34]⟩,
    ⟨.or, [44, 36]⟩,
    ⟨.or, [45, 38]⟩,
    ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19724_aux

theorem PEqualNP.Outside.L_meta_19724 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7837978282315423185 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  exact ⟨PEqualNP.Outside.L_meta_19724_aux.circuit, PEqualNP.Outside.L_meta_19724_aux.mono,
    by decide, by decide +kernel⟩
