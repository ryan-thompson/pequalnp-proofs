import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20424_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.and, [1, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [0, 9]⟩], 10⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20424_aux

theorem PEqualNP.Outside.L_meta_20424 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (895 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  exact ⟨PEqualNP.Outside.L_meta_20424_aux.circuit, PEqualNP.Outside.L_meta_20424_aux.mono, by decide, by decide +kernel⟩
