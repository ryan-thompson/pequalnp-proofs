import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19486_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.not, [0]⟩, ⟨.and, [10, 9]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [14, 1]⟩, ⟨.not, [15]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [16, 17]⟩], 18⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19486_aux

theorem PEqualNP.Outside.L_meta_19486 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3382551 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19486_aux.circuit, PEqualNP.Outside.L_meta_19486_aux.fan, by decide, by decide +kernel⟩
