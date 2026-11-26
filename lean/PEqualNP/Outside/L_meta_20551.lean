import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20551_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [12]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [16, 7]⟩, ⟨.and, [13, 17]⟩], 18⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20551_aux

theorem PEqualNP.Outside.L_meta_20551 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (15767761 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_20551_aux.circuit, PEqualNP.Outside.L_meta_20551_aux.fan, by decide, by decide +kernel⟩
