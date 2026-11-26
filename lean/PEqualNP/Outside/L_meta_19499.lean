import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19499_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [2, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.not, [16]⟩, ⟨.and, [13, 17]⟩], 18⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19499_aux

theorem PEqualNP.Outside.L_meta_19499 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7586366 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19499_aux.circuit, PEqualNP.Outside.L_meta_19499_aux.fan, by decide, by decide +kernel⟩
