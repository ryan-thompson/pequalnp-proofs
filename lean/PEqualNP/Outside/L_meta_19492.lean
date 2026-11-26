import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19492_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [0, 5]⟩, ⟨.not, [15]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19492_aux

theorem PEqualNP.Outside.L_meta_19492 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7571006 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19492_aux.circuit, PEqualNP.Outside.L_meta_19492_aux.fan, by decide, by decide +kernel⟩
