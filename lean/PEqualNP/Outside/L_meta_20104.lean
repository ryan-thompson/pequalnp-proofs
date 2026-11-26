import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20104

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Gate list obtained by factoring a cover of the matrix by rectangles.
def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 3, 6), (true, 5, 7), (true, 1, 2), (true, 0, 16), (true, 4, 17), (true, 0, 18), (true, 4, 19), (true, 5, 22), (true, 17, 19), (true, 17, 21), (true, 7, 16), (true, 26, 18), (true, 18, 20), (true, 21, 3), (true, 29, 4), (true, 1, 22), (true, 20, 6), (true, 32, 2), (false, 23, 8), (false, 24, 9), (false, 25, 10), (false, 27, 11), (false, 28, 12), (false, 30, 13), (false, 31, 14), (false, 33, 15), (true, 34, 35), (true, 42, 36), (true, 43, 37), (true, 44, 38), (true, 45, 39), (true, 46, 40), (true, 47, 41)]
def circuit : Circuit := ⟨codes.map asGate, 48⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_20104

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_20104 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11442406341415304295 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_20104.circuit, PEqualNP.Outside.L_meta_20104.mono, by decide, by decide +kernel⟩
