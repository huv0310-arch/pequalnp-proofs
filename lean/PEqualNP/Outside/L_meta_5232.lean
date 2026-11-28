import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5232

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Upper-bound certificate for the gap `L-meta-5232`: the 8-variable edge-detection function of
the 19-edge graph with edges 0-3, 1-3, 0-4, 2-4, 0-5, 1-5, 3-5, 1-6, 2-6, 3-6, 4-6, 5-6, 0-7, 1-7,
2-7, 3-7, 4-7, 5-7, 6-7 has a monotone 19-gate fan-in-two circuit. The witness reuses shared
subterms: the pair `(x0 || x5)` is computed once and feeds three product terms, and two intermediate
nodes each cover four minimal true points, so the plain DNF's 37 gates drop to 19. -/
def C0 : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.and, [9, 15]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [18, 19]⟩, ⟨GateOp.or, [21, 22]⟩, ⟨GateOp.or, [23, 20]⟩, ⟨GateOp.or, [24, 25]⟩], 26⟩

theorem ok0 : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem ev0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    C0.eval [b0, b1, b2, b3, b4, b5, b6, b7] = ((b0 && b3) || (b0 && b4) || (b0 && b5) || (b0 && b7) || (b1 && b3) || (b1 && b5) || (b1 && b6) || (b1 && b7) || (b2 && b4) || (b2 && b6) || (b2 && b7) || (b3 && b5) || (b3 && b6) || (b3 && b7) || (b4 && b6) || (b4 && b7) || (b5 && b6) || (b5 && b7) || (b6 && b7)) := by
  decide +kernel

theorem ofFn8 (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_5232

theorem PEqualNP.Outside.L_meta_5232 :
    PEqualNP.MetaComplexity.HasCircuitSize 8
      (fun x : Fin 8 → Bool => (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 7) || (x 1 && x 3) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 4) || (x 2 && x 6) || (x 2 && x 7) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)) 19 :=
  ⟨PEqualNP.Outside.L_meta_5232.C0, PEqualNP.Outside.L_meta_5232.ok0, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_5232.ofFn8]
      exact PEqualNP.Outside.L_meta_5232.ev0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
