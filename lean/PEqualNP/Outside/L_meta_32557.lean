import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.EdgeUpper

namespace PEqualNP.Outside.L_meta_32557_aux
open PEqualNP PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds

def ad (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0, 3),(0, 5),(0, 6),(0, 7),(1, 4),(1, 5),(1, 6),(1, 7),(2, 4),(2, 7),(3, 5),(3, 6),(3, 7),(4, 7),(5, 6),(5, 7),(3, 0),(5, 0),(6, 0),(7, 0),(4, 1),(5, 1),(6, 1),(7, 1),(4, 2),(7, 2),(5, 3),(6, 3),(7, 3),(7, 4),(6, 5),(7, 5)])

def G : SimpleGraph (Fin 8) where
  Adj i j := ad i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance instDec : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (ad i j = true))

theorem hfun : (fun x : Fin 8 → Bool => (x 0 && x 3) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 4) || (x 2 && x 7) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)) =
    (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && d) || (a && f) || (a && g) || (a && h) || (b && e) || (b && f) || (b && g) || (b && h) || (c && e) || (c && h) || (d && f) || (d && g) || (d && h) || (e && h) || (f && g) || (f && h)) =
      decide (∃ i j : Fin 8, G.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧
        (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard : G.edgeFinset.card = 16 := by
  decide +kernel

theorem hcov : ∀ i j : Fin 8, G.Adj i j → i ∈ ({0, 4, 5, 6, 7} : Finset (Fin 8)) ∨ j ∈ ({0, 4, 5, 6, 7} : Finset (Fin 8)) := by
  decide

theorem main : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 3) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 4) || (x 2 && x 7) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)) 20 := by
  rw [hfun]
  have h := @PEqualNP.MetaComplexity.Helpers.EdgeUpper.edge_upper 8 G instDec {0, 4, 5, 6, 7} ⟨0, 3, by decide⟩ hcov
  rw [hcard] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 4, 5, 6, 7} : Finset (Fin 8)).card = 5 := by decide
  rw [this] at h2
  omega

end PEqualNP.Outside.L_meta_32557_aux

open PEqualNP.Outside.L_meta_32557_aux in
theorem PEqualNP.Outside.L_meta_32557 : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 3) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 4) || (x 2 && x 7) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)) 20 :=
  main
