/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/KostlanEntropyTransfer.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.KostlanGammaLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreEntropy
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Kostlan entropy transfer

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `ginibre_radial_entropy_eq_gamma_product`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The independent Gamma law of the scaled squared individual radii. -/
def kostlanGammaProduct (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i : Fin n => ProbabilityTheory.gammaMeasure ((i.val + 1 : ℕ) : ℝ) 1)

/-- The actual square entropy transfers to the independent Gamma product. -/
theorem ginibre_radial_entropy_eq_gamma_product (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (hc : HasCompactSupport F)
    (hS : IsSymmetricRadiusTest n F) :
    ginibreSquareEntropy n (fun z => F (fun i => kostlanSquaredRadius n (z i))) =
      squareEntropy (kostlanGammaProduct n) F := by
  apply squareEntropy_eq_of_moments
  · have hs : HasCompactSupport (fun r => F r ^ 2) := by
      apply hc.mono
      intro r hr hz
      exact hr (by simp [hz])
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous (hF.pow 2)
    exact ginibre_radial_expectation_eq_gamma_product n hn (fun r => F r ^ 2)
      (hF.pow 2) (by intro σ r; dsimp; rw [hS σ r]) C hC
  · obtain ⟨C, hC⟩ := (compactSupport_square_mul_log hc).exists_bound_of_continuous
      (continuous_square_mul_log hF)
    exact ginibre_radial_expectation_eq_gamma_product n hn
      (fun r => F r ^ 2 * Real.log (F r ^ 2)) (continuous_square_mul_log hF)
      (by intro σ r; dsimp; rw [hS σ r]) C hC

end
end GinibrePoincare
