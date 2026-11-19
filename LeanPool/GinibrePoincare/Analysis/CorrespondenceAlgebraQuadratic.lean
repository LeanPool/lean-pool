/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAlgebraQuadratic.lean.
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
public import LeanPool.GinibrePoincare.Analysis.PolynomialSectorIncompleteness
/-!
# Correspondence algebra quadratic

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `correspondenceQuadratic_arbitrary_phase`,
`correspondenceQuadratic_sum_decomposition`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The configuration with the same barycenter as `z` whose recentered part is multiplied by
`ζ`: `j ↦ coordinateSum z / n + ζ * recenteredConfiguration n z j`. -/
def correspondenceRelativePhase (n : ℕ) (ζ : ℂ) (z : Configuration n) : Configuration n :=
  fun j => coordinateSum z/(n : ℂ)+ζ*recenteredConfiguration n z j

theorem correspondenceRelativePhase_sum {n : ℕ} (hn : 0 < n) (ζ : ℂ) (z : Configuration n) :
    coordinateSum (correspondenceRelativePhase n ζ z) = coordinateSum z := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [correspondenceRelativePhase, coordinateSum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,← Finset.mul_sum]
  change (n : ℂ)*(coordinateSum z/(n : ℂ))+ζ*coordinateSum (recenteredConfiguration n z) =
      coordinateSum z
  rw [coordinateSum_recentered, mul_zero, add_zero]
  exact mul_div_cancel₀ _ hnC

theorem correspondenceRelativePhase_recenter {n : ℕ} (hn : 0 < n) (ζ : ℂ) (z : Configuration n) :
    recenteredConfiguration n (correspondenceRelativePhase n ζ z) =
      fun j => ζ*recenteredConfiguration n z j := by
  ext j
  simp only [recenteredConfiguration, projectToOrthogonal]
  rw [correspondenceRelativePhase_sum hn]
  simp only [correspondenceRelativePhase, recenteredConfiguration, projectToOrthogonal]
  ring

/-- Remark 1.6 covariance holds for every complex phase, hence every angle. -/
theorem correspondenceQuadratic_arbitrary_phase {n : ℕ} (hn : 0 < n) (ζ : ℂ) (z : Configuration n) :
    ginibreCenteredQuadratic n (correspondenceRelativePhase n ζ z) = ζ^2*ginibreCenteredQuadratic n
        z := by
  unfold ginibreCenteredQuadratic
  rw [correspondenceRelativePhase_recenter hn]
  simp only [mul_pow,← Finset.mul_sum]

/-- Literal center/relative quadratic decomposition in Remark 1.6. -/
theorem correspondenceQuadratic_sum_decomposition {n : ℕ} (hn : 0 < n) (z : Configuration n) :
    (∑ j, z j^2) = (coordinateSum z)^2/(n : ℂ)+ginibreCenteredQuadratic n z := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : ginibreCenteredQuadratic n z =
      (∑ j, z j^2)-2*(coordinateSum z/(n : ℂ))*coordinateSum z+
        (n : ℂ)*(coordinateSum z/(n : ℂ))^2 := by
    unfold ginibreCenteredQuadratic recenteredConfiguration projectToOrthogonal
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_mul]
    simp only [coordinateSum,← Finset.mul_sum]
    ring
  rw [hp]
  field_simp
  ring

end
end GinibrePoincare
