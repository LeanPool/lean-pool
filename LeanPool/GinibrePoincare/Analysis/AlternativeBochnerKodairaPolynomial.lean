/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBochnerKodairaPolynomial.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaIdentity
public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralNumberPolynomial

/-!
# Alternative Bochner Kodaira polynomial

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `bkFinite_integrated_identity`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff ComplexConjugate BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite

theorem bkFinite_conj_coordinate_memLp (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    MemLp (fun z => conj (z j) * finiteHermiteFunction n hn c z) 2 (complexGaussianMeasure n) := by
  apply (memLp_coordinate_mul_finiteHermiteFunction n hn c j).congr_norm
    (((continuous_apply j).star).mul (contDiff_finiteHermiteFunction_smooth n hn
        c).continuous).aestronglyMeasurable
  filter_upwards with z
  simp [Pi.mul_apply]

/-- Equation (6.8) for every actual finite Gaussian Hermite polynomial,
proved by the differential commutator and radial-cutoff integration by parts.
All derivative integrability facts are supplied internally. -/
theorem bkFinite_integrated_identity (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    ‖finiteGaussianNumberL2 n hn c‖ ^ 2 =
      (∑ j : Fin n, ∑ k : Fin n,
        ‖finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c j) k)‖ ^ 2) +
      (n : ℝ) * ∑ j : Fin n, ‖finiteDbarComponentL2 n hn c j‖ ^ 2 := by
  let D := fun j => finiteDbarComponentL2 n hn c j
  let N := fun j => finiteHermiteCombination n hn
    (spectralRaisingCoefficients n j (loweredCoefficients n c j))
  let Q := fun j k => finiteHermiteCombination n hn
    (loweredCoefficients n (loweredCoefficients n c j) k)
  let R := fun j k => finiteHermiteCombination n hn
    (spectralRaisingCoefficients n k (loweredCoefficients n (loweredCoefficients n c j) k))
  have hD (j : Fin n) : (D j : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      dbarComponent (finiteHermiteFunction n hn c) j := finiteDbarComponentL2_coeFn n hn c j
  have hN (j : Fin n) : (N j : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      gaussianDbarAdjointTest j (dbarComponent (finiteHermiteFunction n hn c) j) := by
    rw [show dbarComponent (finiteHermiteFunction n hn c) j =
      finiteHermiteFunction n hn (loweredCoefficients n c j) by
        funext z; exact dbarComponent_finiteHermiteFunction n hn c j z]
    exact spectralAdjoint_finiteHermiteCombination_ae n hn (loweredCoefficients n c j) j
  have hQ (j k : Fin n) : (Q j k : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      dbarComponent (dbarComponent (finiteHermiteFunction n hn c) j) k := by
    filter_upwards [finiteHermiteCombination_coeFn n hn
      (loweredCoefficients n (loweredCoefficients n c j) k)] with z hz
    rw [hz, ← dbarComponent_finiteHermiteFunction]
    rw [show finiteHermiteFunction n hn (loweredCoefficients n c j) =
      dbarComponent (finiteHermiteFunction n hn c) j by
        funext z; exact (dbarComponent_finiteHermiteFunction n hn c j z).symm]
  have he (j k : Fin n) : dbarComponent (dbarComponent (finiteHermiteFunction n hn c) j) k =
      finiteHermiteFunction n hn (loweredCoefficients n (loweredCoefficients n c j) k) := by
    rw [show dbarComponent (finiteHermiteFunction n hn c) j =
      finiteHermiteFunction n hn (loweredCoefficients n c j) by
        funext z; exact dbarComponent_finiteHermiteFunction n hn c j z]
    funext z
    exact dbarComponent_finiteHermiteFunction n hn (loweredCoefficients n c j) k z
  have hR (j k : Fin n) : (R j k : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      gaussianDbarAdjointTest k (dbarComponent (dbarComponent (finiteHermiteFunction n hn c) j) k)
          := by
    rw [he]
    exact spectralAdjoint_finiteHermiteCombination_ae n hn
      (loweredCoefficients n (loweredCoefficients n c j) k) k
  have hZ (j : Fin n) : MemLp (fun z => conj (z j) *
      dbarComponent (finiteHermiteFunction n hn c) j z) 2 (complexGaussianMeasure n) := by
    convert bkFinite_conj_coordinate_memLp n hn (loweredCoefficients n c j) j using 1
    funext z
    rw [dbarComponent_finiteHermiteFunction]
  have hZZ (j k : Fin n) : MemLp (fun z => conj (z k) *
      dbarComponent (dbarComponent (finiteHermiteFunction n hn c) j) k z) 2 (complexGaussianMeasure
          n) := by
    rw [he]
    exact bkFinite_conj_coordinate_memLp n hn (loweredCoefficients n (loweredCoefficients n c j) k)
        k
  have hnumber : (∑ j : Fin n, N j) = finiteGaussianNumberL2 n hn c := by
    unfold finiteGaussianNumberL2
    rw [spectralNumberCoefficients_eq_sum]
    dsimp only [N]
    unfold finiteHermiteCombination
    exact (map_sum _ _ _).symm
  simpa only [hnumber] using bkGaussian_integrated_identity hn (finiteHermiteFunction n hn c)
    (contDiff_finiteHermiteFunction_smooth n hn c) D N Q R hD hN hQ hR hZ hZZ

end
end GinibrePoincare

