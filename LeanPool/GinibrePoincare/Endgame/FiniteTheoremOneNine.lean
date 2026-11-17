/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Endgame/FiniteTheoremOneNine.lean.
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

public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.GroundStateDbar
public import LeanPool.GinibrePoincare.Analysis.HermiteEnergy

/-! # Realizing finite Hermite expansions in the Ginibre ground-state transform -/


@[expose] public section


open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GinibrePoincare
namespace ComplexHermite

noncomputable section

theorem transformedCenteredObservableL2_coeFn {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    transformedCenteredObservableL2 hn f hf =ᵐ[complexGaussianMeasure n]
      normalizedVandermondeTransform n
        (fun z => (centeredObservable n f z : ℂ)) := by
  let u := centeredObservableL2 hn f hf
  have hmul : normalizedVandermondeL2 n hn u =ᵐ[complexGaussianMeasure n]
      fun z => normalizedVandermondeMultiplier n z * u z := by
    exact normalizedVandermondeL2_coeFn_public n hn u
  have hu := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq (centeredObservableL2_coeFn hn f hf)
  filter_upwards [hmul, hu] with z hz hzu
  rw [transformedCenteredObservableL2, hz, hzu]
  unfold normalizedVandermondeMultiplier
  exact (normalizedVandermondeTransform_apply n
    (fun z => (centeredObservable n f z : ℂ)) z).symm

private theorem continuous_finiteHermiteFunction (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    Continuous (finiteHermiteFunction n hn c) := by
  classical
  rw [show finiteHermiteFunction n hn c = fun z =>
      ∑ pq ∈ c.support, c pq * multivariateNormalized n hn pq.1 pq.2 z by
    funext z
    simp [finiteHermiteFunction, Finsupp.linearCombination_apply,
      Finsupp.sum, smul_eq_mul]]
  apply continuous_finsetSum
  intro pq hpq
  exact continuous_const.mul (continuous_multivariateNormalized n hn pq.1 pq.2)

/-- An equality of the Gaussian `L²` classes upgrades to literal equality of
the smooth ground-state representative and its finite Hermite polynomial. -/
theorem transformedCentered_eq_finiteHermiteFunction {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f)
    (c : HermiteMultiIndex n →₀ ℂ)
    (hL2 : transformedCenteredObservableL2 hn f hf =
      finiteHermiteCombination n hn c) :
    normalizedVandermondeTransform n
        (fun z => (centeredObservable n f z : ℂ)) =
      finiteHermiteFunction n hn c := by
  apply continuous_eq_of_ae_eq_complexGaussian hn
  · exact (contDiff_normalizedVandermonde_centered hf.1).continuous
  · exact continuous_finiteHermiteFunction n hn c
  · calc
      _ =ᵐ[complexGaussianMeasure n] transformedCenteredObservableL2 hn f hf :=
        (transformedCenteredObservableL2_coeFn hn f hf).symm
      _ =ᵐ[complexGaussianMeasure n] finiteHermiteCombination n hn c := by
        rw [hL2]
      _ =ᵐ[complexGaussianMeasure n] finiteHermiteFunction n hn c :=
        finiteHermiteCombination_coeFn n hn c

/-- Parseval realizes the concrete Ginibre variance as the coefficient mass
of any finite Hermite expansion of the transformed centered observable. -/
theorem finiteHermite_variance_identity {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f)
    (c : HermiteMultiIndex n →₀ ℂ)
    (hL2 : transformedCenteredObservableL2 hn f hf =
      finiteHermiteCombination n hn c) :
    smoothGinibreVariance n f = c.sum fun _ a => Complex.normSq a := by
  rw [← norm_sq_transformedCenteredObservableL2 hn f hf, hL2,
    norm_sq_finiteHermiteCombination]

/-- The Gaussian antiholomorphic energy of a realized finite expansion is
the exact Hermite diagonal energy divided by `n`. -/
theorem finiteHermite_gaussianDbarEnergy_identity {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f)
    (c : HermiteMultiIndex n →₀ ℂ)
    (hL2 : transformedCenteredObservableL2 hn f hf =
      finiteHermiteCombination n hn c) :
    gaussianDbarEnergy n
        (normalizedVandermondeTransform n
          (fun z => (centeredObservable n f z : ℂ))) =
      (1 / (n : ℝ)) * finiteDbarEnergy c := by
  rw [transformedCentered_eq_finiteHermiteFunction hn f hf c hL2]
  unfold gaussianDbarEnergy dbarNormSq
  congr 1
  rw [integral_finsetSum]
  · have h := finiteGaussianDbarIntegralEnergy n hn c
    have hre := congrArg Complex.re h
    calc
      _ = ∑ j : Fin n,
          (∫ z, conj (dbarComponent (finiteHermiteFunction n hn c) j z) *
            dbarComponent (finiteHermiteFunction n hn c) j z
            ∂complexGaussianMeasure n).re := by
        apply Finset.sum_congr rfl
        intro j hj
        let u := finiteHermiteCombination n hn (loweredCoefficients n c j)
        have hcint : Integrable (fun z =>
            conj (dbarComponent (finiteHermiteFunction n hn c) j z) *
              dbarComponent (finiteHermiteFunction n hn c) j z)
            (complexGaussianMeasure n) := by
          have hu := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) u u
          apply hu.congr
          filter_upwards [finiteHermiteCombination_coeFn n hn
            (loweredCoefficients n c j)] with z hz
          rw [hz, ← dbarComponent_finiteHermiteFunction n hn c j z]
          rw [RCLike.inner_apply]
          ring
        calc
          _ = ∫ z, (conj (dbarComponent (finiteHermiteFunction n hn c) j z) *
              dbarComponent (finiteHermiteFunction n hn c) j z).re
              ∂complexGaussianMeasure n := by
            apply integral_congr_ae
            filter_upwards with z
            simp [Complex.normSq_apply]
          _ = _ := integral_re hcint
      _ = finiteDbarEnergy c := by simpa [map_sum] using hre
  · intro j hj
    let u := finiteHermiteCombination n hn (loweredCoefficients n c j)
    have hcint : Integrable (fun z =>
        conj (dbarComponent (finiteHermiteFunction n hn c) j z) *
          dbarComponent (finiteHermiteFunction n hn c) j z)
        (complexGaussianMeasure n) := by
      have hu := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) u u
      apply hu.congr
      filter_upwards [finiteHermiteCombination_coeFn n hn
        (loweredCoefficients n c j)] with z hz
      rw [hz, ← dbarComponent_finiteHermiteFunction n hn c j z]
      rw [RCLike.inner_apply]
      ring
    apply hcint.re.congr
    filter_upwards [finiteHermiteCombination_coeFn n hn
      (loweredCoefficients n c j)] with z hz
    simp [Complex.normSq_apply]

/-- Exact finite-mode realization of the first (Dirichlet/variance) energy
data: the Ginibre energy is four times the Hermite diagonal energy divided
by `n`. -/
theorem finiteHermite_smoothEnergy_identity {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f)
    (c : HermiteMultiIndex n →₀ ℂ)
    (hL2 : transformedCenteredObservableL2 hn f hf =
      finiteHermiteCombination n hn c) :
    smoothGinibreEnergy n f =
      4 * ((1 / (n : ℝ)) * finiteDbarEnergy c) := by
  rw [groundStateEnergyIdentity n hn (ginibreMeasure_isProbabilityMeasure hn)
    f hf.isSmoothCompactSymmetric,
    finiteHermite_gaussianDbarEnergy_identity hn f hf c hL2]

end
end ComplexHermite
end GinibrePoincare
