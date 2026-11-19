/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreCenterProjectionClasses.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreCenterProjectionEquality
public import LeanPool.GinibrePoincare.Analysis.GinibreOneParticleSpectrum
public import LeanPool.GinibrePoincare.Analysis.VandermondeGroundStateZeroMode

/-!
# Ginibre center projection classes

Part of the ginibre measure and holomorphic geometry development of the
Ginibre Poincaré formalization.

Main results: `ginibreRealCenterL2_ae`, `ginibreRealCenterL2_halfDistance_equality`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- The actual Ginibre L² class of the center sum `S`. -/
def ginibreCenterSumL2 (n : ℕ) (hn : 0 < n) : Lp ℂ 2 (ginibreMeasure n) :=
  (ginibreCoordinateSumPowerL2 n hn 1).val

theorem ginibreCenterSumL2_ae (n : ℕ) (hn : 0 < n) :
    (ginibreCenterSumL2 n hn : Configuration n → ℂ) =ᵐ[ginibreMeasure n] coordinateSum := by
  simpa [ginibreCenterSumL2] using ginibreCoordinateSumPowerL2_ae n hn 1

/-- The center sum belongs to the actual holomorphic closed subspace. -/
theorem ginibreCenterSumL2_mem_holomorphic (n : ℕ) (hn : 0 < n) :
    ginibreCenterSumL2 n hn ∈ ginibreHolomorphicAmbientClosedSpan n hn := by
  let s := ginibreCoordinateSumPowerL2 n hn 1
  let U := vandermondeSymmetricAlternatingEquiv n hn
  let P : ConfigurationPolynomial n :=
    polynomialVandermonde n * ∑ j : Fin n, MvPolynomial.X j
  obtain ⟨hP, hPspan⟩ := exists_memLp_configurationPolynomial_mem_antiDegreeZeroSpan n hn P
  have hrep := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq (ginibreCenterSumL2_ae n hn)
  have hgp : (U s).val = ((groundStateNormalization n : ℂ)⁻¹) •
      hP.toLp (fun z => MvPolynomial.eval z P) := by
    apply Lp.ext
    filter_upwards [normalizedVandermondeL2_coeFn_public n hn s.val,
      hrep, Lp.coeFn_smul ((groundStateNormalization n : ℂ)⁻¹)
        (hP.toLp (fun z => MvPolynomial.eval z P)), hP.coeFn_toLp] with z hU hs hsmul hp
    change (normalizedVandermondeL2 n hn s.val : Configuration n → ℂ) z = _
    rw [hU, hsmul]
    change normalizedVandermondeMultiplier n z * s.val z =
      (groundStateNormalization n : ℂ)⁻¹ * _
    rw [hp]
    change s.val z = coordinateSum z at hs
    rw [hs]
    simp [normalizedVandermondeMultiplier, P, eval_polynomialVandermonde, coordinateSum, mul_assoc]
  have hgzero : (U s).val ∈ hermiteAntiDegreeClosedSpan n hn 0 := by
    rw [hgp]
    exact (hermiteAntiDegreeClosedSpan n hn 0).smul_mem _
      ((hermiteAntiDegreeSpan n hn 0).le_topologicalClosure hPspan)
  have hg : U s ∈ gaussianAlternatingZeroModeClosedSpan n hn := by
    change U s ∈ (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule
    rw [gaussianAlternatingZeroModeClosedSpan_eq_hermiteZeroMode_comap]
    exact hgzero
  have hs : s ∈ ginibreSymmetricHolomorphicPolynomialClosedSpan n hn := by
    have him : U s ∈ (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule.map
        U.toLinearMap := by
      rw [map_ginibreSymmetricHolomorphicPolynomialClosedSpan]
      exact hg
    obtain ⟨w, hw, heq⟩ := him
    have hw' : w = s := U.injective heq
    exact hw' ▸ hw
  exact ⟨s, hs, rfl⟩

/-- The center sum has positive rotation weight one. -/
theorem ginibreCenterSumL2_mem_phase_one (n : ℕ) (hn : 0 < n) :
    ginibreCenterSumL2 n hn ∈ ginibreHolomorphicPhaseDegree n 1 hn := by
  intro u hu
  apply Lp.ext
  have hs := ginibreCenterSumL2_ae n hn
  have hcomp := (measurePreserving_globalPhase_ginibreMeasure hn u
      hu).quasiMeasurePreserving.ae_eq_comp hs
  filter_upwards [Lp.coeFn_compMeasurePreserving (ginibreCenterSumL2 n hn)
    (measurePreserving_globalPhase_ginibreMeasure hn u hu), hcomp,
    Lp.coeFn_smul (u ^ 1) (ginibreCenterSumL2 n hn), hs] with z hleft hsrc hright hval
  change (Lp.compMeasurePreserving (globalPhase u)
    (measurePreserving_globalPhase_ginibreMeasure hn u hu) (ginibreCenterSumL2 n hn)) z = _
  rw [hleft, hright]
  change ginibreCenterSumL2 n hn (globalPhase u z) = (u ^ 1) * ginibreCenterSumL2 n hn z
  simp only [Function.comp_apply] at hsrc
  rw [hsrc, hval]
  simp [coordinateSum, globalPhase, Finset.mul_sum]

/-- The center sum is centered in the literal orthogonal-projection sense. -/
theorem ginibreCenterSumL2_constantProjection_zero (n : ℕ) (hn : 0 < n) :
    (ginibreConstantClosedSubspace n hn).starProjection (ginibreCenterSumL2 n hn) = 0 := by
  apply (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((ginibreConstantClosedSubspace n hn).zero_mem) ?_)
  intro y hy
  rw [sub_zero]
  have hy0 : y ∈ ginibreFiniteQuotientDegreeClosedSpan n 0 hn := by
    rwa [ginibreFiniteQuotientDegreeZero_eq_constants]
  exact inner_eq_zero_of_ginibre_phase_degrees_ne hn (by decide : (1 : ℕ) ≠ 0)
    (ginibreCenterSumL2 n hn) y (ginibreCenterSumL2_mem_phase_one n hn)
    (ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n 0 hn hy0)

/-- Membership in the positive holomorphic class used in Remark 2.8. -/
theorem ginibreCenterSumL2_mem_positive (n : ℕ) (hn : 0 < n) :
    ginibreCenterSumL2 n hn ∈ ginibrePositiveQuotientGradedClosedSpan n hn := by
  have h := ginibreHolomorphicProjection_split n hn (ginibreCenterSumL2 n hn)
  rw [Submodule.starProjection_eq_self_iff.mpr (ginibreCenterSumL2_mem_holomorphic n hn),
    ginibreCenterSumL2_constantProjection_zero, zero_add] at h
  rw [h]
  exact Submodule.starProjection_apply_mem _ _

/-- The conjugate center sum has zero holomorphic projection. -/
theorem ginibreCenterSumL2_conjugateProjection_zero (n : ℕ) (hn : 0 < n) :
    (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
      (star (ginibreCenterSumL2 n hn)) = 0 := by
  let S := ginibreCenterSumL2 n hn
  let C := ginibreConstantClosedSubspace n hn
  let P := ginibrePositiveQuotientGradedClosedSpan n hn
  have hC : C.starProjection (star S) = 0 := by
    rw [ginibreConstantProjection_star, ginibreCenterSumL2_constantProjection_zero,
      ginibreLpStar_zero]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((ginibreHolomorphicAmbientClosedSpan n hn).zero_mem)
  intro y hy
  rw [sub_zero]
  have hsplit := ginibreHolomorphicProjection_split n hn y
  rw [Submodule.starProjection_eq_self_iff.mpr hy] at hsplit
  rw [hsplit, inner_add_right]
  have hc := Submodule.starProjection_inner_eq_zero (star S) (C.starProjection y)
    (Submodule.starProjection_apply_mem C.toSubmodule y)
  rw [hC, sub_zero] at hc
  have hp : inner ℂ (P.starProjection y) (star S) = 0 :=
    inner_star_eq_zero_of_mem_positiveQuotientGradedClosedSpan hn
      (Submodule.starProjection_apply_mem P.toSubmodule y)
      (ginibreCenterSumL2_mem_positive n hn)
  rw [hc, ← inner_conj_symm (star S) (P.starProjection y), hp, map_zero, add_zero]

/-- Actual L² class of the real center observable. -/
def ginibreRealCenterL2 (n : ℕ) (hn : 0 < n) : Lp ℂ 2 (ginibreMeasure n) :=
  (1 / 2 : ℂ) • ginibreCenterSumL2 n hn +
    (1 / 2 : ℂ) • star (ginibreCenterSumL2 n hn)

theorem ginibreRealCenterL2_ae (n : ℕ) (hn : 0 < n) :
    (ginibreRealCenterL2 n hn : Configuration n → ℂ) =ᵐ[ginibreMeasure n]
      fun z => (centerOfMassReal z : ℂ) := by
  let S := ginibreCenterSumL2 n hn
  filter_upwards [Lp.coeFn_add ((1 / 2 : ℂ) • S) ((1 / 2 : ℂ) • star S),
    Lp.coeFn_smul (1 / 2 : ℂ) S, Lp.coeFn_smul (1 / 2 : ℂ) (star S),
    Lp.coeFn_star S, ginibreCenterSumL2_ae n hn] with z hadd hsmul hsstar hstar hs
  change (((1 / 2 : ℂ) • S) + ((1 / 2 : ℂ) • star S)) z = _
  rw [hadd]
  change ((1 / 2 : ℂ) • S) z + ((1 / 2 : ℂ) • star S) z = _
  rw [hsmul, hsstar]
  change (1 / 2 : ℂ) * S z + (1 / 2 : ℂ) * (star S) z = _
  rw [hstar]
  change (1 / 2 : ℂ) * S z + (1 / 2 : ℂ) * conj (S z) = _
  rw [hs]
  exact (centerOfMassReal_complex_decomposition n z).symm

/-- Equation (2.36): the literal holomorphic projection of the real center
is one half of the holomorphic center sum. -/
theorem ginibreRealCenterL2_holomorphicProjection (n : ℕ) (hn : 0 < n) :
    (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
      (ginibreRealCenterL2 n hn) = (1 / 2 : ℂ) • ginibreCenterSumL2 n hn := by
  rw [ginibreRealCenterL2, map_add, map_smul, map_smul,
    Submodule.starProjection_eq_self_iff.mpr (ginibreCenterSumL2_mem_holomorphic n hn),
    ginibreCenterSumL2_conjugateProjection_zero, smul_zero, add_zero]

/-- The projection residual is exactly half the conjugate center sum. -/
theorem ginibreRealCenterL2_projectionResidual (n : ℕ) (hn : 0 < n) :
    ginibreRealCenterL2 n hn -
      (ginibreHolomorphicAmbientClosedSpan n hn).starProjection (ginibreRealCenterL2 n hn) =
        (1 / 2 : ℂ) • star (ginibreCenterSumL2 n hn) := by
  rw [ginibreRealCenterL2_holomorphicProjection, ginibreRealCenterL2]
  abel

/-- Equation (2.36)'s squared projection distance. -/
theorem ginibreRealCenterL2_projectionDistance (n : ℕ) (hn : 0 < n) :
    ‖ginibreRealCenterL2 n hn -
      (ginibreHolomorphicAmbientClosedSpan n hn).starProjection (ginibreRealCenterL2 n hn)‖ ^ 2 =
        (1 / 4 : ℝ) * ‖star (ginibreCenterSumL2 n hn)‖ ^ 2 := by
  rw [ginibreRealCenterL2_projectionResidual, norm_smul, mul_pow]
  norm_num

/-- Equality in the half-distance estimate, equation (2.36). -/
theorem ginibreRealCenterL2_halfDistance_equality (n : ℕ) (hn : 0 < n) :
    ‖ginibreRealCenterL2 n hn -
      (ginibreHolomorphicAmbientClosedSpan n hn).starProjection (ginibreRealCenterL2 n hn)‖ ^ 2 =
        (1 / 2 : ℝ) * ‖ginibreRealCenterL2 n hn‖ ^ 2 := by
  let S := ginibreCenterSumL2 n hn
  have horth : inner ℂ S (star S) = 0 :=
    inner_star_eq_zero_of_mem_positiveQuotientGradedClosedSpan hn
      (ginibreCenterSumL2_mem_positive n hn) (ginibreCenterSumL2_mem_positive n hn)
  have hstar : ‖star S‖ = ‖S‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    exact congrArg ENNReal.toReal AEEqFun.eLpNorm_star
  have hsum : ‖S + star S‖ ^ 2 = 2 * ‖S‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero S (star S) horth
    rw [hstar] at h
    nlinarith
  have hf : ‖ginibreRealCenterL2 n hn‖ ^ 2 = (1 / 2 : ℝ) * ‖S‖ ^ 2 := by
    have he : ginibreRealCenterL2 n hn = (1 / 2 : ℂ) • (S + star S) := by
      simp [ginibreRealCenterL2, S, smul_add]
    rw [he, norm_smul, mul_pow, hsum]
    norm_num
    ring
  rw [ginibreRealCenterL2_projectionDistance, show ‖star (ginibreCenterSumL2 n hn)‖ =
    ‖ginibreCenterSumL2 n hn‖ from hstar, hf]
  dsimp [S]
  ring

end
end GinibrePoincare

