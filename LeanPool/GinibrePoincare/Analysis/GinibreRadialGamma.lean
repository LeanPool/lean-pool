/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreRadialGamma.lean.
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

public import LeanPool.GinibrePoincare.Analysis.EquilibriumProbability
public import LeanPool.GinibrePoincare.Analysis.HomogeneousRadialMeasure
public import LeanPool.GinibrePoincare.Analysis.GlobalPhaseAction
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Gamma law of the recentered Ginibre radius

The polynomially weighted hyperplane Haar measure is homogeneous of degree
`2 * recenteredGammaShape n`. Its quadratic-radius pushforward is therefore
a power-law measure on `(0,∞)`. The Gaussian factor tilts that power law into
the rate-one Gamma density; probability normalization fixes the constant.
The final theorem concerns `radialObservable` under the actual `ginibreMeasure`.
-/


@[expose] public section


open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Pointwise

namespace GinibrePoincare
noncomputable section

/-- Shape of the recentered-radius Gamma law, as an integer. -/
def recenteredGammaShape (n : ℕ) : ℕ := vandermondeDegree n + (n - 1)

/-- The quadratic recentered radius on the intrinsic hyperplane. -/
def hyperplaneRadius (n : ℕ) (w : zeroSumHyperplane n) : ℝ :=
  (n : ℝ) * configurationNormSq w.val

/-- Homogeneous Vandermonde-weighted volume, before applying the Gaussian weight. -/
def recenteredPolynomialMeasure (n : ℕ) : Measure (zeroSumHyperplane n) :=
  (recenteredVolume n).withDensity (fun w => vandermondeDensity w.val)

instance (n : ℕ) : SigmaFinite (recenteredPolynomialMeasure n) := by
  unfold recenteredPolynomialMeasure vandermondeDensity
  infer_instance

theorem zeroSumHyperplane_finrank_complex (n : ℕ) (hn : 0 < n) :
    Module.finrank ℂ (zeroSumHyperplane n) = n - 1 := by
  have h := (equilibriumCoordinates n hn).finrank_eq
  simp only [Module.finrank_pi, Fintype.card_fin, Module.finrank_prod,
    Module.finrank_self] at h
  omega

theorem zeroSumHyperplane_finrank_real (n : ℕ) (hn : 0 < n) :
    Module.finrank ℝ (zeroSumHyperplane n) = 2 * (n - 1) := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (zeroSumHyperplane n),
    Complex.finrank_real_complex, zeroSumHyperplane_finrank_complex n hn]

theorem vandermondeDegree_twice (n : ℕ) :
    2 * vandermondeDegree n = n * (n - 1) := by
  rw [vandermondeDegree_eq_sum_Ioi_card]
  simp_rw [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_reflect (fun i => i) n]
  simpa [Nat.mul_comm] using Finset.sum_range_id_mul_two n

theorem recenteredGammaShape_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < recenteredGammaShape n := by
  unfold recenteredGammaShape
  omega

/-- The integer shape agrees with the paper's exact real normalization. -/
theorem recenteredGammaShape_eq (n : ℕ) (hn : 0 < n) :
    (recenteredGammaShape n : ℝ) = ((n : ℝ) - 1) * ((n : ℝ) + 2) / 2 := by
  have hd := vandermondeDegree_twice n
  have hdR : 2 * (vandermondeDegree n : ℝ) = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hd
  rw [Nat.cast_sub hn] at hdR
  norm_num at hdR
  unfold recenteredGammaShape
  rw [Nat.cast_add, Nat.cast_sub hn]
  push_cast
  nlinarith

theorem configurationNormSq_real_smul (n : ℕ) (t : ℝ) (z : Configuration n) :
    configurationNormSq (t • z) = t ^ 2 * configurationNormSq z := by
  unfold configurationNormSq
  simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.normSq_ofReal,
    ← Finset.mul_sum, pow_two]

theorem hyperplaneRadius_smul (n : ℕ) (t : ℝ) (w : zeroSumHyperplane n) :
    hyperplaneRadius n (t • w) = t ^ 2 * hyperplaneRadius n w := by
  unfold hyperplaneRadius
  rw [show (t • w).val = t • w.val by rfl, configurationNormSq_real_smul]
  ring

theorem hyperplaneRadius_nonneg (n : ℕ) (w : zeroSumHyperplane n) :
    0 ≤ hyperplaneRadius n w := mul_nonneg (Nat.cast_nonneg _) (configurationNormSq_nonneg _)

theorem continuous_hyperplaneRadius (n : ℕ) : Continuous (hyperplaneRadius n) := by
  unfold hyperplaneRadius configurationNormSq
  exact (continuous_finsetSum _ (fun i _ => Complex.continuous_normSq.comp
    ((continuous_apply i).comp continuous_subtype_val))).const_mul _

theorem vandermondeDensity_real_smul (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (z : Configuration n) :
    vandermondeDensity (t • z) =
      ENNReal.ofReal (t ^ (2 * vandermondeDegree n)) * vandermondeDensity z := by
  have hz : t • z = globalPhase (t : ℂ) z := by ext i; simp [globalPhase, Complex.real_smul]
  rw [hz]
  unfold vandermondeDensity vandermondeWeight
  rw [vandermonde_globalPhase, ← vandermondeDegree_eq_sum_Ioi_card,
    map_mul, map_pow, Complex.normSq_ofReal]
  rw [← pow_two, ← pow_mul, ENNReal.ofReal_mul (pow_nonneg ht _)]

theorem hyperplaneRadius_eq_zero_iff (n : ℕ) (hn : 0 < n)
    (w : zeroSumHyperplane n) : hyperplaneRadius n w = 0 ↔ w = 0 := by
  constructor
  · intro hw
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsum : ∑ i : Fin n, Complex.normSq (w.val i) = 0 :=
      (mul_eq_zero.mp hw).resolve_left hnR
    apply Subtype.ext
    ext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (w.val j))).mp hsum i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp hi
  · rintro rfl
    simp [hyperplaneRadius, configurationNormSq]

/-- A quadratic-radius sublevel is compact; in particular the unit sublevel has
finite Vandermonde-weighted Haar mass. -/
theorem isCompact_hyperplaneRadius_unitSublevel (n : ℕ) (hn : 0 < n) :
    IsCompact {w : zeroSumHyperplane n | hyperplaneRadius n w ≤ 1} := by
  have : NormedSpace ℝ (zeroSumHyperplane n) :=
    NormedSpace.restrictScalars ℝ ℂ (zeroSumHyperplane n)
  apply (isCompact_closedBall (0 : zeroSumHyperplane n) 1).of_isClosed_subset
    (isClosed_le (continuous_hyperplaneRadius n) continuous_const)
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖w.val‖ ≤ 1
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  have hs := configurationNormSq_nonneg w.val
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : (n : ℝ) * configurationNormSq w.val ≤ 1 := hw
  have hi : Complex.normSq (w.val i) ≤ configurationNormSq w.val :=
    Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (w.val j)) (Finset.mem_univ i)
  rw [Complex.normSq_eq_norm_sq] at hi
  have hnorm := norm_nonneg (w.val i)
  nlinarith

theorem recenteredPolynomialMeasure_unitSublevel_lt_top (n : ℕ) (hn : 0 < n) :
    recenteredPolynomialMeasure n ((hyperplaneRadius n) ⁻¹' Iic 1) < ⊤ := by
  have hc := isCompact_hyperplaneRadius_unitSublevel n hn
  have hf : Continuous (fun w : zeroSumHyperplane n => vandermondeWeight w.val) :=
    Complex.continuous_normSq.comp (continuous_vandermonde.comp continuous_subtype_val)
  have hi : IntegrableOn (fun w : zeroSumHyperplane n => vandermondeWeight w.val)
      ((hyperplaneRadius n) ⁻¹' Iic 1) (recenteredVolume n) :=
    hf.continuousOn.integrableOn_compact hc
  unfold recenteredPolynomialMeasure
  rw [withDensity_apply _ ((continuous_hyperplaneRadius n).measurable measurableSet_Iic)]
  exact hi.lintegral_lt_top

theorem recenteredPolynomialMeasure_radius_zero (n : ℕ) (hn : 2 ≤ n) :
    recenteredPolynomialMeasure n ((hyperplaneRadius n) ⁻¹' {0}) = 0 := by
  have hn0 : 0 < n := by omega
  have : Nontrivial (zeroSumHyperplane n) := Module.nontrivial_of_finrank_pos
    (by rw [zeroSumHyperplane_finrank_complex n hn0]; omega :
      0 < Module.finrank ℂ (zeroSumHyperplane n))
  have hset : (hyperplaneRadius n) ⁻¹' {0} = {0} := by
    ext w
    simp only [mem_preimage, mem_singleton_iff, hyperplaneRadius_eq_zero_iff n hn0]
  rw [hset]
  unfold recenteredPolynomialMeasure
  exact withDensity_absolutelyContinuous _ _ (measure_singleton _)

theorem recenteredPolynomialMeasure_smul (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 < t) (s : Set (zeroSumHyperplane n)) :
    recenteredPolynomialMeasure n (t • s) =
      ENNReal.ofReal (t ^ (2 * recenteredGammaShape n)) * recenteredPolynomialMeasure n s := by
  unfold recenteredPolynomialMeasure
  have hf : Measurable (fun w : zeroSumHyperplane n => vandermondeDensity w.val) :=
    (measurable_vandermondeDensity (n := n)).comp measurable_subtype_coe
  have hhom : ∀ r : ℝ, 0 < r → ∀ w : zeroSumHyperplane n,
      vandermondeDensity ((r • w).val) =
        ENNReal.ofReal (r ^ (2 * vandermondeDegree n)) * vandermondeDensity w.val := by
    intro r hr w
    change vandermondeDensity (r • w.val) = _
    exact vandermondeDensity_real_smul n r hr.le w.val
  have h := @homogeneous_withDensity_smul (zeroSumHyperplane n)
    inferInstance (NormedSpace.restrictScalars ℝ ℂ (zeroSumHyperplane n))
    inferInstance inferInstance (FiniteDimensional.trans ℝ ℂ (zeroSumHyperplane n))
    (recenteredVolume n) inferInstance
    (fun w : zeroSumHyperplane n => vandermondeDensity w.val) hf
    (2 * vandermondeDegree n) hhom t ht s
  rw [zeroSumHyperplane_finrank_real n hn] at h
  have he : 2 * (n - 1) + 2 * vandermondeDegree n = 2 * recenteredGammaShape n := by
    unfold recenteredGammaShape
    omega
  rw [he] at h
  exact h

/-- The unnormalized radius law is a power-law measure with exponent κ-1. -/
theorem recenteredPolynomialMeasure_radius (n : ℕ) (hn : 2 ≤ n) :
    (recenteredPolynomialMeasure n).map (hyperplaneRadius n) =
      ((recenteredGammaShape n : ℝ≥0∞) *
        recenteredPolynomialMeasure n ((hyperplaneRadius n) ⁻¹' Iic 1)) •
      radialPowerMeasure (recenteredGammaShape n) := by
  have hn0 : 0 < n := by omega
  exact map_quadratic_homogeneous_measure
    (recenteredPolynomialMeasure n) (hyperplaneRadius n)
    (continuous_hyperplaneRadius n).measurable (hyperplaneRadius_nonneg n)
    (recenteredGammaShape n) (recenteredGammaShape_pos n hn)
    (fun t _ w => hyperplaneRadius_smul n t w)
    (fun t ht s => recenteredPolynomialMeasure_smul n hn0 t ht s)
    (recenteredPolynomialMeasure_radius_zero n hn)
    (recenteredPolynomialMeasure_unitSublevel_lt_top n hn0)

/-- The concrete recentered Ginibre marginal is the Gaussian tilt of the
Vandermonde-weighted Haar measure. The scalar is not a hypothesis. -/
theorem recenteredGinibreMeasure_gaussian_tilt (n : ℕ) (hn : 0 < n) :
    ∃ b : ℝ≥0∞, recenteredGinibreMeasure n = b •
      (recenteredPolynomialMeasure n).withDensity
        (fun w => ENNReal.ofReal (Real.exp (-hyperplaneRadius n w))) := by
  obtain ⟨a, _, _, hν⟩ := recenteredGinibreMeasure_eq_withDensity n hn
  let B := (ginibreNormalizingMass n).toReal⁻¹ * ((n : ℝ) / Real.pi) ^ n
  refine ⟨a * ENNReal.ofReal B, ?_⟩
  rw [hν]
  unfold recenteredPolynomialMeasure
  have hv : Measurable (fun w : zeroSumHyperplane n => vandermondeDensity w.val) :=
    (measurable_vandermondeDensity (n := n)).comp measurable_subtype_coe
  have he : Measurable (fun w => ENNReal.ofReal (Real.exp (-hyperplaneRadius n w))) :=
    ENNReal.measurable_ofReal.comp ((Real.continuous_exp.comp (continuous_hyperplaneRadius
      n).neg).measurable)
  rw [← withDensity_mul _ hv he]
  rw [← withDensity_smul _ (hv.mul he)]
  congr 1
  funext w
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  unfold equilibriumGinibreDensity rawGinibreDensity' hyperplaneRadius
    vandermondeDensity vandermondeWeight
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hvR := Complex.normSq_nonneg (vandermonde w.val)
  have hraw :
      (ginibreNormalizingMass n).toReal⁻¹ *
        (((n : ℝ) / Real.pi) ^ n * Real.exp (-(n : ℝ) * configurationNormSq w.val) *
          Complex.normSq (vandermonde w.val)) =
      B * (Complex.normSq (vandermonde w.val) * Real.exp (-(n : ℝ) * configurationNormSq w.val))
        := by
    dsimp [B]
    ring
  rw [hraw, ENNReal.ofReal_mul hB, ENNReal.ofReal_mul hvR]
  simp only [neg_mul, mul_assoc]

/-- The intrinsic recentered radius has the exact Gamma law (shape κ, rate 1). -/
theorem hyperplaneRadius_ginibre_gamma (n : ℕ) (hn : 2 ≤ n) :
    (recenteredGinibreMeasure n).map (hyperplaneRadius n) =
      gammaMeasure (recenteredGammaShape n : ℝ) 1 := by
  have hn0 : 0 < n := by omega
  obtain ⟨b, hb⟩ := recenteredGinibreMeasure_gaussian_tilt n hn0
  have hmap : (recenteredGinibreMeasure n).map (hyperplaneRadius n) =
      (b * ((recenteredGammaShape n : ℝ≥0∞) *
        recenteredPolynomialMeasure n ((hyperplaneRadius n) ⁻¹' Iic 1))) •
        (radialPowerMeasure (recenteredGammaShape n)).withDensity
          (fun x => ENNReal.ofReal (Real.exp (-x))) := by
    rw [hb, Measure.map_smul _ (continuous_hyperplaneRadius n).measurable.aemeasurable]
    have hden : (fun w => ENNReal.ofReal (Real.exp (-hyperplaneRadius n w))) =
        (fun x => ENNReal.ofReal (Real.exp (-x))) ∘ hyperplaneRadius n := rfl
    rw [hden, map_withDensity_comp_measurable _ _
      (continuous_hyperplaneRadius n).measurable _ (by fun_prop),
      recenteredPolynomialMeasure_radius n hn, withDensity_smul_measure, smul_smul]
  have hprob : IsProbabilityMeasure
      ((recenteredGinibreMeasure n).map (hyperplaneRadius n)) := by
    have := recenteredGinibreMeasure_isProbabilityMeasure n hn0
    exact (by infer_instance)
  rw [hmap] at hprob ⊢
  exact normalized_gaussian_tilt_gamma _ (recenteredGammaShape_pos n hn) _ hprob

/-- The paper's radius `n|W|²`, as an observable on the original configuration
space, has the Gamma law with shape `(n-1)(n+2)/2` and rate one. -/
theorem radialObservable_ginibre_gamma (n : ℕ) (hn : 2 ≤ n) :
    (ginibreMeasure n).map (radialObservable n) =
      gammaMeasure (((n : ℝ) - 1) * ((n : ℝ) + 2) / 2) 1 := by
  have hn0 : 0 < n := by omega
  have hcomp : radialObservable n = hyperplaneRadius n ∘ recenteredCoordinate n := rfl
  rw [hcomp, ← Measure.map_map (continuous_hyperplaneRadius n).measurable
    (measurable_recenteredCoordinate n)]
  change (recenteredGinibreMeasure n).map (hyperplaneRadius n) = _
  rw [hyperplaneRadius_ginibre_gamma n hn, recenteredGammaShape_eq n hn0]

end
end GinibrePoincare
