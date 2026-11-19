/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexRadialDensity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticRadialConfinement
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Strong convex radial density

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `radialConfinementProbabilityDensity_pos`,
`radialConfinementProbabilityDensity_isProbability`,
`rhoConvexPotential_radial_density_integrable`, `rhoConvexPotential_radial_density_tendsto_zero`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Positive-radius density for the Kostlan coordinate indexed by k=0,…,n−1,
extended continuously by zero to the negative half-line. -/
def radialConfinementDensity (n k : ℕ) (Q : ℝ → ℝ) (r : ℝ) : ℝ :=
  (max r 0) ^ (2 * k + 1) * Real.exp (-(n : ℝ) * Q r)

theorem radialConfinementDensity_continuous (n k : ℕ) {Q : ℝ → ℝ}
    (hQ : Continuous Q) : Continuous (radialConfinementDensity n k Q) := by
  unfold radialConfinementDensity
  fun_prop

theorem radialConfinementDensity_nonneg (n k : ℕ) (Q : ℝ → ℝ) (r : ℝ) :
    0 ≤ radialConfinementDensity n k Q r := by
  unfold radialConfinementDensity
  positivity

theorem radialConfinementDensity_pos (n k : ℕ) (Q : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) : 0 < radialConfinementDensity n k Q r := by
  unfold radialConfinementDensity
  rw [max_eq_left hr.le]
  positivity

theorem radialConfinementDensity_zero (n k : ℕ) (Q : ℝ → ℝ) {r : ℝ}
    (hr : r ≤ 0) : radialConfinementDensity n k Q r = 0 := by
  simp [radialConfinementDensity, max_eq_right hr]

/-- The genuine density equals exp(−W) on its positive support. -/
theorem radialConfinementDensity_eq_exp (n k : ℕ) (Q : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) :
    radialConfinementDensity n k Q r =
      Real.exp (-radialEffectivePotential n (k + 1) Q r) := by
  unfold radialConfinementDensity radialEffectivePotential
  rw [max_eq_left hr.le]
  have he : (2 * ((k + 1 : ℕ) : ℝ) - 1) = ((2 * k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [he]
  rw [show -((n : ℝ) * Q r - ↑(2 * k + 1) * Real.log r) =
    ↑(2 * k + 1) * Real.log r + -(n : ℝ) * Q r by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log hr]

/-- Quadratic confinement gives integrability of the actual density. -/
theorem radialConfinementDensity_integrable (n k : ℕ) (hn : 0 < n)
    (Q : ℝ → ℝ) (hQ : Continuous Q) (c C : ℝ) (hc : 0 < c)
    (hbound : ∀ r, 0 < r → c * r ^ 2 + C ≤ Q r) :
    Integrable (radialConfinementDensity n k Q) volume := by
  have hnc : 0 < (n : ℝ) * c := mul_pos (Nat.cast_pos.mpr hn) hc
  have hdom : Integrable (fun r : ℝ =>
      Real.exp (-(n : ℝ) * C) * (r ^ (2 * k + 1) * Real.exp (-((n : ℝ) * c) * r ^ 2))) volume := by
    have h := integrable_rpow_mul_exp_neg_mul_sq hnc
      (show (-1 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0)
                                                  (Nat.cast_nonneg _))
    simpa only [Real.rpow_natCast] using h.const_mul (Real.exp (-(n : ℝ) * C))
  apply hdom.norm.mono' (radialConfinementDensity_continuous n k hQ).aestronglyMeasurable
  apply ae_of_all
  intro r
  rw [Real.norm_eq_abs, abs_of_nonneg (radialConfinementDensity_nonneg n k Q r)]
  by_cases hr : 0 < r
  · rw [radialConfinementDensity, max_eq_left hr.le]
    have he : Real.exp (-(n : ℝ) * Q r) ≤
        Real.exp (-(n : ℝ) * C) * Real.exp (-((n : ℝ) * c) * r ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (hbound r hr) (Nat.cast_nonneg n)
      nlinarith
    have hh := mul_le_mul_of_nonneg_left he (pow_nonneg hr.le (2 * k + 1))
    change _ ≤ ‖Real.exp (-(n : ℝ) * C) *
      (r ^ (2 * k + 1) * Real.exp (-((n : ℝ) * c) * r ^ 2))‖
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  · rw [radialConfinementDensity_zero n k Q (le_of_not_gt hr)]
    exact norm_nonneg _

theorem radialConfinementDensity_mass_pos (n k : ℕ) (Q : ℝ → ℝ)
    (hi : Integrable (radialConfinementDensity n k Q) volume) :
    0 < ∫ r, radialConfinementDensity n k Q r := by
  apply (integral_pos_iff_support_of_nonneg
    (radialConfinementDensity_nonneg n k Q) hi).mpr
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support (radialConfinementDensity n k Q) := by
    intro r hr
    exact (radialConfinementDensity_pos n k Q hr.1).ne'
  exact lt_of_lt_of_le (by simp : 0 < volume (Ioo (0 : ℝ) 1)) (measure_mono hsub)

theorem radialConfinementDensity_tendsto_zero (n k : ℕ) (hn : 0 < n)
    (Q : ℝ → ℝ) (c C : ℝ) (hc : 0 < c)
    (hbound : ∀ r, 0 < r → c * r ^ 2 + C ≤ Q r) :
    Tendsto (radialConfinementDensity n k Q) atTop (𝓝 0) := by
  have hnc : 0 < (n : ℝ) * c := mul_pos (Nat.cast_pos.mpr hn) hc
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((2 * k + 1 : ℕ) : ℝ) ((n : ℝ) * c) hnc).const_mul (Real.exp (-(n : ℝ) * C))
  simp only [Real.rpow_natCast, mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (radialConfinementDensity_nonneg n k Q)) ?_ ht
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  unfold radialConfinementDensity
  rw [max_eq_left hrpos.le]
  have he : Real.exp (-(n : ℝ) * Q r) ≤
      Real.exp (-(n : ℝ) * C) * Real.exp (-((n : ℝ) * c) * r) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (hbound r hrpos) (Nat.cast_nonneg n)
    have hrr : r ≤ r ^ 2 := by nlinarith
    have hcc := mul_le_mul_of_nonneg_left hrr hnc.le
    nlinarith
  have hh := mul_le_mul_of_nonneg_left he (pow_nonneg hrpos.le (2 * k + 1))
  nlinarith

/-- Normalization uses the integral of the actual unnormalized density. -/
def radialConfinementProbabilityDensity (n k : ℕ) (Q : ℝ → ℝ) (r : ℝ) : ℝ :=
  radialConfinementDensity n k Q r / ∫ t, radialConfinementDensity n k Q t

theorem radialConfinementProbabilityDensity_integral (n k : ℕ) (Q : ℝ → ℝ)
    (hi : Integrable (radialConfinementDensity n k Q) volume) :
    ∫ r, radialConfinementProbabilityDensity n k Q r = 1 := by
  unfold radialConfinementProbabilityDensity
  rw [integral_div, div_self (radialConfinementDensity_mass_pos n k Q hi).ne']

theorem radialConfinementProbabilityDensity_continuous (n k : ℕ) {Q : ℝ → ℝ}
    (hQ : Continuous Q) : Continuous (radialConfinementProbabilityDensity n k Q) :=
  (radialConfinementDensity_continuous n k hQ).div_const _

theorem radialConfinementProbabilityDensity_hasDerivAt (n k : ℕ)
    (Q : ℝ → ℝ) (hQ : Differentiable ℝ Q) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (radialConfinementProbabilityDensity n k Q)
      (-deriv (radialEffectivePotential n (k + 1) Q) r *
        radialConfinementProbabilityDensity n k Q r) r := by
  let W := radialEffectivePotential n (k + 1) Q
  have hW : DifferentiableAt ℝ W r :=
    ((hQ r).const_mul (n : ℝ)).sub
      ((Real.differentiableAt_log hr.ne').const_mul (2 * ((k + 1 : ℕ) : ℝ) - 1))
  have h := (hW.hasDerivAt.neg.exp).div_const
    (∫ t, radialConfinementDensity n k Q t)
  have he : (fun t => Real.exp (-W t) / ∫ x, radialConfinementDensity n k Q x) =ᶠ[𝓝 r]
      radialConfinementProbabilityDensity n k Q := by
    filter_upwards [eventually_gt_nhds hr] with t ht
    exact congrArg (fun x => x / ∫ x, radialConfinementDensity n k Q x)
      (radialConfinementDensity_eq_exp n k Q ht).symm
  apply (h.congr_of_eventuallyEq he.symm).congr_deriv
  rw [radialConfinementProbabilityDensity, radialConfinementDensity_eq_exp n k Q hr]
  dsimp [W]
  ring

theorem radialConfinementProbabilityDensity_contDiffAt (n k : ℕ)
    {Q : ℝ → ℝ} (hQ : ContDiff ℝ 2 Q) {r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ 2 (radialConfinementProbabilityDensity n k Q) r := by
  have he : radialConfinementProbabilityDensity n k Q =ᶠ[𝓝 r]
      (fun t => t ^ (2 * k + 1) * Real.exp (-(n : ℝ) * Q t) /
        ∫ x, radialConfinementDensity n k Q x) := by
    filter_upwards [eventually_gt_nhds hr] with t ht
    simp only [radialConfinementProbabilityDensity, radialConfinementDensity, max_eq_left ht.le]
  apply ContDiffAt.congr_of_eventuallyEq _ he
  fun_prop

theorem radialConfinementProbabilityDensity_nonneg (n k : ℕ) (Q : ℝ → ℝ)
    (hi : Integrable (radialConfinementDensity n k Q) volume) (r : ℝ) :
    0 ≤ radialConfinementProbabilityDensity n k Q r :=
  div_nonneg (radialConfinementDensity_nonneg n k Q r)
    (radialConfinementDensity_mass_pos n k Q hi).le

theorem radialConfinementProbabilityDensity_pos (n k : ℕ) (Q : ℝ → ℝ)
    (hi : Integrable (radialConfinementDensity n k Q) volume) {r : ℝ} (hr : 0 < r) :
    0 < radialConfinementProbabilityDensity n k Q r :=
  div_pos (radialConfinementDensity_pos n k Q hr)
    (radialConfinementDensity_mass_pos n k Q hi)

/-- The normalized scalar density defines an actual probability measure. -/
theorem radialConfinementProbabilityDensity_isProbability (n k : ℕ)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hi : Integrable (radialConfinementDensity n k Q) volume) :
    IsProbabilityMeasure ((volume : Measure ℝ).withDensity
      (fun r => ENNReal.ofReal (radialConfinementProbabilityDensity n k Q r))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hp := radialConfinementProbabilityDensity_nonneg n k Q hi
  have hm := (radialConfinementProbabilityDensity_continuous n k hQ).measurable
  have hpi : Integrable (radialConfinementProbabilityDensity n k Q) volume := hi.div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hpi (Eventually.of_forall hp),
    radialConfinementProbabilityDensity_integral n k Q hi]
  norm_num

theorem rhoConvexPotential_radial_density_integrable (n k : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    Integrable (radialConfinementDensity n k (fun r : ℝ => V (r : ℂ))) volume := by
  apply radialConfinementDensity_integrable n k hn _
    (hV.continuous.comp Complex.continuous_ofReal) (ρ / 2) (V 0) (by positivity)
  intro r hr
  simpa only [Complex.normSq_ofReal, pow_two, Function.comp_apply] using
    rhoConvexPotential_quadratic_lower_bound ρ hrot hc (r : ℂ)

theorem rhoConvexPotential_radial_density_tendsto_zero (n k : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential}
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    Tendsto (radialConfinementProbabilityDensity n k (fun r : ℝ => V (r : ℂ)))
      atTop (𝓝 0) := by
  have ht := radialConfinementDensity_tendsto_zero n k hn
    (fun r : ℝ => V (r : ℂ)) (ρ / 2) (V 0) (by positivity) (by
      intro r hr
      simpa only [Complex.normSq_ofReal, pow_two, Function.comp_apply] using
        rhoConvexPotential_quadratic_lower_bound ρ hrot hc (r : ℂ))
  change Tendsto (fun r => radialConfinementDensity n k (fun t : ℝ => V (t : ℂ)) r /
    ∫ x, radialConfinementDensity n k (fun t : ℝ => V (t : ℂ)) x) atTop (𝓝 0)
  simpa only [zero_div] using ht.div_const
    (∫ r, radialConfinementDensity n k (fun t : ℝ => V (t : ℂ)) r)

end
end GinibrePoincare
