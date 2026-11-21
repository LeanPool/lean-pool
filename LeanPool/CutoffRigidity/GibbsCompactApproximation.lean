/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsFormConfinement
public import LeanPool.CutoffRigidity.GibbsMoments
public import LeanPool.CutoffRigidity.GibbsLocalizedTranslations
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Actual global Gibbs compact-approximation prerequisites

Spatial cutoff errors are uniformly small on the genuine closed H¹ unit
ball by the proved form confinement. Uniform convexity also bounds the
actual Gibbs density and yields the canonical continuous linear inclusion
from Lebesgue L² to Gibbs L². No compact embedding is assumed here.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- Compact cutoff errors of actual Gibbs L² classes are genuine L² functions. -/
theorem gibbs_cutoff_error_memLp
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (u : EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] ℝ) :
    MemLp (fun x => u x - χ x * u x) 2 (gibbsMeasure volume V) := by
  let := hprob
  have hχL : MemLp χ ⊤ (gibbsMeasure volume V) := hχ.memLp_of_hasCompactSupport hχc
  have hm : MemLp (fun x => χ x * u x) 2 (gibbsMeasure volume V) := hχL.fun_mul (Lp.memLp u)
  convert! (Lp.memLp u).sub hm using 1

/-- The actual cutoff error is controlled by the actual Gibbs spatial tail. -/
theorem gibbsSobolev_cutoff_error_integral_sq_le
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχbounds : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {R : ℝ} (hR : 0 < R)
    (hχone : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, χ x = 1)
    (u : gibbsSobolevGraph hV hprob) :
    (∫ x, (gibbsSobolevInclusion hV hprob u x - χ x * gibbsSobolevInclusion hV hprob u x) ^ 2
      ∂gibbsMeasure volume V) ≤ gibbsFormConfinementConstant V ρ * ‖u‖ ^ 2 / R ^ 2 := by
  let μ := gibbsMeasure volume V
  let U := gibbsSobolevInclusion hV hprob u
  let S := {x : EuclideanSpace ℝ (Fin d) | R ≤ ‖x‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_norm.measurable
  have hi := integral_mono (gibbs_cutoff_error_memLp hprob hχ hχc U).integrable_sq
    ((Lp.memLp U).integrable_sq.indicator hS) (fun x => by
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        have hb := hχbounds x
        have hs : (1 - χ x) ^ 2 ≤ 1 := by nlinarith
        have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (U x))
        nlinarith
      · rw [Set.indicator_of_notMem hx]
        have hxR : ‖x‖ ≤ R := (lt_of_not_ge hx).le
        have hone := hχone x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hxR)
        simp only [hone, one_mul, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        exact le_rfl)
  rw [integral_indicator hS] at hi
  exact hi.trans (gibbsSobolev_tail_bound hV hprob ρ hρ hHess u R hR)

/-- The actual uniform H¹ cutoff error, in the genuine Gibbs L² norm. -/
theorem gibbsSobolev_cutoff_error_L2_norm_le
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχbounds : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {R : ℝ} (hR : 0 < R)
    (hχone : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, χ x = 1)
    (u : gibbsSobolevGraph hV hprob) :
    ‖(gibbs_cutoff_error_memLp hprob hχ hχc (gibbsSobolevInclusion hV hprob u)).toLp
      (fun x => gibbsSobolevInclusion hV hprob u x - χ x * gibbsSobolevInclusion hV hprob u x)‖ ≤
      Real.sqrt (gibbsFormConfinementConstant V ρ) / R * ‖u‖ := by
  have hC : 0 ≤ gibbsFormConfinementConstant V ρ := by
    unfold gibbsFormConfinementConstant
    positivity
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_toLp_sq, mul_pow, div_pow, Real.sq_sqrt hC]
  have h := gibbsSobolev_cutoff_error_integral_sq_le hV hprob ρ hρ hHess hχ hχc hχbounds hR hχone u
  convert! h using 1
  ring

/-- A concrete smooth compact cutoff equal to one on the full starting ball. -/
@[expose] noncomputable def gibbsSpatialCutoff (R : ℝ) (hR : 0 < R) : EuclideanSpace ℝ (Fin d) → ℝ
  :=
  (⟨R, 2 * R, hR, by linarith⟩ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))

theorem gibbsSpatialCutoff_contDiff (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ 2 (gibbsSpatialCutoff (d := d) R hR) :=
  (⟨R, 2 * R, hR, by linarith⟩ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).contDiff

theorem gibbsSpatialCutoff_hasCompactSupport (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (gibbsSpatialCutoff (d := d) R hR) :=
  (⟨R, 2 * R, hR, by linarith⟩ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).hasCompactSupport

theorem gibbsSpatialCutoff_bounds (R : ℝ) (hR : 0 < R) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ gibbsSpatialCutoff R hR x ∧ gibbsSpatialCutoff R hR x ≤ 1 :=
  ⟨(⟨R, 2 * R, hR, by linarith⟩ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).nonneg,
    (⟨R, 2 * R, hR, by linarith⟩ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).le_one⟩

theorem gibbsSpatialCutoff_one (R : ℝ) (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Metric.closedBall 0 R) : gibbsSpatialCutoff R hR x = 1
      :=
  (⟨R, 2 * R, hR, by linarith⟩ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).one_of_mem_closedBall
    hx

/-- The actual smooth spatial cutoffs approximate the closed Sobolev
inclusion uniformly on graph-energy balls, with error O(R⁻¹). -/
theorem gibbsSobolev_spatial_cutoff_error_L2_norm_le
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (R : ℝ) (hR : 0 < R) (u : gibbsSobolevGraph hV hprob) :
    ‖(gibbs_cutoff_error_memLp hprob (gibbsSpatialCutoff_contDiff R hR).continuous
      (gibbsSpatialCutoff_hasCompactSupport R hR) (gibbsSobolevInclusion hV hprob u)).toLp
      (fun x => gibbsSobolevInclusion hV hprob u x - gibbsSpatialCutoff R hR x *
        gibbsSobolevInclusion hV hprob u x)‖ ≤
      Real.sqrt (gibbsFormConfinementConstant V ρ) / R * ‖u‖ :=
  gibbsSobolev_cutoff_error_L2_norm_le hV hprob ρ hρ hHess (gibbsSpatialCutoff_contDiff R
    hR).continuous
    (gibbsSpatialCutoff_hasCompactSupport R hR) (gibbsSpatialCutoff_bounds R hR) hR
    (gibbsSpatialCutoff_one R hR) u

/-- Uniform convexity gives a global bound for the actual Gibbs density. -/
theorem gibbs_density_uniform_bound
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : EuclideanSpace ℝ (Fin d)) :
    Real.exp (-V x) ≤ Real.exp (‖gradient V 0‖ ^ 2 / ρ - V 0) := by
  have h := gibbs_density_gaussian_domination hV ρ hρ hHess x
  have he : Real.exp (-(ρ / 4) * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr
    (by nlinarith [sq_nonneg ‖x‖])
  exact h.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)

/-- The actual Gibbs measure is dominated by a finite explicit multiple of
Lebesgue measure; this is a proved density bound, not a measure premise. -/
theorem gibbsMeasure_le_smul_volume
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    gibbsMeasure volume V ≤ ENNReal.ofReal (Real.exp (‖gradient V 0‖ ^ 2 / ρ - V 0)) • volume := by
  rw [gibbsMeasure]
  have h := withDensity_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_le_ofReal (gibbs_density_uniform_bound hV
      ρ hρ hHess x)))
  exact h.trans_eq (withDensity_const _)

/-- The canonical actual continuous linear map from Lebesgue L² to the
uniformly convex Gibbs L² space. -/
@[expose] noncomputable def volumeToGibbsL2
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    (EuclideanSpace ℝ (Fin d) →₂[volume] ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] ℝ) :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (gibbsMeasure_le_smul_volume hV ρ hρ hHess)

/-- The genuine change-of-measure inclusion preserves actual representatives
almost everywhere for the Gibbs measure. -/
theorem volumeToGibbsL2_coeFn
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (f : EuclideanSpace ℝ (Fin d) →₂[volume] ℝ) :
    (volumeToGibbsL2 hV ρ hρ hHess f : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[gibbsMeasure volume V] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (gibbsMeasure_le_smul_volume hV ρ hρ hHess) f

/-- Explicit finite operator-norm bound for the actual change-of-measure map. -/
theorem volumeToGibbsL2_norm_le
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ‖volumeToGibbsL2 hV ρ hρ hHess‖ ≤ Real.exp (‖gradient V 0‖ ^ 2 / ρ - V 0) ^ (1 / 2 : ℝ) := by
  have h := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := (2 : ℝ≥0∞))
    ENNReal.ofReal_ne_top (gibbsMeasure_le_smul_volume hV ρ hρ hHess)
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, one_div,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h
  convert! h using 1
  simp only [one_div]


/-- Triangle-ready representative compatibility for a localized Gibbs L²
function passed through the actual unweighted-to-weighted inclusion. -/
theorem volumeToGibbsL2_cutoff_coeFn
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (u : EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] ℝ) :
    (volumeToGibbsL2 hV ρ hρ hHess
      ((compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob hχ hχc u).toLp
        (fun x => χ x * u x)) :
      EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[gibbsMeasure volume V] fun x => χ x * u x := by
  exact (volumeToGibbsL2_coeFn hV ρ hρ hHess _).trans
    ((gibbsMeasure_absolutelyContinuous volume V).ae_eq
      (compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob hχ hχc u).coeFn_toLp)

/-- The actual approximation error after unweighted localization and the
canonical continuous inclusion back into Gibbs L². This is directly usable
in the global compactness triangle inequality. -/
theorem gibbsSobolev_cutoff_transferred_error_L2_norm_le
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχbounds : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {R : ℝ} (hR : 0 < R)
    (hχone : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, χ x = 1)
    (u : gibbsSobolevGraph hV hprob) :
    ‖gibbsSobolevInclusion hV hprob u - volumeToGibbsL2 hV ρ hρ hHess
      ((compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob hχ hχc
        (gibbsSobolevInclusion hV hprob u)).toLp
        (fun x => χ x * gibbsSobolevInclusion hV hprob u x))‖ ≤
      Real.sqrt (gibbsFormConfinementConstant V ρ) / R * ‖u‖ := by
  let U := gibbsSobolevInclusion hV hprob u
  let f := (compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob hχ hχc U).toLp
    (fun x => χ x * U x)
  let J := volumeToGibbsL2 hV ρ hρ hHess
  let hE := gibbs_cutoff_error_memLp hprob hχ hχc U
  have heq : U - J f = hE.toLp (fun x => U x - χ x * U x) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub U (J f), volumeToGibbsL2_cutoff_coeFn hV hprob ρ hρ hHess hχ hχc U,
      hE.coeFn_toLp] with x hs hc he
    have hsub : (U - J f : EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] ℝ) x = U x - J f x
      := by
      convert! hs using 1
    rw [hsub, hc, he]
  change ‖U - J f‖ ≤ _
  rw [heq]
  exact gibbsSobolev_cutoff_error_L2_norm_le hV hprob ρ hρ hHess hχ hχc hχbounds hR hχone u

/-- Concrete smooth spatial-cutoff form of the transferred approximation
error, uniform on the genuine closed Gibbs H¹ unit ball. -/
theorem gibbsSobolev_spatial_cutoff_transferred_error_L2_norm_le
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (R : ℝ) (hR : 0 < R) (u : gibbsSobolevGraph hV hprob) :
    ‖gibbsSobolevInclusion hV hprob u - volumeToGibbsL2 hV ρ hρ hHess
      ((compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob
        (gibbsSpatialCutoff_contDiff R hR).continuous (gibbsSpatialCutoff_hasCompactSupport R hR)
        (gibbsSobolevInclusion hV hprob u)).toLp
        (fun x => gibbsSpatialCutoff R hR x * gibbsSobolevInclusion hV hprob u x))‖ ≤
      Real.sqrt (gibbsFormConfinementConstant V ρ) / R * ‖u‖ :=
  gibbsSobolev_cutoff_transferred_error_L2_norm_le hV hprob ρ hρ hHess
    (gibbsSpatialCutoff_contDiff R hR).continuous (gibbsSpatialCutoff_hasCompactSupport R hR)
    (gibbsSpatialCutoff_bounds R hR) hR (gibbsSpatialCutoff_one R hR) u

end CutoffRigidity
