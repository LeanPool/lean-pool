/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpP8
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34Slices
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder

/-!
# The local `L^{3/2}` class and linear growth of `p₇ + p₈` for the ball cut-off

The decomposition `prop:pressure-decomposition`, grouped in `cor:CZ-harmonic`,
splits the pressure into a Calderón–Zygmund part, a harmonic remainder, and
the force part `p₇ + p₈`. The force potentials use the smooth ball cutoff `η`
of the radius-`ρ` ball at `x₀`. The cancellation feeding the Liouville step of `ext:newtonian`
needs the pair `p₇ + p₈` of force potentials to be `L^{3/2}` on every round ball about the
origin with local norm growing at most linearly in the radius, and it needs the growth
constant to be nonnegative.

The membership of the two potentials was proved in
`CKN/Foundation/Euclidean/PotentialLocalLpP8.lean` under the single-slice hypotheses that
each datum `η fⱼ` and `(∂ⱼη) fⱼ` is `L^q` on the whole space for some `q ≥ 6/5` and vanishes
off a fixed closed ball.  This file discharges those hypotheses for the concrete cut-off
`mollifiedBallCutoff x₀ hρ` from a single `L^q` hypothesis on the slice `f(·, s)` over the
ball `vec3Ball x₀ ρ`: the cut-off is bounded by `1`, its derivative is bounded by
`cutoffGradientConstant / ρ`, and both are supported in that ball.  The resulting growth
constant is recorded as `czHarmonicForceGrowthConstant`.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
noncomputable section

namespace CKN

/-- The coordinate projections dominate the ambient norm on `Vec3 = Fin 3 → ℝ`. -/
private lemma norm_le_vec3EuclideanNorm (x : Vec3) :
    ‖x‖ ≤ vec3EuclideanNorm x := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg x)]
  intro i
  change |x i| ≤ vec3EuclideanNorm x
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _hj => sq_nonneg (x j)) (Finset.mem_univ i)

/-- A function that is `L^r` on a Euclidean ball and vanishes off it is `L^r` on all of
`ℝ³`. -/
private lemma memLp_of_memLp_restrict_vec3Ball {g : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    {r : ℝ≥0∞} (hg : MemLp g r (volume.restrict (vec3Ball x₀ ρ)))
    (hzero : ∀ y, y ∉ vec3Ball x₀ ρ → g y = 0) : MemLp g r volume := by
  have hind : (vec3Ball x₀ ρ).indicator g = g := by
    apply Set.indicator_eq_self.2
    exact Function.support_subset_iff'.2 hzero
  have h := (memLp_indicator_iff_restrict (isOpen_vec3Ball x₀ ρ).measurableSet).2 hg
  rwa [hind] at h

/-- The linear-growth constant of `p₇ + p₈` for the cutoff of `lem:cutoff` at `x₀` of radius
`ρ`. -/
@[expose]
def czHarmonicForceGrowthConstant (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (f : ParabolicPoint → Vec3) (s : ℝ) : ℝ :=
  CKN.Foundation.Euclidean.pressureP7GrowthConstant (mollifiedBallCutoff x₀ hρ) f s
      (‖x₀‖ + ρ) +
    CKN.Foundation.Euclidean.pressureP8GrowthConstant (mollifiedBallCutoff x₀ hρ) f s
      (‖x₀‖ + ρ)

/-- The componentwise hypotheses of the force-cancellation estimate of `lem:pk-bounds` hold
for the ball cut-off `mollifiedBallCutoff x₀ hρ` as soon as the slice `f(·, s)` is `L^q` on
the ball `vec3Ball x₀ ρ` with `q ≥ 6/5`.  The two force potentials `p₇ + p₈` are therefore
`L^{3/2}` on every round ball about the origin, with local norm bounded by the nonnegative
constant `czHarmonicForceGrowthConstant` times `1 + R`, as required by the Liouville step of
`ext:newtonian`. -/
theorem pressureP7_add_pressureP8_local_of_slice_memLp
    {f : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ q : ℝ} (hρ : 0 < ρ) (hq : 6 / 5 ≤ q) {s : ℝ}
    (hf : MemLp (fun x : Vec3 => f (x, s)) (ENNReal.ofReal q)
      (volume.restrict (vec3Ball x₀ ρ))) :
    (∀ R : ℝ, 0 < R →
        MemLp (pressureP7 (mollifiedBallCutoff x₀ hρ) f s +
          pressureP8 (mollifiedBallCutoff x₀ hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
      0 ≤ czHarmonicForceGrowthConstant x₀ hρ f s ∧
      ∀ R : ℝ, 0 < R →
        lpNorm (pressureP7 (mollifiedBallCutoff x₀ hρ) f s +
          pressureP8 (mollifiedBallCutoff x₀ hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤
          czHarmonicForceGrowthConstant x₀ hρ f s * (1 + R) := by
  have hfj : ∀ j : Fin 3, MemLp (fun x : Vec3 => f (x, s) j) (ENNReal.ofReal q)
      (volume.restrict (vec3Ball x₀ ρ)) := fun j => by
    simpa only [ContinuousLinearMap.proj_apply] using
      hf.continuousLinearMap_comp (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)
  have hηmeas : AEStronglyMeasurable (mollifiedBallCutoff x₀ hρ)
      (volume.restrict (vec3Ball x₀ ρ)) :=
    (mollifiedBallCutoff_smooth x₀ hρ).continuous.aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hηbound : ∀ y : Vec3, ‖mollifiedBallCutoff x₀ hρ y‖ ≤ (1 : ℝ) := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (mollifiedBallCutoff_nonneg x₀ hρ y)]
    exact mollifiedBallCutoff_le_one x₀ hρ y
  have hηsupp : tsupport (mollifiedBallCutoff x₀ hρ) ⊆ vec3Ball x₀ ρ :=
    pressure_cutoff_support_subset_ball x₀ hρ
  have hηzero : ∀ y, y ∉ vec3Ball x₀ ρ → mollifiedBallCutoff x₀ hρ y = 0 :=
    fun y hy => image_eq_zero_of_notMem_tsupport (fun hyt => hy (hηsupp hyt))
  have hηderivzero : ∀ (j : Fin 3) (y : Vec3), y ∉ vec3Ball x₀ ρ →
      spatialDeriv (mollifiedBallCutoff x₀ hρ) j y = 0 :=
    fun j y hy => image_eq_zero_of_notMem_tsupport
      (fun hyt => hy (hηsupp ((tsupport_fderiv_apply_subset ℝ (basisVec j)) hyt)))
  -- A point outside the ambient closed ball of radius `‖x₀‖ + ρ` is outside `vec3Ball x₀ ρ`.
  have hnotball : ∀ y : Vec3, y ∉ Metric.closedBall (0 : Vec3) (‖x₀‖ + ρ) →
      y ∉ vec3Ball x₀ ρ := by
    intro y hy hyb
    apply hy
    have hyρ : vec3EuclideanNorm (y - x₀) < ρ := hyb
    have hsub : ‖y - x₀‖ ≤ vec3EuclideanNorm (y - x₀) := norm_le_vec3EuclideanNorm _
    have hadd : ‖y‖ ≤ ‖y - x₀‖ + ‖x₀‖ := by
      have h := norm_add_le (y - x₀) x₀
      have hyeq : (y - x₀) + x₀ = y := by abel
      rwa [hyeq] at h
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    linarith only [hyρ, hsub, hadd]
  -- The cut-off factors on the ball.
  have hmulball₇ : ∀ j : Fin 3, MemLp
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j) (ENNReal.ofReal q)
      (volume.restrict (vec3Ball x₀ ρ)) := fun j =>
    (hfj j).of_le (hηmeas.mul (hfj j).aestronglyMeasurable) (by
      filter_upwards with y
      change |mollifiedBallCutoff x₀ hρ y * f (y, s) j| ≤ ‖f (y, s) j‖
      rw [abs_mul, Real.norm_eq_abs]
      simpa only [Real.norm_eq_abs, one_mul] using
        (mul_le_mul_of_nonneg_right (hηbound y) (abs_nonneg (f (y, s) j))))
  have hmulball₈ : ∀ j : Fin 3, MemLp
      (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)
      (ENNReal.ofReal q) (volume.restrict (vec3Ball x₀ ρ)) := by
    intro j
    have hc : 0 ≤ cutoffGradientConstant / ρ :=
      (abs_nonneg (spatialDeriv (mollifiedBallCutoff x₀ hρ) j 0)).trans
        (pressure_cutoff_spatialDeriv_bound x₀ hρ 0 j)
    have hmeas : AEStronglyMeasurable (spatialDeriv (mollifiedBallCutoff x₀ hρ) j)
        (volume.restrict (vec3Ball x₀ ρ)) :=
      (contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth x₀ hρ) j).continuous
        |>.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    refine ((hfj j).const_mul (cutoffGradientConstant / ρ)).of_le
      (hmeas.mul (hfj j).aestronglyMeasurable) ?_
    filter_upwards with y
    change |spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j| ≤
      ‖(cutoffGradientConstant / ρ) * f (y, s) j‖
    rw [abs_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_right
      (pressure_cutoff_spatialDeriv_bound x₀ hρ y j) (abs_nonneg (f (y, s) j))
  -- Extend the memberships from the ball to all of `ℝ³`.
  have hdata₇ : ∀ j : Fin 3, MemLp
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
      (ENNReal.ofReal q) volume := fun j =>
    memLp_of_memLp_restrict_vec3Ball (hmulball₇ j)
      (fun y hy => by rw [hηzero y hy, zero_mul])
  have hdata₈ : ∀ j : Fin 3, MemLp
      (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)
      (ENNReal.ofReal q) volume := fun j =>
    memLp_of_memLp_restrict_vec3Ball (hmulball₈ j)
      (fun y hy => by rw [hηderivzero j y hy, zero_mul])
  have hsupp₇ : ∀ (j : Fin 3) (y : Vec3),
      y ∉ Metric.closedBall (0 : Vec3) (‖x₀‖ + ρ) →
      mollifiedBallCutoff x₀ hρ y * f (y, s) j = 0 :=
    fun j y hy => by rw [hηzero y (hnotball y hy), zero_mul]
  have hsupp₈ : ∀ (j : Fin 3) (y : Vec3),
      y ∉ Metric.closedBall (0 : Vec3) (‖x₀‖ + ρ) →
      spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j = 0 :=
    fun j y hy => by rw [hηderivzero j y (hnotball y hy), zero_mul]
  have hR : 0 < ‖x₀‖ + ρ := by positivity
  obtain ⟨hmem, hbound⟩ :=
    CKN.Foundation.Euclidean.pressureP7_add_pressureP8_memLp_and_lpNorm_growth
      (η := mollifiedBallCutoff x₀ hρ) (f := f) (s := s) (R := ‖x₀‖ + ρ) (q := q)
      hR hq hdata₇ hsupp₇ hdata₈ hsupp₈
  refine ⟨fun R hR' => hmem R hR', ?_, fun R hR' => ?_⟩
  · exact CKN.Foundation.Euclidean.pressureP7_add_pressureP8_growthConstant_nonneg
      (mollifiedBallCutoff x₀ hρ) f s hR
  · rw [czHarmonicForceGrowthConstant]
    exact hbound R hR'

end CKN
