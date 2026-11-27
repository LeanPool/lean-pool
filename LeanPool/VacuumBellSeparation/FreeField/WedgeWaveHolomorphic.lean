/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeWaveContinuity
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Genuine Hilbert-space holomorphy inside the wedge strip

The extension by zero is only a device for using the ordinary derivative on an
open neighborhood. On the closed strip it is exactly the physical wave. Cauchy's
scalar estimate and the original square-integrable slab bound dominate the
actual difference quotients in the original mass-shell Hilbert space.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology

/-- The rapidity strip with imaginary part strictly between zero and π. -/
def openRapidityStrip : Set ℂ := {ζ | 0 < ζ.im ∧ ζ.im < Real.pi}

/-- Wedge wave extended L². -/
noncomputable def wedgeWaveExtendedL2 {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) (ζ : ℂ) : Lp ℂ 2 (oneParticleMeasure m) := by
  classical
  exact if hζ : ζ ∈ closedRapidityStrip then wedgeWaveL2 hm F hF ζ hζ else 0

/-- Wedge wave extended. -/
noncomputable def wedgeWaveExtended (m : ℝ) (F : RealTestFunction) (ζ : ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ := by
  classical
  exact if ζ ∈ closedRapidityStrip then wedgeWave m F ζ p else 0

theorem wedgeWaveExtendedL2_ae {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) (ζ : ℂ) :
    wedgeWaveExtendedL2 hm F hF ζ =ᵐ[oneParticleMeasure m] wedgeWaveExtended m F ζ := by
  classical
  by_cases hζ : ζ ∈ closedRapidityStrip
  · have he : wedgeWaveExtended m F ζ = wedgeWave m F ζ := by
      funext p
      simp only [wedgeWaveExtended, ite_eq_left hζ]
    rw [he]
    simpa only [wedgeWaveExtendedL2, dite_eq_left hζ] using wedgeWaveL2_ae hm F hF ζ hζ
  · have he : wedgeWaveExtended m F ζ = 0 := by
      funext p
      simp only [wedgeWaveExtended, ite_eq_right hζ, Pi.zero_apply]
    rw [he]
    simpa only [wedgeWaveExtendedL2, dite_eq_right hζ] using
      (Lp.coeFn_zero ℂ 2 (oneParticleMeasure m))

/-- Wedge wave derivative given by `∫ x : Spacetime, wedgeWavePhaseDerivative m p ζ x * (F.1 x :
ℂ)`. -/
noncomputable def wedgeWaveDerivative (m : ℝ) (F : RealTestFunction) (ζ : ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∫ x : Spacetime, wedgeWavePhaseDerivative m p ζ x * (F.1 x : ℂ)

theorem continuous_wedgeWaveDerivative_momentum (m : ℝ) (F : RealTestFunction) (ζ : ℂ) :
    Continuous (wedgeWaveDerivative m F ζ) := by
  have hc : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × Spacetime =>
      wedgeWavePhaseDerivative m q.1 ζ q.2 * (F.1 q.2 : ℂ)) := by
    unfold wedgeWavePhaseDerivative
    exact ((Complex.continuous_exp.comp (continuous_const.mul
      (continuous_boostPhase_comp m (-ζ) continuous_fst continuous_snd))).mul
      ((continuous_const.mul (continuous_boostPhaseDeriv_comp m (-ζ)
        continuous_fst continuous_snd)).neg)).mul
      (Complex.continuous_ofReal.comp ((continuous_testFunction F).comp continuous_snd))
  apply continuousOn_univ.mp
  exact continuousOn_integral_of_compact_support F.2.2 hc.continuousOn
    (fun p x _ hx => by simp only [image_eq_zero_of_notMem_tsupport hx,
      Complex.ofReal_zero, mul_zero])

theorem norm_wedgeWaveDerivative_disk_le {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) {ζ₀ : ℂ} {r B : ℝ} (hr : 0 < r)
    (hs : Metric.closedBall ζ₀ (3 * r) ⊆ closedRapidityStrip)
    (hB : ∀ ζ ∈ Metric.closedBall ζ₀ (3 * r), |ζ.re| ≤ B)
    {ζ : ℂ} (hζ : ζ ∈ Metric.ball ζ₀ r) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖wedgeWaveDerivative m F ζ p‖ ≤
      ((2 * Real.exp B / dispersion m p) ^ 2 * maxCoordDerivNorm F 2) / r := by
  have hd : Differentiable ℂ (fun z => wedgeWave m F z p) :=
    fun z => (hasDerivAt_wedgeWave m F p z).differentiableAt
  unfold wedgeWaveDerivative
  rw [← (hasDerivAt_wedgeWave m F p ζ).deriv]
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd.diffContOnCl
  intro z hz
  have hz₀ : z ∈ Metric.closedBall ζ₀ (3 * r) := by
    have h₁ := Metric.mem_sphere.mp hz
    have h₂ := Metric.mem_ball.mp hζ
    have h₃ := dist_triangle z ζ ζ₀
    rw [Metric.mem_closedBall]
    linarith
  exact norm_wedgeWave_closedStrip_le hm F hF (hs hz₀) (hB z hz₀) p

/-- A local disk estimate supplies the actual mass-shell Hilbert derivative. -/
theorem hasDerivAt_wedgeWaveExtendedL2_on_disk {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ leftWedge 0)
    {ζ₀ : ℂ} {r B : ℝ} (hr : 0 < r)
    (hs : Metric.closedBall ζ₀ (3 * r) ⊆ closedRapidityStrip)
    (hB : ∀ ζ ∈ Metric.closedBall ζ₀ (3 * r), |ζ.re| ≤ B) :
    ∃ g : Lp ℂ 2 (oneParticleMeasure m),
      g =ᵐ[oneParticleMeasure m] wedgeWaveDerivative m F ζ₀ ∧
      HasDerivAt (wedgeWaveExtendedL2 hm F hF) g ζ₀ := by
  classical
  let A (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
    (2 * Real.exp B / dispersion m p) ^ 2 * maxCoordDerivNorm F 2
  have hz₀ : ζ₀ ∈ Metric.ball ζ₀ r := Metric.mem_ball_self hr
  have hsmall : Metric.ball ζ₀ r ⊆ closedRapidityStrip := by
    intro z hz
    apply hs
    rw [Metric.mem_closedBall]
    have := Metric.mem_ball.mp hz
    linarith
  have hd (z : ℂ) (hz : z ∈ Metric.ball ζ₀ r) (p : EuclideanSpace ℝ (Fin 3)) :
      ‖wedgeWaveDerivative m F z p‖ ≤ A p / r :=
    norm_wedgeWaveDerivative_disk_le hm F hF hr hs hB hz p
  let C (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
    (16 * Real.exp B ^ 4 * maxCoordDerivNorm F 2 ^ 2 / r ^ 2) *
      (dispersion m p ^ 4)⁻¹
  have hC : Integrable C (oneParticleMeasure m) :=
    (integrable_inv_dispersion_pow_four_massShell hm).const_mul _
  have hD : MemLp (wedgeWaveDerivative m F ζ₀) 2 (oneParticleMeasure m) := by
    have hc := continuous_wedgeWaveDerivative_momentum m F ζ₀
    rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
    apply hC.mono' (hc.norm.pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc
        ‖wedgeWaveDerivative m F ζ₀ p‖ ^ 2 ≤ (A p / r) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hd ζ₀ hz₀ p) 2
        _ = C p := by dsimp [A, C]; ring
  refine ⟨hD.toLp (wedgeWaveDerivative m F ζ₀), hD.coeFn_toLp, ?_⟩
  apply hasDerivAt_L2_of_dominated_representatives (oneParticleMeasure m) _
    (wedgeWaveExtended m F) (wedgeWaveExtendedL2_ae hm F hF) _
    (wedgeWaveDerivative m F ζ₀) hD.coeFn_toLp ζ₀
    (bound := fun p => 4 * C p)
  · exact Eventually.of_forall fun p =>
      (hasDerivAt_wedgeWave m F p ζ₀).congr_of_eventuallyEq
        (Filter.Eventually.mono (Metric.ball_mem_nhds ζ₀ hr) fun z hz => by
          simp only [wedgeWaveExtended, ite_eq_left (hsmall hz)])
  · exact hC.const_mul 4
  · filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds ζ₀ hr)] with z hne hz
    have hzneq : z ≠ ζ₀ := hne
    exact Eventually.of_forall fun p => by
      have hslope : ‖(z - ζ₀)⁻¹ • (wedgeWave m F z p - wedgeWave m F ζ₀ p)‖ ≤ A p / r := by
        have hdiff : ‖wedgeWave m F z p - wedgeWave m F ζ₀ p‖ ≤ A p / r * ‖z - ζ₀‖ := by
          apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
            (fun w _ => (hasDerivAt_wedgeWave m F p w).hasDerivWithinAt)
            (fun w hw => hd w hw p) (convex_ball ζ₀ r) hz₀ hz
        rw [norm_smul, norm_inv]
        calc
          ‖z - ζ₀‖⁻¹ * ‖wedgeWave m F z p - wedgeWave m F ζ₀ p‖ ≤
              ‖z - ζ₀‖⁻¹ * (A p / r * ‖z - ζ₀‖) :=
            mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr (norm_nonneg _))
          _ = A p / r := by
            field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzneq)]
      simp only [wedgeWaveExtended, ite_eq_left (hsmall hz), ite_eq_left (hsmall hz₀)]
      have hres : ‖(z - ζ₀)⁻¹ • (wedgeWave m F z p - wedgeWave m F ζ₀ p) -
          wedgeWaveDerivative m F ζ₀ p‖ ≤ 2 * (A p / r) :=
        (norm_sub_le _ _).trans (by linarith [hd ζ₀ hz₀ p])
      calc
        _ ≤ (2 * (A p / r)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hres 2
        _ = 4 * C p := by dsimp [A, C]; ring

theorem differentiableOn_wedgeWaveExtendedL2 {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ leftWedge 0) :
    DifferentiableOn ℂ (wedgeWaveExtendedL2 hm F hF) openRapidityStrip := by
  intro ζ₀ hζ₀
  let r : ℝ := min ζ₀.im (Real.pi - ζ₀.im) / 4
  have hr : 0 < r := div_pos (lt_min hζ₀.1 (sub_pos.mpr hζ₀.2)) (by norm_num)
  have hlow : 3 * r ≤ ζ₀.im := by
    have h := min_le_left ζ₀.im (Real.pi - ζ₀.im)
    dsimp [r]; linarith [hζ₀.1]
  have hupp : ζ₀.im + 3 * r ≤ Real.pi := by
    have h := min_le_right ζ₀.im (Real.pi - ζ₀.im)
    dsimp [r]; linarith [hζ₀.2]
  have hs : Metric.closedBall ζ₀ (3 * r) ⊆ closedRapidityStrip := by
    intro z hz
    have hi := Complex.abs_im_le_norm (z - ζ₀)
    simp only [Complex.sub_im] at hi
    have hn : ‖z - ζ₀‖ ≤ 3 * r := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
    have hlo := (abs_le.mp (hi.trans hn)).1
    have hup := (abs_le.mp (hi.trans hn)).2
    exact ⟨by linarith, by linarith⟩
  have hB : ∀ z ∈ Metric.closedBall ζ₀ (3 * r), |z.re| ≤ |ζ₀.re| + 3 * r := by
    intro z hz
    have hi := Complex.abs_re_le_norm (z - ζ₀)
    simp only [Complex.sub_re] at hi
    have hn : ‖z - ζ₀‖ ≤ 3 * r := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
    calc
      |z.re| = |(z.re - ζ₀.re) + ζ₀.re| := by rw [sub_add_cancel]
      _ ≤ |z.re - ζ₀.re| + |ζ₀.re| := abs_add_le _ _
      _ ≤ _ := by linarith
  obtain ⟨g, _, hg⟩ := hasDerivAt_wedgeWaveExtendedL2_on_disk hm F hF hr hs hB
  exact hg.differentiableAt.differentiableWithinAt

end VacuumBellSeparation
