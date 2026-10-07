/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCutoffBridge
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCutoffSupport
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianChangeBack
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianData
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianOperatorLocalized
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCarleman
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianParameters
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianInitialTrace
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianShellCaccioppoli
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianRadialMass
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianWeights
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEnergyL2
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortHeatL2
public import LeanPool.EscauriazaSereginSverak.Linear.UCTrace
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# The Gaussian average estimate for backward uniqueness

The cutoff equals the translated field on the normalized averaging box in
`lem:bu-gaussian`.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

theorem buGaussian_cutoff_field_eq_on_average_box
    {ρ ε : ℝ} (hρ : 4 < ρ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 12)
    (v : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (hz : z ∈ spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2 : ℝ) 1)) :
    ucCutoffScalar (ucSpatialCutoff ρ (by linarith only [hρ]))
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) z = 1 ∧
      buGaussianShiftedCutoffField ρ (by linarith only [hρ]) ε v z =
        buGaussianShiftedField (1 / 6) v z := by
  rcases hz with ⟨hy, hs⟩
  have hyNormMetric : ‖z.1‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hy
  have hyNorm : vec3EuclideanNorm z.1 < Real.sqrt 3 := by
    calc
      vec3EuclideanNorm z.1 ≤ Real.sqrt 3 * ‖z.1‖ :=
        vec3EuclideanNorm_le_sqrt_three_mul_norm _
      _ < Real.sqrt 3 := by
        have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
        calc
          Real.sqrt 3 * ‖z.1‖ < Real.sqrt 3 * 1 :=
            mul_lt_mul_of_pos_left hyNormMetric hsqrt
          _ = Real.sqrt 3 := by ring
  have hplateau : z.1 ∈ vec3Ball 0 (13 * ρ / 20) := by
    change vec3EuclideanNorm (z.1 - 0) < 13 * ρ / 20
    rw [sub_zero]
    have hsqrt : Real.sqrt 3 < 2 := by
      nlinarith only [Real.sqrt_nonneg (3 : ℝ),
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have hrad : Real.sqrt 3 < 13 * ρ / 20 := by nlinarith only [hρ, hsqrt]
    exact lt_trans hyNorm hrad
  have hqlo : (1 / 3 : ℝ) < z.2 - 1 / 6 := by linarith only [hs.1]
  have hqhi : z.2 - 1 / 6 < 3 / 2 := by linarith only [hs.2]
  have h2ε : 2 * ε ≤ 1 / 6 := by nlinarith only [hεsmall]
  have hθ : ucSpatialCutoff ρ (by linarith only [hρ]) z.1 = 1 :=
    buGaussian_spatial_cutoff_eq_one_on_plateau (by linarith only [hρ]) hplateau
  have hη : ucFinalTimeCutoff (z.2 - 1 / 6) = 1 :=
    ucFinalTimeCutoff_eq_one hqhi.le
  have hχ : ucInitialTimeCutoff ε (z.2 - 1 / 6) = 1 :=
    ucInitialTimeCutoff_eq_one hε (h2ε.trans (by linarith only [hqlo]))
  have hscalar : ucCutoffScalar (ucSpatialCutoff ρ (by linarith only [hρ]))
      (fun s => ucFinalTimeCutoff (s - 1 / 6))
      (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) z = 1 := by
    change ucSpatialCutoff ρ (by linarith only [hρ]) z.1 *
      ucFinalTimeCutoff (z.2 - 1 / 6) *
      ucInitialTimeCutoff ε (z.2 - 1 / 6) = 1
    rw [hθ, hη, hχ]
    ring
  refine ⟨hscalar, ?_⟩
  change ucCutoffScalar (ucSpatialCutoff ρ (by linarith only [hρ]))
      (fun s => ucFinalTimeCutoff (s - 1 / 6))
      (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) z • _ = _
  rw [hscalar]
  simp

theorem buGaussian_metric_average_physical_integrable
    (A : ℝ) (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtw : ParabolicPoint → Vec3)
    (hderiv : HasSpaceTimeWeakDerivs buHalfSpace (Ioo 0 1) w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint, S ⊆ buHalfCylinder → Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) +
        ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hgrowth : ∀ z ∈ buHalfCylinder,
      vec3EuclideanNorm (w z) ≤ Real.exp (A * vec3EuclideanNorm z.1 ^ 2))
    (x : Vec3) (scale t : ℝ) (hx₃ : 2 < x 2)
    (hscalele : scale ≤ 1) (ht : 0 < t) (httop : 5 * t / 2 < 1) :
    IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (Metric.ball x scale) (Ioo t (5 * t / 2))) volume := by
  let Q : Set ParabolicPoint :=
    spaceTimeSet (Metric.ball x scale) (Ioo t (5 * t / 2))
  have hQsub : Q ⊆ buHalfCylinder := by
    intro z hz
    rcases hz with ⟨hzx, hzt⟩
    have hdist : dist z.1 x < scale := by simpa only [Metric.mem_ball] using hzx
    have hcoord : |z.1 2 - x 2| ≤ dist z.1 x := by
      have h := norm_le_pi_norm (z.1 - x) (2 : Fin 3)
      simpa [dist_eq_norm, Real.norm_eq_abs] using h
    have hspace : 0 < z.1 2 := by
      have habs : |z.1 2 - x 2| < 1 := lt_of_le_of_lt hcoord
        (lt_of_lt_of_le hdist hscalele)
      have hlow := (abs_lt.mp habs).1
      linarith only [hx₃, hlow]
    change z ∈ spaceTimeSet buHalfSpace (Ioo 0 1)
    exact ⟨hspace, ⟨ht.trans hzt.1, hzt.2.trans httop⟩⟩
  have hQbounded : Bornology.IsBounded Q := by
    let Kprod : Set (Vec3 × ℝ) :=
      Metric.closedBall x scale ×ˢ Icc t (5 * t / 2)
    let K : Set ParabolicPoint := parabolicHomeomorph.symm '' Kprod
    have hKprod : IsCompact Kprod :=
      (isCompact_closedBall x scale).prod isCompact_Icc
    have hK : IsCompact K := parabolicHomeomorph.symm.isCompact_image.mpr hKprod
    have hQsubK : Q ⊆ K := by
      intro z hz
      rcases hz with ⟨hzx, hzt⟩
      refine ⟨(z.1, z.2), ⟨Metric.ball_subset_closedBall hzx,
        ⟨hzt.1.le, hzt.2.le⟩⟩, ?_⟩
      rw [← parabolicHomeomorph_apply]
      exact parabolicHomeomorph.left_inv z
    exact hK.isBounded.subset hQsubK
  have hlocal := buGaussian_local_quadratic_l2 A w Dw D2w Dtw
    hderiv hL2 hgrowth
  have hQL2 := hlocal Q hQsub hQbounded
  have hWfinite : (∫⁻ z in Q, ‖w z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hQL2
    intro z
    exact le_add_of_nonneg_right (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity)))
  exact uc_squared_norm_integrable_on_subset Q Q w
    (hderiv.1.mono_set hQsub) hWfinite Subset.rfl

theorem buGaussian_change_back_metric_average
    (x : Vec3) (scale : ℝ) (hscale : 0 < scale) (w : ParabolicPoint → Vec3)
    (hInt : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (Metric.ball x scale)
        (Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6))) volume) :
    (∫ z in spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2 : ℝ) 1),
      vec3EuclideanNorm
        (buGaussianAverageScaledField x scale (1 / 6) w z) ^ 2) =
      (scale ^ 5)⁻¹ *
        ∫ z in spaceTimeSet (Metric.ball x scale)
          (Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6)),
          vec3EuclideanNorm (w z) ^ 2 := by
  let Ω : Set Vec3 := Metric.ball x scale
  let I : Set ℝ := Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6)
  let shift : ℝ := -(scale ^ 2 / 6)
  let F : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (w z) ^ 2
  have hscaleSq : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hΩ : MeasurableSet Ω := (Metric.isOpen_ball).measurableSet
  have hI : MeasurableSet I := measurableSet_Ioo
  have hF : AEStronglyMeasurable F (volume.restrict (spaceTimeSet Ω I)) := by
    exact hInt.aestronglyMeasurable
  have hspace : rescaledSpace scale x Ω = Metric.ball 0 1 := by
    ext y
    change dist (x + scale • y) x < scale ↔ dist y 0 < 1
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(x + scale • y) - x‖ < scale ↔ ‖y - 0‖ < 1
    rw [add_sub_cancel_left, sub_zero, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos hscale]
    constructor
    · intro hy
      have hmul : scale * ‖y‖ < scale * 1 := by simpa using hy
      exact (mul_lt_mul_iff_of_pos_left hscale).mp hmul
    · intro hy
      have hmul := mul_lt_mul_of_pos_left hy hscale
      simpa using hmul
  have htime : rescaledTime scale (-(scale ^ 2 / 6)) I =
      Ioo (1 / 2) 1 := by
    ext s
    change shift + scale ^ 2 * s ∈ Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6) ↔
      s ∈ Ioo (1 / 2) 1
    simp only [mem_Ioo]
    constructor
    · rintro ⟨hslo, hshi⟩
      constructor
      · apply (mul_lt_mul_iff_of_pos_left hscaleSq).mp
        dsimp [shift] at hslo
        nlinarith only [hslo]
      · apply (mul_lt_mul_iff_of_pos_left hscaleSq).mp
        dsimp [shift] at hshi
        nlinarith only [hshi]
    · rintro ⟨hslo, hshi⟩
      constructor
      · dsimp [shift]
        nlinarith only [mul_lt_mul_of_pos_left hslo hscaleSq]
      · dsimp [shift]
        nlinarith only [mul_lt_mul_of_pos_left hshi hscaleSq]
  have hpre : spaceTimeSet (rescaledSpace scale x Ω)
      (rescaledTime scale (-(scale ^ 2 / 6)) I) =
      spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2) 1) := by
    rw [hspace, htime]
  have hpoint : scalingParabolic scale (x, shift) =
      fun z => buGaussianScaledPoint x scale (1 / 6) z := by
    funext z
    change (x + scale • z.1, shift + scale ^ 2 * z.2) =
      (x + scale • z.1, scale ^ 2 * (z.2 - 1 / 6))
    dsimp [shift]
    congr 1
    ring
  have hchange := CKN.integral_comp_scaling_test scale hscale (x, shift)
    (Ω := Ω) (I := I) (F := F) hΩ hI hF
  have hcoef : (ENNReal.ofReal (scale⁻¹ ^ 5)).toReal = (scale ^ 5)⁻¹ := by
    rw [ENNReal.toReal_ofReal (by positivity), inv_pow]
  rw [hpre, hpoint, hcoef, smul_eq_mul] at hchange
  dsimp [F] at hchange
  simpa [buGaussianAverageScaledField, Ω, I] using hchange

theorem buGaussian_shifted_scalar_derivatives
    {ρ ε : ℝ} (hρ : 0 < ρ) (z : ParabolicPoint) (j k : Fin 3) :
    spatialPartial
        (ucCutoffScalar (ucSpatialCutoff ρ hρ)
          (fun s => ucFinalTimeCutoff (s - 1 / 6))
          (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) j z =
      spatialPartial (ucGaussianCutoff ρ hρ ε) j
        (buGaussianTimeShiftPoint (-1 / 6) z) ∧
    spatialSecondPartial
        (ucCutoffScalar (ucSpatialCutoff ρ hρ)
          (fun s => ucFinalTimeCutoff (s - 1 / 6))
          (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) j k z =
      spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j k
        (buGaussianTimeShiftPoint (-1 / 6) z) ∧
    timePartial
        (ucCutoffScalar (ucSpatialCutoff ρ hρ)
          (fun s => ucFinalTimeCutoff (s - 1 / 6))
          (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) z =
    timePartial (ucGaussianCutoff ρ hρ ε)
        (buGaussianTimeShiftPoint (-1 / 6) z) := by
  let ψ : Vec3 × ℝ → ℝ := fun q => ucGaussianCutoff ρ hρ ε q
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ] using ucGaussianCutoff_smooth ρ hρ ε
  have hscalar : (fun q : ParabolicPoint =>
      ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) q) =
      (fun q : ParabolicPoint =>
        ucGaussianCutoff ρ hρ ε (q.1, (-1 / 6) + q.2)) := by
    funext q
    simp only [ucCutoffScalar, ucGaussianCutoff]
    have ht : q.2 - 1 / 6 = (-1 / 6) + q.2 := by ring
    rw [ht]
  have hfirst := buGaussian_timeShift_test_derivatives (-1 / 6) hψ z j
  change spatialPartial
      (fun q : ParabolicPoint =>
        ucGaussianCutoff ρ hρ ε (q.1, (-1 / 6) + q.2)) j z =
      spatialPartial ψ j (buGaussianTimeShiftPoint (-1 / 6) z) ∧
      timePartial
        (fun q : ParabolicPoint =>
          ucGaussianCutoff ρ hρ ε (q.1, (-1 / 6) + q.2)) z =
      timePartial ψ (buGaussianTimeShiftPoint (-1 / 6) z) at hfirst
  have hfirst' : spatialPartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) j z =
      spatialPartial (ucGaussianCutoff ρ hρ ε) j
        (buGaussianTimeShiftPoint (-1 / 6) z) := by
    calc
      _ = spatialPartial
          (fun q : ParabolicPoint =>
            ucGaussianCutoff ρ hρ ε (q.1, (-1 / 6) + q.2)) j z := by
          exact congrArg (fun f : ParabolicPoint → ℝ => spatialPartial f j z) hscalar
      _ = spatialPartial (ucGaussianCutoff ρ hρ ε) j
          (buGaussianTimeShiftPoint (-1 / 6) z) := by
          simpa [ψ] using hfirst.1
  have htime' : timePartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) z =
      timePartial (ucGaussianCutoff ρ hρ ε)
        (buGaussianTimeShiftPoint (-1 / 6) z) := by
    calc
      _ = timePartial
          (fun q : ParabolicPoint =>
            ucGaussianCutoff ρ hρ ε (q.1, (-1 / 6) + q.2)) z := by
          exact congrArg (fun f : ParabolicPoint → ℝ => timePartial f z) hscalar
      _ = timePartial (ucGaussianCutoff ρ hρ ε)
          (buGaussianTimeShiftPoint (-1 / 6) z) := by
          simpa [ψ] using hfirst.2
  have hfun : (fun y : Vec3 => spatialPartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) j (y, z.2)) =
      (fun y : Vec3 => spatialPartial (ucGaussianCutoff ρ hρ ε) j
        (buGaussianTimeShiftPoint (-1 / 6) (y, z.2))) := by
    funext y
    have h := buGaussian_timeShift_test_derivatives (-1 / 6) hψ (y, z.2) j
    change spatialPartial
        (fun q : ParabolicPoint =>
          ucGaussianCutoff ρ hρ ε (q.1, (-1 / 6) + q.2)) j (y, z.2) =
        spatialPartial ψ j (buGaussianTimeShiftPoint (-1 / 6) (y, z.2)) ∧
      timePartial
        (fun q : ParabolicPoint =>
          ucGaussianCutoff ρ hρ ε (q.1, (-1 / 6) + q.2)) (y, z.2) =
        timePartial ψ (buGaussianTimeShiftPoint (-1 / 6) (y, z.2)) at h
    calc
      _ = spatialPartial
          (fun q : ParabolicPoint =>
            ucGaussianCutoff ρ hρ ε (q.1, (-1 / 6) + q.2)) j (y, z.2) := by
          exact congrArg
            (fun f : ParabolicPoint → ℝ => spatialPartial f j (y, z.2)) hscalar
      _ = spatialPartial (ucGaussianCutoff ρ hρ ε) j
          (buGaussianTimeShiftPoint (-1 / 6) (y, z.2)) := by
          simpa [ψ] using h.1
  have hsecond : spatialSecondPartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) j k z =
      spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j k
        (buGaussianTimeShiftPoint (-1 / 6) z) := by
    rw [show spatialSecondPartial
        (ucCutoffScalar (ucSpatialCutoff ρ hρ)
          (fun s => ucFinalTimeCutoff (s - 1 / 6))
          (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) j k z =
        (fderiv ℝ (fun y : Vec3 => spatialPartial
          (ucCutoffScalar (ucSpatialCutoff ρ hρ)
            (fun s => ucFinalTimeCutoff (s - 1 / 6))
            (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) j (y, z.2)) z.1)
          (basisVec k) by rfl]
    rw [hfun]
    rfl
  exact ⟨hfirst', hsecond, htime'⟩

theorem buGaussian_average_time_weight_le_one {s : ℝ}
    (hs : s ∈ Icc (1 / 2 : ℝ) 1) :
    gaussCarlemanTimeWeight s ≤ 1 := by
  have hspos : 0 < s := by linarith only [hs.1]
  have hweightPos : 0 < gaussCarlemanTimeWeight s := by
    unfold gaussCarlemanTimeWeight
    positivity
  have hlog : Real.log (gaussCarlemanTimeWeight s) ≤ 0 := by
    rw [gaussCarlemanTimeWeight, Real.log_mul hspos.ne' (Real.exp_ne_zero _),
      Real.log_exp]
    calc
      Real.log s + (1 - s) / 3 ≤ (s - 1) + (1 - s) / 3 :=
        add_le_add_left (Real.log_le_sub_one_of_pos hspos) _
      _ ≤ 0 := by nlinarith only [hs.2]
  have hle := (Real.log_le_iff_le_exp hweightPos).mp hlog
  simpa using hle

theorem buGaussian_carleman_mass_density_lower
    {a ρ ε : ℝ} (hρ : 4 < ρ) (ha : 1 ≤ a) (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 12) (v : ParabolicPoint → Vec3)
    (z : ParabolicPoint)
    (hz : z ∈ spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2 : ℝ) 1)) :
    Real.exp (-(3 / 2 : ℝ)) *
        vec3EuclideanNorm (buGaussianShiftedField (1 / 6) v z) ^ 2 ≤
      ucGaussianWeight a z * (a / z.2) *
        vec3EuclideanNorm (buGaussianShiftedCutoffField ρ
          (by linarith only [hρ]) ε v z) ^ 2 := by
  have hs : z.2 ∈ Ioo (1 / 2 : ℝ) 1 := hz.2
  have hspos : 0 < z.2 := by linarith only [hs.1]
  have htimeWeight := buGaussian_average_time_weight_le_one
    ⟨hs.1.le, hs.2.le⟩
  have htimePos : 0 < gaussCarlemanTimeWeight z.2 := by
    unfold gaussCarlemanTimeWeight
    positivity
  have hpow : 1 ≤ gaussCarlemanTimeWeight z.2 ^ (-2 * a) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos htimePos htimeWeight
      (by nlinarith only [ha])
  have hnormY : vec3EuclideanNorm z.1 < Real.sqrt 3 := by
    have hm : ‖z.1‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hz.1
    calc
      vec3EuclideanNorm z.1 ≤ Real.sqrt 3 * ‖z.1‖ :=
        vec3EuclideanNorm_le_sqrt_three_mul_norm _
      _ < Real.sqrt 3 := by
        have hroot : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
        calc
          Real.sqrt 3 * ‖z.1‖ < Real.sqrt 3 * 1 := mul_lt_mul_of_pos_left hm hroot
          _ = Real.sqrt 3 := by ring
  have hY : vec3EuclideanNorm z.1 ^ 2 ≤ 3 := by
    have hy0 : 0 ≤ vec3EuclideanNorm z.1 := vec3EuclideanNorm_nonneg _
    have hsq : vec3EuclideanNorm z.1 ^ 2 < (Real.sqrt 3) ^ 2 :=
      (sq_lt_sq₀ hy0 (Real.sqrt_nonneg _)).2 hnormY
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hsq
    exact hsq.le
  have hexp : Real.exp (-(3 / 2 : ℝ)) ≤
      Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) := by
    apply Real.exp_le_exp.mpr
    have hden : 2 ≤ 4 * z.2 := by nlinarith only [hs.1]
    have hfrac : vec3EuclideanNorm z.1 ^ 2 / (4 * z.2) ≤ 3 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * z.2)).2
      nlinarith only [hY, hden]
    calc
      -(3 / 2 : ℝ) ≤ -(vec3EuclideanNorm z.1 ^ 2 / (4 * z.2)) := neg_le_neg hfrac
      _ = -(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2) := by ring
  have hcoef : 1 ≤ a / z.2 := by
    exact (le_div_iff₀ hspos).2 (by nlinarith only [ha, hs.2])
  have hcut := (buGaussian_cutoff_field_eq_on_average_box
    hρ hε hεsmall v z hz).2
  rw [hcut]
  unfold ucGaussianWeight
  have hnormSq : 0 ≤ vec3EuclideanNorm (buGaussianShiftedField (1 / 6) v z) ^ 2 :=
    sq_nonneg _
  calc
    Real.exp (-(3 / 2 : ℝ)) *
        vec3EuclideanNorm (buGaussianShiftedField (1 / 6) v z) ^ 2 ≤
      (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
        vec3EuclideanNorm (buGaussianShiftedField (1 / 6) v z) ^ 2 := by
      have hprod : Real.exp (-(3 / 2 : ℝ)) ≤
          gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
            Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) := by
        calc
          Real.exp (-(3 / 2 : ℝ)) ≤
              Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) := hexp
          _ = 1 * Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_right hprod hnormSq
    _ ≤ (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
        ((a / z.2) *
          vec3EuclideanNorm (buGaussianShiftedField (1 / 6) v z) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hnormSq
    _ = (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
        (a / z.2) * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) v z) ^ 2 := by
      ring

theorem buGaussian_shifted_cutoff_heat_eq_raw
    {ρ ε : ℝ} (hρ : 0 < ρ) (z : ParabolicPoint)
    (v : ParabolicPoint → Vec3) (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) :
    ucCutoffHeat (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))
        (buGaussianShiftedField (1 / 6) v)
        (buGaussianShiftedDw (1 / 6) Dv)
        (buGaussianShiftedD2w (1 / 6) D2v)
        (buGaussianShiftedDtw (1 / 6) Dtv) z =
      ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv
        ((buGaussianTimeShiftPoint (1 / 6)).symm z) := by
  let T := buGaussianTimeShiftPoint (1 / 6)
  let q := T.symm z
  have hqcoord : q = (z.1, z.2 - 1 / 6) := by
    dsimp [q, T]
    exact buGaussian_timeShift_point_symm_apply (1 / 6) z
  have hqshift : buGaussianTimeShiftPoint (-1 / 6) z = q := by
    rw [show (-1 / 6 : ℝ) = -(1 / 6 : ℝ) by norm_num]
    rw [← buGaussian_timeShift_inverse (1 / 6)]
  have hscalar : ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) z =
      ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) q := by
    change ucSpatialCutoff ρ hρ z.1 * ucFinalTimeCutoff (z.2 - 1 / 6) *
        ucInitialTimeCutoff ε (z.2 - 1 / 6) =
      ucSpatialCutoff ρ hρ q.1 * ucFinalTimeCutoff q.2 *
        ucInitialTimeCutoff ε q.2
    rw [hqcoord]
  have hpartial (j : Fin 3) :
      spatialPartial (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) j z =
      spatialPartial (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        ucFinalTimeCutoff (ucInitialTimeCutoff ε)) j q := by
    have hj := (buGaussian_shifted_scalar_derivatives
      (ρ := ρ) (ε := ε) hρ z j (0 : Fin 3)).1
    rw [hqshift] at hj
    simpa only [ucGaussianCutoff] using hj
  have hpartial2 (j k : Fin 3) :
      spatialSecondPartial (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) j k z =
      spatialSecondPartial (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        ucFinalTimeCutoff (ucInitialTimeCutoff ε)) j k q := by
    have hjk := (buGaussian_shifted_scalar_derivatives
      (ρ := ρ) (ε := ε) hρ z j k).2.1
    rw [hqshift] at hjk
    simpa only [ucGaussianCutoff] using hjk
  have htime : timePartial (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) z =
      timePartial (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        ucFinalTimeCutoff (ucInitialTimeCutoff ε)) q := by
    have ht := (buGaussian_shifted_scalar_derivatives (ρ := ρ) (ε := ε) hρ z
      (0 : Fin 3) (0 : Fin 3)).2.2
    rw [hqshift] at ht
    simpa only [ucGaussianCutoff] using ht
  have hv : buGaussianShiftedField (1 / 6) v z = v q := rfl
  have hDv : buGaussianShiftedDw (1 / 6) Dv z = Dv q := rfl
  have hsourceHeat : ucWeakHeatVector
      (buGaussianShiftedD2w (1 / 6) D2v)
      (buGaussianShiftedDtw (1 / 6) Dtv) z =
      ucWeakHeatVector D2v Dtv q := by
    funext i
    simp [ucWeakHeatVector, buGaussianShiftedD2w,
      buGaussianShiftedDtw, q, T]
  have hraw : ucCutoffHeat (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))
        (buGaussianShiftedField (1 / 6) v)
        (buGaussianShiftedDw (1 / 6) Dv)
        (buGaussianShiftedD2w (1 / 6) D2v)
        (buGaussianShiftedDtw (1 / 6) Dtv) z =
      ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv q := by
    funext i
    simp only [ucCutoffHeat]
    rw [hscalar, htime]
    simp_rw [hpartial, hpartial2]
    rw [hv, hDv, hsourceHeat]
  simpa [T, q] using hraw

theorem buGaussian_shifted_cutoff_field_dw_eq_raw
    {ρ ε : ℝ} (hρ : 0 < ρ) (z : ParabolicPoint)
    (v : ParabolicPoint → Vec3) (Dv : ParabolicPoint → Fin 3 → Vec3) :
    buGaussianShiftedCutoffField ρ hρ ε v z =
        ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v ((buGaussianTimeShiftPoint (1 / 6)).symm z) ∧
      buGaussianShiftedCutoffDw ρ hρ ε v Dv z =
        ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dv ((buGaussianTimeShiftPoint (1 / 6)).symm z) := by
  let T := buGaussianTimeShiftPoint (1 / 6)
  let q := T.symm z
  have hqcoord : q = (z.1, z.2 - 1 / 6) := by
    dsimp [q, T]
    exact buGaussian_timeShift_point_symm_apply (1 / 6) z
  have hscalar : ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) z =
      ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) q := by
    change ucSpatialCutoff ρ hρ z.1 * ucFinalTimeCutoff (z.2 - 1 / 6) *
        ucInitialTimeCutoff ε (z.2 - 1 / 6) =
      ucSpatialCutoff ρ hρ q.1 * ucFinalTimeCutoff q.2 *
        ucInitialTimeCutoff ε q.2
    rw [hqcoord]
  have hpartial (j : Fin 3) :
      spatialPartial (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))) j z =
      spatialPartial (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        ucFinalTimeCutoff (ucInitialTimeCutoff ε)) j q := by
    have hj := (buGaussian_shifted_scalar_derivatives
      (ρ := ρ) (ε := ε) hρ z j (0 : Fin 3)).1
    have hqshift : buGaussianTimeShiftPoint (-1 / 6) z = q := by
      rw [show (-1 / 6 : ℝ) = -(1 / 6 : ℝ) by norm_num,
        ← buGaussian_timeShift_inverse (1 / 6)]
    rw [hqshift] at hj
    simpa only [ucGaussianCutoff] using hj
  constructor
  · change ucCutoffField (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))
        (buGaussianShiftedField (1 / 6) v) z = _
    rw [ucCutoffField, hscalar]
    rfl
  · change ucCutoffDw (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6))
        (buGaussianShiftedField (1 / 6) v)
        (buGaussianShiftedDw (1 / 6) Dv) z = _
    funext i j
    simp only [ucCutoffDw]
    rw [hscalar, hpartial j]
    rfl

theorem buGaussian_shifted_operator_localized_ae_bound
    {ρ ε c₁ scale : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hεsmall : 2 * ε ≤ 1 / 2) (hc₁ : 0 ≤ c₁) (hscale : 0 ≤ scale)
    (v : ParabolicPoint → Vec3) (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3)
    (hineq : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c₁ * scale * (vec3EuclideanNorm (v z) +
          Real.sqrt (spatialGradientSq v Dv z))) :
    ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))),
      vec3EuclideanNorm (ucWeakHeatVector
        (buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v)
        (buGaussianShiftedCutoffDtw ρ hρ ε v Dtv) z) ≤
      c₁ * scale *
          (vec3EuclideanNorm (buGaussianShiftedCutoffField ρ hρ ε
              v z) +
            3 * Real.sqrt (spatialGradientSq
              (buGaussianShiftedCutoffField ρ hρ ε v)
              (buGaussianShiftedCutoffDw ρ hρ ε v Dv) z)) +
        (if z.1 ∈ {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
            vec3EuclideanNorm y ≤ 3 * ρ / 4} then
          (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
            3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
              vec3EuclideanNorm (buGaussianShiftedField (1 / 6) v z) +
          18 * (cutoffGradientConstant / ρ) * Real.sqrt
            (spatialGradientSq (buGaussianShiftedField (1 / 6) v)
              (buGaussianShiftedDw (1 / 6) Dv) z) else 0) +
        (if 3 / 2 ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
            ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 7 / 4 then
          32 * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) v z) else 0) +
        (if ε ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
            ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 2 * ε then
          (8 / ε) * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) v z) else 0) := by
  let σ : ℝ := 1 / 6
  let B : Set Vec3 := vec3Ball 0 ρ
  let S₀ : Set ParabolicPoint := spaceTimeSet B (Ioo 0 (2 - σ))
  let S₁ : Set ParabolicPoint := spaceTimeSet B (Ioo σ 2)
  let T := buGaussianTimeShiftPoint σ
  have hS₀sub : S₀ ⊆ ucCylinder ρ := by
    intro q hq
    exact ⟨hq.1, hq.2.1, lt_of_lt_of_le hq.2.2 (by norm_num [S₀, σ])⟩
  have hS₁meas : MeasurableSet S₁ := by
    exact (vec3Ball_measurable 0 ρ).prod measurableSet_Ioo
  have hraw := buGaussian_cutoff_operator_localized_ae_bound
    hρ hε hεsmall hc₁ hscale v Dv D2v Dtv hineq
  have hraw₀ : ∀ᵐ q ∂(volume.restrict S₀),
      q ∈ ucCylinder ρ →
        vec3EuclideanNorm (ucCutoffHeat (ucSpatialCutoff ρ hρ)
          ucFinalTimeCutoff (ucInitialTimeCutoff ε) v Dv D2v Dtv q) ≤ _ :=
    ae_mono (Measure.restrict_mono hS₀sub le_rfl) hraw
  have hshift := buGaussian_timeShift_ae hraw₀
  filter_upwards [hshift, ae_restrict_mem hS₁meas] with z hzbound hzmem
  let q : ParabolicPoint := T.symm z
  have hqcoord : q.2 = z.2 - σ := by
    dsimp [q, T]
    rw [buGaussian_timeShift_point_symm_apply]
  have hqmem : q ∈ ucCylinder ρ := by
    have hσ : σ = (1 / 6 : ℝ) := rfl
    refine ⟨hzmem.1, ?_, ?_⟩
    · rw [hqcoord, hσ]
      linarith only [hzmem.2.1]
    · rw [hqcoord]
      rw [hσ]
      linarith only [hzmem.2.2]
  have hrawbound := hzbound hqmem
  have hrawbound' := hrawbound
  change vec3EuclideanNorm (ucCutoffHeat (ucSpatialCutoff ρ hρ)
    ucFinalTimeCutoff (ucInitialTimeCutoff ε) v Dv D2v Dtv q) ≤ _ at hrawbound'
  have hfielddw := buGaussian_shifted_cutoff_field_dw_eq_raw
    (ρ := ρ) (ε := ε) hρ z v Dv
  have hcutgrad : spatialGradientSq
        (buGaussianShiftedCutoffField ρ hρ ε v)
        (buGaussianShiftedCutoffDw ρ hρ ε v Dv) z =
      spatialGradientSq
        (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v)
        (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dv) q := by
    unfold spatialGradientSq
    rw [hfielddw.2]
  have hheat : ucWeakHeatVector
      (buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v)
      (buGaussianShiftedCutoffDtw ρ hρ ε v Dtv) z =
      ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv q := by
    calc
      _ = ucCutoffHeat (ucSpatialCutoff ρ hρ)
          (fun s => ucFinalTimeCutoff (s - 1 / 6))
          (fun s => ucInitialTimeCutoff ε (s - 1 / 6))
          (buGaussianShiftedField (1 / 6) v)
          (buGaussianShiftedDw (1 / 6) Dv)
          (buGaussianShiftedD2w (1 / 6) D2v)
          (buGaussianShiftedDtw (1 / 6) Dtv) z := by
            symm
            exact ucCutoffHeat_eq_weakHeat _ _ _ _ _ _ _ z
      _ = ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dv D2v Dtv q := by
            exact buGaussian_shifted_cutoff_heat_eq_raw
              (ρ := ρ) (ε := ε) hρ z v Dv D2v Dtv
  have hheatnorm : vec3EuclideanNorm (ucWeakHeatVector
      (buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v)
      (buGaussianShiftedCutoffDtw ρ hρ ε v Dtv) z) =
      vec3EuclideanNorm (ucCutoffHeat (ucSpatialCutoff ρ hρ)
        ucFinalTimeCutoff (ucInitialTimeCutoff ε) v Dv D2v Dtv q) :=
    congrArg vec3EuclideanNorm hheat
  have hraw' := hrawbound'
  rw [← hheatnorm, ← hfielddw.1, ← hcutgrad] at hraw'
  simpa [σ, B, S₀, S₁, T, q,
    buGaussian_timeShift_point_symm_apply,
    buGaussianShiftedField, buGaussianShiftedDw, spatialGradientSq] using hraw'

end ESS
