/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupMeasure
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ForceSlotNumericalScaling

/-!
# Critical energy under blow-up scaling

The open-top energy on the unit past cylinder is the normalized energy at the
original point and radius (`prop:blowup-limit`).
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Scaling maps the open unit past cylinder to the open past cylinder at the
original point. -/
theorem blowupOpenPast_image_subset
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    ∀ z ∈ goodPointPastCylinder 0 0 1,
      parabolicTranslate x₀ t₀ (parabolicScale r z) ∈
        goodPointPastCylinder x₀ t₀ r := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  change (x₀ + r • x, t₀ + r ^ 2 * t) ∈
    vec3Ball x₀ r ×ˢ Ioo (t₀ - r ^ 2) t₀
  constructor
  · change vec3EuclideanNorm (x₀ + r • x - x₀) < r
    rw [add_sub_cancel_left, vec3EuclideanNorm_smul, abs_of_pos hr]
    have hx' : vec3EuclideanNorm x < 1 := by
      simpa only [mem_vec3Ball, sub_zero] using hx
    nlinarith only [hx', hr]
  · have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    have htlower : -(1 : ℝ) < t := by
      simpa only [zero_sub, one_pow] using ht.1
    have htupper : t < 0 := ht.2
    constructor
    · have h := mul_lt_mul_of_pos_left htlower hr2
      linarith only [h]
    · have h := mul_neg_of_pos_of_neg hr2 htupper
      linarith only [h]

/-- Zero extension has no effect on the rescaled energy inside an admissible
open past cylinder. -/
theorem blowupEnergy_eq_unextendedRescale
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (hopen : goodPointPastCylinder x₀ t₀ r ⊆ goodPointDomain) :
    goodPointEnergy (blowupVelocity x₀ t₀ r u)
        (blowupPressure x₀ t₀ r p) 0 0 1 =
      goodPointEnergy (parabolicRescaleVelocity x₀ t₀ r u)
        (parabolicRescalePressure x₀ t₀ r p) 0 0 1 := by
  rw [goodPointEnergy_eq_open_top, goodPointEnergy_eq_open_top]
  have hBmeas : MeasurableSet (goodPointPastCylinder (0 : Vec3) 0 1) :=
    (vec3Ball_measurable 0 1).prod measurableSet_Ioo
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hBmeas] with z hz
  have hzD : z ∈ blowupDomain x₀ t₀ r :=
    hopen (blowupOpenPast_image_subset x₀ t₀ r hr z hz)
  rw [blowupVelocity_eq_of_mem x₀ t₀ r u z hzD,
    blowupPressure_eq_of_mem x₀ t₀ r p z hzD]
  rfl

/-- The zero-extended blow-up fields have exactly the normalized critical
energy of the original fields at an admissible open-top radius. -/
theorem blowupEnergy_rescale_of_admissible
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (hopen : goodPointPastCylinder x₀ t₀ r ⊆ goodPointDomain) :
    goodPointEnergy (blowupVelocity x₀ t₀ r u)
        (blowupPressure x₀ t₀ r p) 0 0 1 =
      ENNReal.ofReal (r⁻¹ ^ 2) * goodPointEnergy u p x₀ t₀ r := by
  rw [blowupEnergy_eq_unextendedRescale u p x₀ t₀ r hr hopen]
  rw [goodPointEnergy, goodPointEnergy]
  have hscaled (z : ParabolicPoint) :
      ENNReal.ofReal
          (vec3EuclideanNorm (parabolicRescaleVelocity x₀ t₀ r u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |parabolicRescalePressure x₀ t₀ r p z| ^ (3 / 2 : ℝ) =
        ENNReal.ofReal (r ^ 3) *
          (ENNReal.ofReal (vec3EuclideanNorm
              (u (parabolicTranslate x₀ t₀ (parabolicScale r z)))) ^ (3 : ℝ) +
            ENNReal.ofReal |p (parabolicTranslate x₀ t₀
              (parabolicScale r z))| ^ (3 / 2 : ℝ)) := by
    rw [parabolicRescaleVelocity, parabolicRescalePressure,
      vec3EuclideanNorm_smul, abs_of_pos hr, abs_mul,
      abs_of_nonneg (sq_nonneg r)]
    have hU : ENNReal.ofReal
          (r * vec3EuclideanNorm
            (u (parabolicTranslate x₀ t₀ (parabolicScale r z)))) ^ (3 : ℝ) =
        ENNReal.ofReal (r ^ 3) *
          ENNReal.ofReal (vec3EuclideanNorm
            (u (parabolicTranslate x₀ t₀ (parabolicScale r z)))) ^ (3 : ℝ) := by
      rw [ENNReal.ofReal_mul (p := r)
          (q := vec3EuclideanNorm
            (u (parabolicTranslate x₀ t₀ (parabolicScale r z)))) hr.le,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (3 : ℝ)),
        ENNReal.ofReal_rpow_of_nonneg hr.le (by norm_num : 0 ≤ (3 : ℝ))]
      exact congrArg (fun a : ℝ≥0∞ => a *
          ENNReal.ofReal (vec3EuclideanNorm
            (u (parabolicTranslate x₀ t₀ (parabolicScale r z)))) ^ (3 : ℝ))
        (congrArg ENNReal.ofReal (Real.rpow_natCast r 3))
    have hP : ENNReal.ofReal
          (r ^ 2 * |p (parabolicTranslate x₀ t₀ (parabolicScale r z))|) ^
            (3 / 2 : ℝ) =
        ENNReal.ofReal (r ^ 3) *
          ENNReal.ofReal |p (parabolicTranslate x₀ t₀ (parabolicScale r z))| ^
            (3 / 2 : ℝ) := by
      rw [ENNReal.ofReal_mul (p := r ^ 2)
          (q := |p (parabolicTranslate x₀ t₀ (parabolicScale r z))|)
          (sq_nonneg r),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (3 / 2 : ℝ)),
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg r)
          (by norm_num : 0 ≤ (3 / 2 : ℝ))]
      have hscalar : (r ^ 2) ^ (3 / 2 : ℝ) = r ^ 3 := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_natCast r 3,
          ← Real.rpow_mul (le_of_lt hr)]
        norm_num
      rw [hscalar]
    rw [hU, hP]
    ring
  simp_rw [hscaled]
  have hscale := CKN.Core.Endgame.force_slot_lintegral_scaling hr (x₀, t₀)
    (0, 0) (1 : ℝ)
    (fun z : ParabolicPoint =>
      ENNReal.ofReal (r ^ 3) *
        (ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)))
  have hscale' :
      (∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (r ^ 3) *
          (ENNReal.ofReal (vec3EuclideanNorm (u
            (parabolicTranslate x₀ t₀ (parabolicScale r z)))) ^ (3 : ℝ) +
            ENNReal.ofReal |p (parabolicTranslate x₀ t₀
              (parabolicScale r z))| ^ (3 / 2 : ℝ))) =
        ENNReal.ofReal (r⁻¹ ^ 5) *
          (∫⁻ z in parabolicCylinder x₀ t₀ r,
            ENNReal.ofReal (r ^ 3) *
              (ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
                ENNReal.ofReal |p z| ^ (3 / 2 : ℝ))) := by
    simpa [CKN.scalingParabolic, parabolicTranslate, parabolicScale] using hscale
  rw [hscale']
  rw [lintegral_const_mul' (ENNReal.ofReal (r ^ 3)) _ ENNReal.ofReal_ne_top]
  have hcoeff : ENNReal.ofReal (r⁻¹ ^ 5) * ENNReal.ofReal (r ^ 3) =
      ENNReal.ofReal (r⁻¹ ^ 2) := by
    rw [← ENNReal.ofReal_mul (p := r⁻¹ ^ 5) (q := r ^ 3)
      (by positivity : 0 ≤ r⁻¹ ^ 5)]
    congr 1
    field_simp
  rw [← mul_assoc, hcoeff]

/-- At every admissible radius, a bad point gives the same lower bound on the
rescaled unit-cylinder energy. -/
theorem blowupBadPointRescaledEnergy_lower
    (ε₀ : ℝ) (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (z₀ : ParabolicPoint) (r : ℝ)
    (hbad : ¬ IsGoodPoint ε₀ u p z₀)
    (hbase : z₀ ∈ goodPointClosedTopDomain)
    (hr : 0 < r)
    (hopen : goodPointPastCylinder z₀.1 z₀.2 r ⊆ goodPointDomain)
    (hclosed : closure (parabolicCylinder z₀.1 z₀.2 r) ⊆
      goodPointClosedTopDomain) :
    ENNReal.ofReal (ε₀ / 8) ≤
      goodPointEnergy (blowupVelocity z₀.1 z₀.2 r u)
        (blowupPressure z₀.1 z₀.2 r p) 0 0 1 := by
  rw [blowupEnergy_rescale_of_admissible u p z₀.1 z₀.2 r hr hopen]
  exact blowupBadPointEnergy_lower ε₀ u p z₀ r hbad hbase hr hopen hclosed

/-- A sufficiently small radius at a bad point has the quantitative
rescaled-unit-cylinder lower bound. -/
theorem blowupBadPoint_smallRadius_lower
    (ε₀ : ℝ) (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ r : ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hbad : ¬ IsGoodPoint ε₀ u p (x₀, t₀))
    (hr : 0 < r) (hrsmall : r < 1 / 4) :
    ENNReal.ofReal (ε₀ / 8) ≤
      goodPointEnergy (blowupVelocity x₀ t₀ r u)
        (blowupPressure x₀ t₀ r p) 0 0 1 := by
  obtain ⟨hbase, hopen, hclosed⟩ :=
    blowupSmallRadius_admissible x₀ t₀ r hx₀ ht₀ hr hrsmall
  exact blowupBadPointRescaledEnergy_lower ε₀ u p (x₀, t₀) r
    hbad hbase hr hopen hclosed

/-- Along any shrinking positive scale sequence, the bad-point energy lower
bound holds on the rescaled unit cylinder from some index onward. -/
theorem blowupBadPoint_eventually_lower
    (ε₀ : ℝ) (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hbad : ¬ IsGoodPoint ε₀ u p (x₀, t₀))
    (hr : ∀ k, 0 < r k)
    (hr0 : Filter.Tendsto r Filter.atTop (nhds 0)) :
    ∀ᶠ k in Filter.atTop,
      ENNReal.ofReal (ε₀ / 8) ≤
        goodPointEnergy (blowupVelocity x₀ t₀ (r k) u)
          (blowupPressure x₀ t₀ (r k) p) 0 0 1 := by
  have hsmall : ∀ᶠ k in Filter.atTop, r k < 1 / 4 :=
    hr0.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall] with k hk
  exact blowupBadPoint_smallRadius_lower ε₀ u p x₀ t₀ (r k)
    hx₀ ht₀ hbad (hr k) hk

end ESS
