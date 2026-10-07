/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# A fixed radial regularizing kernel

The profile and its dilates used by `eq:reg-mollifier` on the Euclidean
three dimensional `L²` carrier.
-/

public section

open MeasureTheory
open scoped Convolution ENNReal

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

private theorem finrank_L2Vec3 : Module.finrank ℝ L2Vec3 = 3 := by
  calc
    Module.finrank ℝ L2Vec3 = Module.finrank ℝ (Fin 3 → ℝ) :=
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).finrank_eq
    _ = Fintype.card (Fin 3) := Module.finrank_pi ℝ
    _ = 3 := by simp

/-- Smooth compactly supported radial data for the kernel in
`lem:reg-mollifier-bounds`. -/
structure RegMollifierProfile where
  /-- The fixed real scalar kernel. -/
  rho : SchwartzMap L2Vec3 ℝ
  /-- The kernel is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) rho
  /-- The kernel has compact support. -/
  compact : HasCompactSupport rho
  /-- The support is contained in the unit ball. -/
  support_unit : tsupport rho ⊆ Metric.ball (0 : L2Vec3) 1
  /-- Radiality of the profile. -/
  radial : ∀ x y : L2Vec3, ‖x‖ = ‖y‖ → rho x = rho y
  /-- The profile is nonnegative. -/
  nonneg : ∀ x, 0 ≤ rho x
  /-- The profile has total mass one. -/
  integral_eq_one : ∫ x : L2Vec3, rho x = 1

/-- The normalized spatial dilate of the fixed profile. -/
@[expose]
def regMollifierKernel (ρ : RegMollifierProfile) (ε : ℝ) (_hε : 0 < ε)
    (x : L2Vec3) : ℝ :=
  (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • x)

/-- The dilated profile remains radial. -/
theorem regMollifierKernel_radial (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) {x y : L2Vec3} (hxy : ‖x‖ = ‖y‖) :
    regMollifierKernel ρ ε hε x = regMollifierKernel ρ ε hε y := by
  unfold regMollifierKernel
  have hscaled : ‖ε⁻¹ • x‖ = ‖ε⁻¹ • y‖ := by rw [norm_smul, norm_smul, hxy]
  rw [ρ.radial _ _ hscaled]

/-- The dilated profile is nonnegative. -/
theorem regMollifierKernel_nonneg (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) (x : L2Vec3) :
    0 ≤ regMollifierKernel ρ ε hε x := by
  unfold regMollifierKernel
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _)) (ρ.nonneg _)

/-- The normalized dilate has total mass one. -/
theorem regMollifierKernel_integral_eq_one (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) :
    ∫ x : L2Vec3, regMollifierKernel ρ ε hε x = 1 := by
  have hdim : Module.finrank ℝ L2Vec3 = 3 := finrank_L2Vec3
  have hchange :
      ∫ x : L2Vec3, ρ.rho (ε⁻¹ • x) =
        |ε ^ Module.finrank ℝ L2Vec3| * ∫ x : L2Vec3, ρ.rho x := by
    simpa [smul_eq_mul] using
      (Measure.integral_comp_inv_smul (μ := volume) (f := ρ.rho) ε)
  change ∫ x : L2Vec3, (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • x) = 1
  rw [integral_const_mul, hchange, hdim, abs_of_pos (pow_pos hε 3),
    ρ.integral_eq_one]
  field_simp [ne_of_gt hε]

private theorem regMollifierKernel_contDiff (ρ : RegMollifierProfile)
    (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • x)) := by
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun x : L2Vec3 => ε⁻¹ • x) := by
    fun_prop
  exact contDiff_const.mul (ρ.smooth.comp hscale)

private theorem regMollifierKernel_hasCompactSupport
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (regMollifierKernel ρ ε hε) := by
  unfold regMollifierKernel
  have hscale : ε⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hε)
  have hcompact := ρ.compact.comp_homeomorph
    (Homeomorph.smulOfNeZero ε⁻¹ hscale)
  change HasCompactSupport (fun x => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • x))
  exact hcompact.mul_left

/-- Every dilated profile belongs to `L²`; this supplies the convolution
kernel in the pointwise estimate of `lem:reg-mollifier-bounds`. -/
theorem regMollifierKernel_memLp_two (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) :
  MemLp (regMollifierKernel ρ ε hε) (2 : ℝ≥0∞) volume := by
  change MemLp (fun x => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • x))
    (2 : ℝ≥0∞) volume
  exact (regMollifierKernel_contDiff ρ ε).continuous.memLp_of_hasCompactSupport
    (regMollifierKernel_hasCompactSupport ρ ε hε)

/-- The dilated kernel is integrable, as required for probability averaging
in `lem:reg-mollifier-bounds`. -/
theorem regMollifierKernel_integrable (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) : Integrable (regMollifierKernel ρ ε hε) volume := by
  exact (regMollifierKernel_contDiff ρ ε).continuous.integrable_of_hasCompactSupport
    (regMollifierKernel_hasCompactSupport ρ ε hε)

private theorem regMollifierKernel_integral_norm_sq (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) :
    ∫ x : L2Vec3, ‖regMollifierKernel ρ ε hε x‖ ^ 2 =
      ε ^ (-3 : ℝ) * ∫ x : L2Vec3, ‖ρ.rho x‖ ^ 2 := by
  have hdim : Module.finrank ℝ L2Vec3 = 3 := finrank_L2Vec3
  have hchange := Measure.integral_comp_inv_smul (μ := volume)
    (f := fun x : L2Vec3 => ‖ρ.rho x‖ ^ 2) ε
  calc
    ∫ x : L2Vec3, ‖regMollifierKernel ρ ε hε x‖ ^ 2 =
        (ε ^ 3)⁻¹ ^ 2 * ∫ x : L2Vec3, ‖ρ.rho (ε⁻¹ • x)‖ ^ 2 := by
      change ∫ x : L2Vec3,
        ‖(ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • x)‖ ^ 2 = _
      calc
        _ = ∫ x : L2Vec3,
            ((ε ^ 3)⁻¹ ^ 2) * ‖ρ.rho (ε⁻¹ • x)‖ ^ 2 := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hε 3))]
              ring
        _ = (ε ^ 3)⁻¹ ^ 2 * ∫ x : L2Vec3, ‖ρ.rho (ε⁻¹ • x)‖ ^ 2 := by
              rw [integral_const_mul]
    _ = ε ^ (-3 : ℝ) * ∫ x : L2Vec3, ‖ρ.rho x‖ ^ 2 := by
      rw [hchange, hdim, abs_of_pos (pow_pos hε 3), smul_eq_mul]
      have hpow : ε ^ (-3 : ℝ) = (ε ^ 3)⁻¹ := by
        calc
          ε ^ (-3 : ℝ) = (ε ^ (3 : ℝ))⁻¹ := by
            rw [Real.rpow_neg (by positivity)]
          _ = (ε ^ 3)⁻¹ := by
            exact congrArg Inv.inv (Real.rpow_natCast ε 3)
      rw [hpow]
      field_simp [ne_of_gt hε]

/-- The normalized spatial dilate has the expected three dimensional
`L²` scaling, used in the derivative bounds of `lem:reg-mollifier-bounds`. -/
theorem regMollifierKernel_eLpNorm_two (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) :
    eLpNorm (regMollifierKernel ρ ε hε) 2 volume =
      ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume := by
  have hρ : MemLp ρ.rho (2 : ℝ≥0∞) volume :=
    ρ.smooth.continuous.memLp_of_hasCompactSupport ρ.compact
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
        (regMollifierKernel_memLp_two ρ ε hε),
      MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hρ]
  simp only [ENNReal.toReal_ofNat]
  have hscaleNat := regMollifierKernel_integral_norm_sq ρ ε hε
  have hscale : ∫ a : L2Vec3, ‖regMollifierKernel ρ ε hε a‖ ^ (2 : ℝ) =
      ε ^ (-3 : ℝ) * ∫ a : L2Vec3, ‖ρ.rho a‖ ^ (2 : ℝ) := by
    calc
      ∫ a : L2Vec3, ‖regMollifierKernel ρ ε hε a‖ ^ (2 : ℝ) =
          ∫ a : L2Vec3, ‖regMollifierKernel ρ ε hε a‖ ^ 2 := by
        congr 1
        funext a
        exact Real.rpow_natCast _ 2
      _ = ε ^ (-3 : ℝ) * ∫ a : L2Vec3, ‖ρ.rho a‖ ^ 2 := hscaleNat
      _ = ε ^ (-3 : ℝ) * ∫ a : L2Vec3, ‖ρ.rho a‖ ^ (2 : ℝ) := by
        congr 2
        funext a
        exact (Real.rpow_natCast _ 2).symm
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
  calc
    (∫ a : L2Vec3, ‖regMollifierKernel ρ ε hε a‖ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ =
        (ε ^ (-3 : ℝ) * ∫ a : L2Vec3, ‖ρ.rho a‖ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
      exact congrArg (fun z : ℝ => z ^ (2 : ℝ)⁻¹) hscale
    _ = ε ^ (-(3 / 2 : ℝ)) *
        (∫ a : L2Vec3, ‖ρ.rho a‖ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_mul (le_of_lt hε)]
      norm_num

/-- Componentwise convolution by the dilated radial profile. -/
@[expose]
def scalarVectorActionLinear : ℝ →ₗ[ℝ] L2Vec3 →ₗ[ℝ] L2Vec3 :=
  LinearMap.mk₂ ℝ (fun c x => c • x)
    (by intro c d x; exact add_smul c d x)
    (by intro c d x; exact mul_smul c d x)
    (by intro c x y; exact smul_add c x y)
    (by intro c d x; exact (smul_comm c d x).symm)

/-- The continuous scalar multiplication map on Hilbert vectors used by convolution. -/
@[expose]
def scalarVectorAction : ℝ →L[ℝ] L2Vec3 →L[ℝ] L2Vec3 :=
  scalarVectorActionLinear.mkContinuous₂ 1 (by
    intro c x
    change ‖c • x‖ ≤ 1 * ‖c‖ * ‖x‖
    simpa [one_mul] using (norm_smul_le c x))

/-- Componentwise convolution by the dilated radial profile. -/
@[expose]
def regMollifyVector (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (f : L2Vec3 → L2Vec3) : L2Vec3 → L2Vec3 :=
  MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
    scalarVectorAction volume

/-- The `L² × L² → L∞` estimate for the pointwise vector convolution by the
fixed regularizing kernel. -/
theorem regMollifyVector_pointwise_enorm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : L2Vec3 → L2Vec3} (hf : MemLp f (2 : ℝ≥0∞) volume)
    (x : L2Vec3) :
    ‖regMollifyVector ρ ε hε f x‖ₑ ≤
      eLpNorm (regMollifierKernel ρ ε hε) 2 volume * eLpNorm f 2 volume := by
  change ‖MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
      scalarVectorAction volume x‖ₑ ≤ _
  calc
    _ ≤ ‖scalarVectorAction‖ₑ *
        eLpNorm (regMollifierKernel ρ ε hε) 2 volume * eLpNorm f 2 volume := by
          exact MeasureTheory.enorm_convolution_le
            (L := scalarVectorAction)
            (p := (2 : ℝ≥0∞)) (q := 2)
            (regMollifierKernel_memLp_two ρ ε hε).aestronglyMeasurable
            hf.aestronglyMeasurable x
    _ ≤ eLpNorm (regMollifierKernel ρ ε hε) 2 volume * eLpNorm f 2 volume := by
      have hL : ‖scalarVectorAction‖ₑ ≤ 1 :=
        ContinuousLinearMap.opENorm_le_iff.mpr (by
        intro c
        have hc : ‖scalarVectorAction c‖ₑ ≤ ‖c‖ₑ := by
          apply ContinuousLinearMap.opENorm_le_bound
          intro x
          change ‖c • x‖ₑ ≤ _
          exact enorm_smul_le
        calc
          ‖scalarVectorAction c‖ₑ ≤ ‖c‖ₑ := hc
          _ = 1 * ‖c‖ₑ := by simp)
      calc
        ‖scalarVectorAction‖ₑ * eLpNorm (regMollifierKernel ρ ε hε) 2 volume *
            eLpNorm f 2 volume ≤
          (1 * eLpNorm (regMollifierKernel ρ ε hε) 2 volume) *
            eLpNorm f 2 volume := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hL (by positivity)) (by positivity)
        _ = eLpNorm (regMollifierKernel ρ ε hε) 2 volume * eLpNorm f 2 volume := by simp

/-- The pointwise estimate with the scale factor displayed in
`lem:reg-mollifier-bounds`. -/
theorem regMollifyVector_pointwise_enorm_le_scaled
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : L2Vec3 → L2Vec3} (hf : MemLp f (2 : ℝ≥0∞) volume)
    (x : L2Vec3) :
    ‖regMollifyVector ρ ε hε f x‖ₑ ≤
      ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) *
        eLpNorm ρ.rho 2 volume * eLpNorm f 2 volume := by
  calc
    ‖regMollifyVector ρ ε hε f x‖ₑ ≤
        eLpNorm (regMollifierKernel ρ ε hε) 2 volume * eLpNorm f 2 volume :=
      regMollifyVector_pointwise_enorm_le ρ ε hε hf x
    _ = ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) *
        eLpNorm ρ.rho 2 volume * eLpNorm f 2 volume := by
      rw [regMollifierKernel_eLpNorm_two ρ ε hε]

/-- The convolution by a dilated profile is measurable for every `L²`
representative. -/
theorem regMollifyVector_aestronglyMeasurable
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : L2Vec3 → L2Vec3} (hf : MemLp f (2 : ℝ≥0∞) volume) :
    AEStronglyMeasurable (regMollifyVector ρ ε hε f) volume := by
  change AEStronglyMeasurable
    (MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
      scalarVectorAction volume) volume
  exact (regMollifierKernel_memLp_two ρ ε hε).aestronglyMeasurable.convolution
    (L := scalarVectorAction) hf.aestronglyMeasurable

/-- The order-zero `L²` to `L∞` estimate for arbitrary profiles in
`lem:reg-mollifier-bounds`. -/
theorem regMollifyVector_eLpNorm_top_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : L2Vec3 → L2Vec3} (hf : MemLp f (2 : ℝ≥0∞) volume) :
    eLpNorm (regMollifyVector ρ ε hε f) ∞ volume ≤
      ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume * eLpNorm f 2 volume := by
  rw [eLpNorm_exponent_top (regMollifyVector_aestronglyMeasurable ρ ε hε hf)]
  exact eLpNormEssSup_le_of_ae_enorm_bound
    (Filter.Eventually.of_forall fun x =>
      regMollifyVector_pointwise_enorm_le_scaled ρ ε hε hf x)

end CKN.Leray

end
