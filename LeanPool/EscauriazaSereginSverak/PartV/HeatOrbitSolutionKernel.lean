/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalMain
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatKernel

/-!
# Kernel bounds for the heat orbit of an `L²` datum

At positive times the Gaussian kernel and its spatial derivatives are square
integrable, uniformly for times bounded away from zero.  By the Cauchy–Schwarz
inequality the heat orbit of an `L²` datum and the convolution of the datum
with a kernel derivative are therefore bounded pointwise, Lipschitz in the
datum, and jointly measurable in space and time.  These are the kernel facts
behind the heat-orbit clauses of `prop:pv-local-solution`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

/-- Convolution of a scalar datum with the `j`th spatial derivative of the
Gaussian kernel at time `t`; for `t > 0` it is the classical `j`th derivative
of the heat orbit. -/
@[expose] def heatConvGrad (t : ℝ) (f : Vec3 → ℝ) (j : Fin 3) (x : Vec3) : ℝ :=
  ∫ y : Vec3, heatKernelSpaceDerivative y t j * f (x - y)

/-- The Gaussian kernel is jointly measurable in space and time. -/
theorem heatKernel_vecTime_measurable :
    Measurable (fun p : Vec3 × ℝ => heatKernel p.1 p.2) := by
  unfold heatKernel
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd) ?_ measurable_const
  fun_prop

/-- The weight `C (1 + |y|)⁻³` is square integrable on `ℝ³`. -/
theorem one_add_norm_inv_cube_memLp_two (C : ℝ) :
    MemLp (fun y : Vec3 => C * ((1 + ‖y‖) ^ 3)⁻¹) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun y : Vec3 => C * ((1 + ‖y‖) ^ 3)⁻¹) volume := by
    have hc : Continuous (fun y : Vec3 => C * ((1 + ‖y‖) ^ 3)⁻¹) := by
      have hne : ∀ y : Vec3, (1 + ‖y‖) ^ 3 ≠ 0 := fun y => by positivity
      exact continuous_const.mul
        (((continuous_const.add continuous_norm).pow 3).inv₀ hne)
    exact hc.aestronglyMeasurable
  have hfin : (Module.finrank ℝ Vec3 : ℝ) < 6 := by
    rw [Module.finrank_fin_fun]
    norm_num
  have hweight : Integrable (fun x : Vec3 => (1 + ‖x‖) ^ (-(6 : ℝ))) volume :=
    integrable_one_add_norm (μ := volume) (E := Vec3) (r := 6) hfin
  apply (memLp_two_iff_integrable_sq hmeas).2
  refine (hweight.const_mul (C ^ 2)).congr (Filter.Eventually.of_forall fun y => ?_)
  have hpos : 0 < 1 + ‖y‖ := by positivity
  change C ^ 2 * (1 + ‖y‖) ^ (-(6 : ℝ)) = (C * ((1 + ‖y‖) ^ 3)⁻¹) ^ 2
  rw [Real.rpow_neg hpos.le, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-- For times bounded away from zero, the Gaussian kernel and its spatial
derivatives are bounded in `L²` uniformly in time. -/
theorem heatKernel_eLpNorm_two_uniform {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ t : ℝ, δ ≤ t →
      eLpNorm (fun y : Vec3 => heatKernel y t) 2 volume ≤ B ∧
      ∀ j : Fin 3, eLpNorm (fun y : Vec3 => heatKernelSpaceDerivative y t j) 2 volume ≤ B := by
  set s : ℝ := Real.sqrt δ with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hδ
  set m : ℝ := min s 1 with hm_def
  have hm : 0 < m := lt_min hs one_pos
  have hms : m ≤ s := min_le_left _ _
  have hm1 : m ≤ 1 := min_le_right _ _
  set C : ℝ := 1000 / m ^ 3 + 300000 / (s * m ^ 3) with hC_def
  refine ⟨eLpNorm (fun y : Vec3 => C * ((1 + ‖y‖) ^ 3)⁻¹) 2 volume,
    (one_add_norm_inv_cube_memLp_two C).eLpNorm_lt_top, fun t ht => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le hδ ht
  have hsqrt : s ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  have hrho (y : Vec3) : m * (1 + ‖y‖) ≤ rhoTwo y t := by
    unfold rhoTwo
    have h1 : ‖y‖ ≤ vec3EuclideanNorm y := norm_le_vec3EuclideanNorm y
    have h3 : m * ‖y‖ ≤ ‖y‖ := mul_le_of_le_one_left (norm_nonneg _) hm1
    rw [mul_add, mul_one]
    linarith only [h1, h3, hms, hsqrt]
  have hbase (y : Vec3) : 0 < m * (1 + ‖y‖) := by positivity
  have hcube (y : Vec3) : (m * (1 + ‖y‖)) ^ 3 ≤ rhoTwo y t ^ 3 :=
    pow_le_pow_left₀ (hbase y).le (hrho y) 3
  have hweq (y : Vec3) (A : ℝ) : A / (m * (1 + ‖y‖)) ^ 3 =
      A / m ^ 3 * ((1 + ‖y‖) ^ 3)⁻¹ := by
    rw [mul_pow]
    field_simp
  have hW1 (y : Vec3) : 1000 / m ^ 3 * ((1 + ‖y‖) ^ 3)⁻¹ ≤ C * ((1 + ‖y‖) ^ 3)⁻¹ := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [hC_def]
    have : 0 ≤ 300000 / (s * m ^ 3) := by positivity
    linarith only [this]
  have hW2 (y : Vec3) : 300000 / (s * m ^ 3) * ((1 + ‖y‖) ^ 3)⁻¹ ≤
      C * ((1 + ‖y‖) ^ 3)⁻¹ := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [hC_def]
    have : 0 ≤ 1000 / m ^ 3 := by positivity
    linarith only [this]
  refine ⟨?_, fun j => ?_⟩
  · have hmeas : AEStronglyMeasurable (fun y : Vec3 => heatKernel y t) volume :=
      (heatKernel_vecTime_measurable.comp (measurable_id.prodMk
        measurable_const)).aestronglyMeasurable
    refine eLpNorm_mono_real hmeas fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg y t)]
    calc
      heatKernel y t ≤ 1000 / rhoTwo y t ^ 3 := heatKernel_le_rho_inv_cube htpos
      _ ≤ 1000 / (m * (1 + ‖y‖)) ^ 3 :=
        div_le_div_of_nonneg_left (by norm_num) (pow_pos (hbase y) 3) (hcube y)
      _ = 1000 / m ^ 3 * ((1 + ‖y‖) ^ 3)⁻¹ := hweq y 1000
      _ ≤ C * ((1 + ‖y‖) ^ 3)⁻¹ := hW1 y
  · have hmeas : AEStronglyMeasurable (fun y : Vec3 => heatKernelSpaceDerivative y t j) volume :=
      ((heatKernelSpaceDerivative_vecTime_measurable j).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    refine eLpNorm_mono_real hmeas fun y => ?_
    rw [Real.norm_eq_abs]
    have hrpos : 0 < rhoTwo y t := lt_of_lt_of_le (hbase y) (hrho y)
    have hrs : s ≤ rhoTwo y t := by
      unfold rhoTwo
      linarith only [vec3EuclideanNorm_nonneg y, hsqrt]
    calc
      |heatKernelSpaceDerivative y t j| ≤ 300000 / rhoTwo y t ^ 4 :=
        heatKernelSpaceDerivative_abs_le_rho_inv_four htpos j
      _ ≤ 300000 / (s * (m * (1 + ‖y‖)) ^ 3) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        rw [show rhoTwo y t ^ 4 = rhoTwo y t * rhoTwo y t ^ 3 by ring]
        exact mul_le_mul hrs (hcube y) (by positivity) hrpos.le
      _ = 300000 / (s * m ^ 3) * ((1 + ‖y‖) ^ 3)⁻¹ := by
        rw [mul_pow]
        field_simp
      _ ≤ C * ((1 + ‖y‖) ^ 3)⁻¹ := hW2 y

/-- At a positive time the Gaussian kernel and its spatial derivatives are
square integrable. -/
theorem heatKernel_memLp_two {t : ℝ} (ht : 0 < t) :
    MemLp (fun y : Vec3 => heatKernel y t) 2 volume ∧
      ∀ j : Fin 3, MemLp (fun y : Vec3 => heatKernelSpaceDerivative y t j) 2 volume := by
  obtain ⟨B, hB, hbound⟩ := heatKernel_eLpNorm_two_uniform ht
  obtain ⟨hK, hD⟩ := hbound t le_rfl
  exact ⟨hK.trans_lt hB, fun j => (hD j).trans_lt hB⟩

/-- The Cauchy–Schwarz inequality for a convolution integral at one point. -/
theorem lintegral_enorm_mul_sub_le {k f : Vec3 → ℝ} (hk : AEStronglyMeasurable k volume)
    (hf : AEStronglyMeasurable f volume) (x : Vec3) :
    ∫⁻ y : Vec3, ‖k y‖ₑ * ‖f (x - y)‖ₑ ≤ eLpNorm k 2 volume * eLpNorm f 2 volume := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Vec3) x
  have hfx : AEStronglyMeasurable (fun y => f (x - y)) volume :=
    hf.comp_measurePreserving hmp
  have hfxNorm : eLpNorm (fun y => f (x - y)) 2 volume = eLpNorm f 2 volume :=
    eLpNorm_comp_measurePreserving hf hmp
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Vec3) hpq
    (f := fun y => ‖k y‖ₑ) (g := fun y => ‖f (x - y)‖ₑ) hk.enorm hfx.enorm
  rw [← hfxNorm, eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hk,
    eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hfx,
    eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  simpa using h

/-- A convolution integral of two `L²` functions converges absolutely at every
point and is bounded by the product of the `L²` norms. -/
theorem integrable_mul_sub_enorm_le {k f : Vec3 → ℝ} (hk : MemLp k 2 volume)
    (hf : MemLp f 2 volume) (x : Vec3) :
    Integrable (fun y : Vec3 => k y * f (x - y)) volume ∧
      ‖∫ y : Vec3, k y * f (x - y)‖ₑ ≤ eLpNorm k 2 volume * eLpNorm f 2 volume := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Vec3) x
  have hfx : AEStronglyMeasurable (fun y => f (x - y)) volume :=
    hf.aestronglyMeasurable.comp_measurePreserving hmp
  have hl := lintegral_enorm_mul_sub_le hk.aestronglyMeasurable hf.aestronglyMeasurable x
  have hl' : ∫⁻ y : Vec3, ‖k y * f (x - y)‖ₑ ≤ eLpNorm k 2 volume * eLpNorm f 2 volume := by
    simpa only [enorm_mul] using hl
  have hfin : eLpNorm k 2 volume * eLpNorm f 2 volume < ∞ :=
    ENNReal.mul_lt_top hk.eLpNorm_lt_top hf.eLpNorm_lt_top
  exact ⟨⟨hk.aestronglyMeasurable.mul hfx, hasFiniteIntegral_iff_enorm.2 (hl'.trans_lt hfin)⟩,
    (enorm_integral_le_lintegral_enorm _).trans hl'⟩

/-- The convolution integral is Lipschitz in the datum for the `L²` norm. -/
theorem integral_mul_sub_sub_enorm_le {k f g : Vec3 → ℝ} (hk : MemLp k 2 volume)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x : Vec3) :
    ‖(∫ y : Vec3, k y * f (x - y)) - ∫ y : Vec3, k y * g (x - y)‖ₑ ≤
      eLpNorm k 2 volume * eLpNorm (f - g) 2 volume := by
  have hfI := (integrable_mul_sub_enorm_le hk hf x).1
  have hgI := (integrable_mul_sub_enorm_le hk hg x).1
  rw [← integral_sub hfI hgI]
  have heq : (fun y : Vec3 => k y * f (x - y) - k y * g (x - y)) =
      fun y => k y * (f - g) (x - y) := by
    funext y
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  exact (integrable_mul_sub_enorm_le hk (hf.sub hg) x).2

/-- A convolution integral in space whose kernel depends measurably on time is
jointly strongly measurable in space and time. -/
theorem stronglyMeasurable_integral_kernel_mul_sub {k : Vec3 × ℝ → ℝ} (hk : Measurable k)
    {f : Vec3 → ℝ} (hf : AEStronglyMeasurable f volume) :
    StronglyMeasurable (fun z : ParabolicPoint => ∫ y : Vec3, k (y, z.2) * f (z.1 - y)) := by
  set g : Vec3 → ℝ := hf.mk f
  have hg : StronglyMeasurable g := hf.stronglyMeasurable_mk
  have heq : (fun z : ParabolicPoint => ∫ y : Vec3, k (y, z.2) * f (z.1 - y)) =
      fun z => ∫ y : Vec3, k (y, z.2) * g (z.1 - y) := by
    funext z
    apply integral_congr_ae
    have hmp := Measure.measurePreserving_sub_left (volume : Measure Vec3) z.1
    filter_upwards [hmp.quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk] with y hy
    simp only [Function.comp_apply] at hy
    rw [hy]
  rw [heq]
  apply StronglyMeasurable.integral_prod_right
    (f := fun (z : ParabolicPoint) (y : Vec3) => k (y, z.2) * g (z.1 - y))
  apply Measurable.stronglyMeasurable
  change Measurable (fun p : ParabolicPoint × Vec3 => k (p.2, p.1.2) * g (p.1.1 - p.2))
  exact (hk.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).mul
    (hg.measurable.comp ((measurable_fst.comp measurable_fst).sub measurable_snd))

/-- The heat orbit of an `L²` datum is bounded pointwise, uniformly for times
bounded away from zero, and so is its convolution with a kernel derivative. -/
theorem heatConv_heatConvGrad_bound {δ : ℝ} (hδ : 0 < δ) {f : Vec3 → ℝ}
    (hf : MemLp f 2 volume) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, δ ≤ t → ∀ x : Vec3,
      |heatConv t f x| ≤ M ∧ ∀ j : Fin 3, |heatConvGrad t f j x| ≤ M := by
  obtain ⟨B, hB, hbound⟩ := heatKernel_eLpNorm_two_uniform hδ
  have hfin : B * eLpNorm f 2 volume ≠ ∞ := (ENNReal.mul_lt_top hB hf.eLpNorm_lt_top).ne
  refine ⟨(B * eLpNorm f 2 volume).toReal, ENNReal.toReal_nonneg, fun t ht x => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le hδ ht
  obtain ⟨hK, hD⟩ := heatKernel_memLp_two htpos
  obtain ⟨hKB, hDB⟩ := hbound t ht
  have hconv (k : Vec3 → ℝ) (hk : MemLp k 2 volume) (hkB : eLpNorm k 2 volume ≤ B) :
      |∫ y : Vec3, k y * f (x - y)| ≤ (B * eLpNorm f 2 volume).toReal := by
    rw [← Real.norm_eq_abs, ← toReal_enorm]
    apply ENNReal.toReal_mono hfin
    exact (integrable_mul_sub_enorm_le hk hf x).2.trans (by gcongr)
  refine ⟨?_, fun j => hconv _ (hD j) (hDB j)⟩
  rw [heatConv_eq_integral]
  exact hconv _ hK hKB

end ESS

end
