/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatKernel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Integrability
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# A weighted `L¹` bound for the spatial-gradient heat kernel

On a slab `ℝ³ × (0,τ)`, the kernel `∂_j W₊` restricted to `(0,τ)` is integrable,
and against the weight `(1 + ‖x‖)^{-2}` its convolution with a source in `L²`
supported in `(0,τ)` is bounded in `L¹` by the `L²` norm of the source. This
identifies limits of forced heat responses of smooth approximants with the
kernel formula of `lem:pv-stokes` for rough tensors.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The spatial weight `(1 + ‖x‖)^{-2}` used to localize the rough forced heat
response. -/
@[expose] def forcedHeatWeight (x : Vec3) : ℝ := ((1 + ‖x‖) ^ 2)⁻¹

theorem forcedHeatWeight_pos (x : Vec3) : 0 < forcedHeatWeight x := by
  unfold forcedHeatWeight
  positivity

theorem forcedHeatWeight_continuous : Continuous forcedHeatWeight := by
  unfold forcedHeatWeight
  exact ((continuous_const.add continuous_norm).pow 2).inv₀ fun x =>
    (by positivity : (0 : ℝ) < (1 + ‖x‖) ^ 2).ne'

/-- The squared weight has finite integral over the slab. -/
theorem forcedHeatWeight_sq_lintegral_lt_top (τ : ℝ) :
    ∫⁻ z in (univ : Set Vec3) ×ˢ Ioo 0 τ, ENNReal.ofReal (forcedHeatWeight z.1) ^ (2 : ℝ)
      < ∞ := by
  have hint : Integrable (fun x : Vec3 => (1 + ‖x‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by rw [Module.finrank_fin_fun]; norm_num)
  have hsq (x : Vec3) : ENNReal.ofReal (forcedHeatWeight x) ^ (2 : ℝ) =
      ENNReal.ofReal ((1 + ‖x‖) ^ (-(4 : ℝ))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (forcedHeatWeight_pos x).le (by norm_num)]
    congr 1
    unfold forcedHeatWeight
    have hpos : 0 < 1 + ‖x‖ := by positivity
    rw [Real.rpow_two, inv_pow, ← pow_mul, Real.rpow_neg hpos.le, ← Real.rpow_natCast]
    norm_num
  have hfin : ∫⁻ x : Vec3, ENNReal.ofReal ((1 + ‖x‖) ^ (-(4 : ℝ))) < ∞ :=
    hint.lintegral_lt_top
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  calc
    ∫⁻ z, ENNReal.ofReal (forcedHeatWeight z.1) ^ (2 : ℝ)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 τ))) =
        ∫⁻ z, ENNReal.ofReal ((1 + ‖z.1‖) ^ (-(4 : ℝ))) * (fun _ : ℝ => (1 : ℝ≥0∞)) z.2
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 τ))) := by
      simp only [hsq, mul_one]
    _ = (∫⁻ x : Vec3, ENNReal.ofReal ((1 + ‖x‖) ^ (-(4 : ℝ)))) *
          ∫⁻ _t in Ioo 0 τ, (1 : ℝ≥0∞) :=
      lintegral_prod_mul (ENNReal.measurable_ofReal.comp ((continuous_const.add
        continuous_norm).rpow_const fun x => Or.inl
          (by positivity : (0 : ℝ) < 1 + ‖x‖).ne').measurable).aemeasurable
        aemeasurable_const
    _ < ∞ := by
      refine ENNReal.mul_lt_top hfin ?_
      simp [Real.volume_Ioo]

/-- The kernel `∂_j W₊` has finite mass on `ℝ³ × (0,τ]`. -/
theorem heatKernelSpaceDerivative_window_lintegral_lt_top {τ : ℝ} (hτ : 0 < τ) (j : Fin 3) :
    ∫⁻ p in (univ : Set Vec3) ×ˢ Ioc 0 τ, ‖heatKernelSpaceDerivative p.1 p.2 j‖ₑ < ∞ := by
  have hint := heatKernelGradientNorm_integrable_prod hτ
  have hfin := hint.hasFiniteIntegral
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hfin
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  apply ENNReal.ofReal_le_ofReal
  refine le_trans ?_ (le_abs_self _)
  exact Finset.single_le_sum (f := fun k => |heatKernelSpaceDerivative p.1 p.2 k|)
    (fun k _ => abs_nonneg _) (Finset.mem_univ j)

/-- The weighted `L¹` bound: for a source `H ∈ L²` vanishing at nonpositive times,
`∫_{ℝ³×(0,τ)} w(x) ∫ |∂_j W₊(p) H(z - p)| dp dz ≤ C ‖H‖₂` with `C` depending only
on `τ`. -/
theorem kernel_weighted_lintegral_le {τ : ℝ} (hτ : 0 < τ) (j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : Vec3 × ℝ → ℝ, AEStronglyMeasurable H volume →
      (∀ z, H z ≠ 0 → 0 < z.2) →
      ∫⁻ z in (univ : Set Vec3) ×ˢ Ioo 0 τ, ENNReal.ofReal (forcedHeatWeight z.1) *
          ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H (z - p)‖ₑ ≤
        ENNReal.ofReal C * eLpNorm H 2 volume := by
  set A : Set (Vec3 × ℝ) := (univ : Set Vec3) ×ˢ Ioo 0 τ
  set B : Set (Vec3 × ℝ) := (univ : Set Vec3) ×ˢ Ioc 0 τ
  have hA : MeasurableSet A := MeasurableSet.univ.prod measurableSet_Ioo
  have hB : MeasurableSet B := MeasurableSet.univ.prod measurableSet_Ioc
  set kB : Vec3 × ℝ → ℝ≥0∞ := B.indicator fun p => ‖heatKernelSpaceDerivative p.1 p.2 j‖ₑ
  set a : Vec3 × ℝ → ℝ≥0∞ := A.indicator fun z => ENNReal.ofReal (forcedHeatWeight z.1)
  set IK : ℝ≥0∞ := ∫⁻ p, kB p
  set Ia : ℝ≥0∞ := (∫⁻ z, a z ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
  have hIK : IK < ∞ := by
    simp only [IK, kB]
    rw [lintegral_indicator hB]
    exact heatKernelSpaceDerivative_window_lintegral_lt_top hτ j
  have hIa : Ia < ∞ := by
    have ha2 : (fun z => a z ^ (2 : ℝ)) = A.indicator fun z =>
        ENNReal.ofReal (forcedHeatWeight z.1) ^ (2 : ℝ) := by
      funext z
      by_cases hz : z ∈ A
      · simp [a, hz]
      · simp [a, hz]
    simp only [Ia]
    rw [ha2, lintegral_indicator hA]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (forcedHeatWeight_sq_lintegral_lt_top τ).ne
  refine ⟨(IK * Ia).toReal, ENNReal.toReal_nonneg, fun H hH hsupp => ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.mul_lt_top hIK hIa).ne]
  set H' : Vec3 × ℝ → ℝ := hH.mk H
  have hH' : StronglyMeasurable H' := hH.stronglyMeasurable_mk
  have hHH' : H =ᵐ[volume] H' := hH.ae_eq_mk
  have hKm := heatKernelSpaceDerivative_vecTime_measurable j
  have hkBm : Measurable kB := (hKm.enorm).indicator hB
  have ham : Measurable a :=
    (ENNReal.measurable_ofReal.comp (forcedHeatWeight_continuous.measurable.comp
      measurable_fst)).indicator hA
  have hh'm : Measurable (fun z : Vec3 × ℝ => ‖H' z‖ₑ) := hH'.measurable.enorm
  -- step 1: restrict the kernel to the window and pass to the measurable modification
  have hstep1 : ∀ z ∈ A, ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H (z - p)‖ₑ ≤
      ∫⁻ p, kB p * ‖H' (z - p)‖ₑ := by
    intro z hz
    have hshift : (fun p : Vec3 × ℝ => H (z - p)) =ᵐ[volume] fun p => H' (z - p) :=
      ((volume : Measure (Vec3 × ℝ)).measurePreserving_sub_left z).quasiMeasurePreserving.ae_eq_comp
        hHH'
    calc
      ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H (z - p)‖ₑ ≤
          ∫⁻ p, kB p * ‖H (z - p)‖ₑ := by
        apply lintegral_mono
        intro p
        dsimp only
        rw [enorm_mul]
        by_cases hp : p ∈ B
        · simp only [kB, indicator_of_mem hp]
          exact le_rfl
        · by_cases hHp : H (z - p) = 0
          · simp [hHp]
          · have hpos := hsupp _ hHp
            have hp2 : ¬ (0 < p.2 ∧ p.2 ≤ τ) := fun h => hp ⟨mem_univ _, h⟩
            have hz2 : z.2 < τ := hz.2.2
            have hlt : p.2 < z.2 := by
              simp only [Prod.snd_sub, sub_pos] at hpos
              exact hpos
            have hnonpos : p.2 ≤ 0 := by
              by_contra hne
              exact hp2 ⟨lt_of_not_ge hne, (hlt.trans hz2).le⟩
            simp [heatKernelSpaceDerivative, not_lt.mpr hnonpos]
      _ = ∫⁻ p, kB p * ‖H' (z - p)‖ₑ := by
        apply lintegral_congr_ae
        filter_upwards [hshift] with p hp
        rw [hp]
  -- step 2: the outer integral
  have hswapm : AEMeasurable (Function.uncurry fun (z p : Vec3 × ℝ) =>
      a z * (kB p * ‖H' (z - p)‖ₑ)) (volume.prod volume) := by
    refine Measurable.aemeasurable ?_
    exact (ham.comp measurable_fst).mul ((hkBm.comp measurable_snd).mul
      (hh'm.comp (measurable_fst.sub measurable_snd)))
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).2 (by norm_num)
  have hnormH : eLpNorm H 2 volume = (∫⁻ z, ‖H' z‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_congr_ae hHH', eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num)
      (by norm_num) hH'.aestronglyMeasurable]
    norm_num
  have hholder (p : Vec3 × ℝ) : ∫⁻ z, a z * ‖H' (z - p)‖ₑ ≤ Ia * eLpNorm H 2 volume := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj ham.aemeasurable
      (hh'm.comp (measurable_id.sub_const p)).aemeasurable
    rw [hnormH]
    refine h.trans (le_of_eq ?_)
    congr 2
    exact lintegral_sub_right_eq_self (fun z => ‖H' z‖ₑ ^ (2 : ℝ)) p
  calc
    ∫⁻ z in A, ENNReal.ofReal (forcedHeatWeight z.1) *
        ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H (z - p)‖ₑ ≤
        ∫⁻ z, a z * ∫⁻ p, kB p * ‖H' (z - p)‖ₑ := by
      rw [← lintegral_indicator hA]
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ A
      · simp only [a, indicator_of_mem hz]
        exact mul_le_mul_right (hstep1 z hz) _
      · simp [a, hz]
    _ = ∫⁻ z, ∫⁻ p, a z * (kB p * ‖H' (z - p)‖ₑ) := by
      congr 1
      funext z
      rw [lintegral_const_mul' _ _ (by simp [a, indicator]; split_ifs <;> simp)]
    _ = ∫⁻ p, ∫⁻ z, a z * (kB p * ‖H' (z - p)‖ₑ) := lintegral_lintegral_swap hswapm
    _ = ∫⁻ p, kB p * ∫⁻ z, a z * ‖H' (z - p)‖ₑ := by
      congr 1
      funext p
      rw [← lintegral_const_mul' _ _ (by simp [kB, indicator]; split_ifs <;> simp)]
      congr 1
      funext z
      ring
    _ ≤ ∫⁻ p, kB p * (Ia * eLpNorm H 2 volume) :=
      lintegral_mono fun p => mul_le_mul_right (hholder p) _
    _ = IK * Ia * eLpNorm H 2 volume := by
      rw [lintegral_mul_const _ hkBm, mul_assoc]

end ESS

end
