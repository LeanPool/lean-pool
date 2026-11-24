/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian

/-!
# Compact finiteness and compactly supported tests for smooth Monge–Ampère measures
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder ENNReal

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

private theorem continuousOn_realHessian {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (a b : ComplexModel n) :
    ContinuousOn (fun z ↦ realHessian u z a b) U := by
  have h2 : ContinuousOn (iteratedFDeriv ℝ 2 u) U :=
    ContinuousOn.continuousOn_iteratedFDeriv hu U.isOpen
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change ContinuousOn (fun z ↦ iteratedFDeriv ℝ 2 u z ![a, b]) U
  exact (continuous_eval_const ![a, b]).comp_continuousOn h2

private theorem continuousOn_smoothDensity {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ContinuousOn (smoothDensity u) U := by
  have hH (j k : Fin n) : ContinuousOn (fun z ↦ complexHessian u z j k) U := by
    have h00 := continuousOn_realHessian hu (coordinateVector j) (coordinateVector k)
    have hII := continuousOn_realHessian hu
      (Complex.I • coordinateVector j) (Complex.I • coordinateVector k)
    have h0I := continuousOn_realHessian hu
      (coordinateVector j) (Complex.I • coordinateVector k)
    have hI0 := continuousOn_realHessian hu
      (Complex.I • coordinateVector j) (coordinateVector k)
    have ha : ContinuousOn (fun z ↦
        ((realHessian u z (coordinateVector j) (coordinateVector k) +
          realHessian u z (Complex.I • coordinateVector j)
            (Complex.I • coordinateVector k) : ℝ) : ℂ)) U :=
      Complex.continuous_ofReal.comp_continuousOn (h00.add hII)
    have hb : ContinuousOn (fun z ↦
        ((realHessian u z (coordinateVector j) (Complex.I • coordinateVector k) -
          realHessian u z (Complex.I • coordinateVector j)
            (coordinateVector k) : ℝ) : ℂ)) U :=
      Complex.continuous_ofReal.comp_continuousOn (h0I.sub hI0)
    unfold complexHessian
    exact (ha.div_const 4).add
      (((continuousOn_const : ContinuousOn (fun _ : ComplexModel n ↦ Complex.I) U).mul
        hb).div_const 4)
  have hmat : ContinuousOn (complexHessian u) U :=
    continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦ hH j k
  have hdet : ContinuousOn (fun z ↦ (complexHessian u z).det) U :=
    continuous_id.matrix_det.comp_continuousOn hmat
  have hre : ContinuousOn (fun z ↦ (complexHessian u z).det.re) U :=
    Complex.continuous_re.comp_continuousOn hdet
  unfold smoothDensity
  exact (continuousOn_const.mul hre)

theorem smoothMeasure_finiteOnCompacts {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn U u)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ U) :
    smoothMeasure U u hu K < ⊤ := by
  have hcontK : ContinuousOn (smoothDensity u) K :=
    (continuousOn_smoothDensity hu.1).mono hKU
  have hint : Integrable (smoothDensity u) (volume.restrict K) :=
    hcontK.integrableOn_compact hK
  have hnonneg : 0 ≤ᵐ[volume.restrict K] smoothDensity u := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact smoothDensity_nonneg (hu.2.2 z (hKU hz))
  have hlintegral :
      ∫⁻ z, ENNReal.ofReal (smoothDensity u z) ∂(volume.restrict K) ≠ (⊤ : ℝ≥0∞) :=
    (lintegral_ofReal_ne_top_iff_integrable hint.aestronglyMeasurable hnonneg).2 hint
  unfold smoothMeasure
  rw [withDensity_apply _ hK.measurableSet,
    Measure.restrict_restrict_of_subset hKU]
  exact lt_top_iff_ne_top.2 hlintegral

theorem smoothMeasure_test_integral {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn U u)
    (φ : ComplexModel n → ℝ) (hφ : Continuous φ) (hK : HasCompactSupport φ)
    (hU : tsupport φ ⊆ U) :
    Integrable φ (smoothMeasure U u hu) ∧
      Integrable (fun z => φ z * smoothDensity u z)
        (volume.restrict (U : Set (ComplexModel n))) ∧
      (∫ z, φ z ∂(smoothMeasure U u hu)) =
        ∫ z in U, φ z * smoothDensity u z := by
  let μU : Measure (ComplexModel n) := volume.restrict (U : Set (ComplexModel n))
  let w : ComplexModel n → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (smoothDensity u z)
  have hw : AEMeasurable w μU := by
    exact ((continuousOn_smoothDensity hu.1).aemeasurable
      U.isOpen.measurableSet).ennreal_ofReal
  have hwtop : ∀ᵐ z ∂μU, w z < (⊤ : ℝ≥0∞) := by
    exact ae_of_all _ fun z ↦ ENNReal.ofReal_lt_top
  have hwreal : ∀ᵐ z ∂μU, (w z).toReal = smoothDensity u z := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with z hz
    exact smoothMeasure_weight_toReal U u hu hz
  have hprodK : IntegrableOn (fun z ↦ φ z * smoothDensity u z) (tsupport φ) :=
    (hφ.continuousOn.mul ((continuousOn_smoothDensity hu.1).mono hU)).integrableOn_compact hK
  have hprodU : IntegrableOn (fun z ↦ φ z * smoothDensity u z) U :=
    hprodK.of_forall_sdiff_eq_zero U.isOpen.measurableSet fun z hz ↦ by
      have hzero : φ z = 0 := by
        by_contra hne
        exact hz.2 (subset_tsupport φ hne)
      simp [hzero]
  have hweighted : Integrable (fun z ↦ (w z).toReal • φ z) μU := by
    refine hprodU.congr ?_
    filter_upwards [hwreal] with z hz
    simp only [hz, smul_eq_mul]
    rw [mul_comm]
  have hφmeasure : Integrable φ (smoothMeasure U u hu) := by
    change Integrable φ (μU.withDensity w)
    exact (integrable_withDensity_iff_integrable_smul₀' hw hwtop).2 hweighted
  refine ⟨hφmeasure, hprodU, ?_⟩
  change (∫ z, φ z ∂(μU.withDensity w)) =
    ∫ z, φ z * smoothDensity u z ∂μU
  rw [integral_withDensity_eq_integral_toReal_smul₀ hw hwtop]
  apply integral_congr_ae
  filter_upwards [hwreal] with z hz
  simp only [hz, smul_eq_mul]
  rw [mul_comm]

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
