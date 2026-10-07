/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsTimeBounds
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Reg Tails Time Energy

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The spatial gradient size is square integrable in time when its
nonnegative spacetime density has finite integral. -/
theorem regTails_timeGradientNorm_sq_integral_bound
    {α : Type} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {B : ℝ} (F : α × ℝ → ℝ)
    (hFmeas : Measurable F)
    (hTotal : 2 * (∫⁻ z, ENNReal.ofReal (F z)
        ∂(μ.prod (volume.restrict (Ioi (0 : ℝ))))) ≤
      ENNReal.ofReal (B ^ (2 : ℕ))) :
    ∀ T : ℝ, 0 < T →
      let g : ℝ → ℝ := fun t => Real.sqrt
        (∫⁻ x, ENNReal.ofReal (F (x, t)) ∂μ).toReal
      MemLp g 2 (volume.restrict (Ioo (0 : ℝ) T)) ∧
        (∫ t in Ioo (0 : ℝ) T, g t ^ (2 : ℕ) ∂volume) ≤ B ^ (2 : ℕ) / 2 ∧
        ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
          (∫⁻ x, ENNReal.ofReal (F (x, t)) ∂μ) ≠ ⊤ := by
  intro T hT
  let μT : Measure ℝ := volume.restrict (Ioo (0 : ℝ) T)
  let μpos : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let H : ℝ → ℝ≥0∞ := fun t => ∫⁻ x, ENNReal.ofReal (F (x, t)) ∂μ
  let g : ℝ → ℝ := fun t => Real.sqrt (H t).toReal
  have hDensity : Measurable (fun z : α × ℝ => ENNReal.ofReal (F z)) :=
    ENNReal.measurable_ofReal.comp hFmeas
  have hDensityCurried : Measurable
      (Function.uncurry fun x t => ENNReal.ofReal (F (x, t))) := by
    convert hDensity using 1
    funext z
    rcases z with ⟨x, t⟩
    rfl
  have hDensityAEMeasurable : AEMeasurable
      (Function.uncurry fun x t => ENNReal.ofReal (F (x, t))) (μ.prod μT) :=
    hDensityCurried.aemeasurable
  have hHmeas : Measurable H := by
    apply Measurable.lintegral_prod_left
    exact hDensity
  have hgmeas : Measurable g := by
    exact Real.continuous_sqrt.measurable.comp (ENNReal.measurable_toReal.comp hHmeas)
  have hprodRestrict : μ.prod μT ≤ μ.prod μpos := by
    apply Measure.prod_mono le_rfl
    apply Measure.restrict_mono_set
    intro t ht
    exact ht.1
  have htotalFinite : (∫⁻ z, ENNReal.ofReal (F z) ∂(μ.prod μpos)) ≠ ⊤ := by
    apply ne_of_lt
    by_contra hnot
    have htop : (∫⁻ z, ENNReal.ofReal (F z) ∂(μ.prod μpos)) = ⊤ :=
      top_unique (not_lt.mp hnot)
    rw [htop] at hTotal
    simp at hTotal
  have hHT : (∫⁻ t, H t ∂μT) ≤
      ∫⁻ z, ENNReal.ofReal (F z) ∂(μ.prod μpos) := by
    calc
      (∫⁻ t, H t ∂μT) =
          ∫⁻ t, ∫⁻ x, ENNReal.ofReal (F (x, t)) ∂μ ∂μT := rfl
      _ = ∫⁻ x, ∫⁻ t, ENNReal.ofReal (F (x, t)) ∂μT ∂μ :=
        (MeasureTheory.lintegral_lintegral_swap
          (μ := μ) (ν := μT) (f := fun x t => ENNReal.ofReal (F (x, t)))
          hDensityAEMeasurable).symm
      _ = ∫⁻ z, ENNReal.ofReal (F z) ∂(μ.prod μT) :=
        (MeasureTheory.lintegral_prod _ hDensityAEMeasurable).symm
      _ ≤ _ := lintegral_mono' hprodRestrict le_rfl
  have hHTle : (∫⁻ t, H t ∂μT) ≤ ENNReal.ofReal (B ^ (2 : ℕ) / 2) := by
    have hHalf : (∫⁻ z, ENNReal.ofReal (F z) ∂(μ.prod μpos)) ≤
        ENNReal.ofReal (B ^ (2 : ℕ)) / 2 := by
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
        (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).2
      simpa [μpos, mul_comm] using hTotal
    calc
      _ ≤ ENNReal.ofReal (B ^ (2 : ℕ)) / 2 := hHT.trans hHalf
      _ = ENNReal.ofReal (B ^ (2 : ℕ) / 2) := by
        have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
        rw [htwo, ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hHfinite : ∀ᵐ t ∂μT, H t ≠ ⊤ := by
    have hae := ae_lt_top hHmeas
      (ne_of_lt (lt_of_le_of_lt hHTle ENNReal.ofReal_lt_top))
    filter_upwards [hae] with t ht
    exact ne_of_lt ht
  have hgSq : (fun t : ℝ => g t ^ (2 : ℕ)) =ᵐ[μT] fun t => (H t).toReal := by
    filter_upwards [] with t
    simp [g, Real.sq_sqrt, ENNReal.toReal_nonneg]
  have hOfRealSq : (fun t : ℝ => ENNReal.ofReal (g t ^ (2 : ℕ))) =ᵐ[μT] H := by
    filter_upwards [hHfinite, hgSq] with t ht hsq
    rw [hsq, ENNReal.ofReal_toReal ht]
  have hlintegralSq : (∫⁻ t, ENNReal.ofReal (g t ^ (2 : ℕ)) ∂μT) ≤
      ENNReal.ofReal (B ^ (2 : ℕ) / 2) := by
    calc
      _ = ∫⁻ t, H t ∂μT := lintegral_congr_ae hOfRealSq
      _ ≤ _ := hHTle
  have hgSqIntegrable : Integrable (fun t : ℝ => g t ^ (2 : ℕ)) μT := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (hgmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => sq_nonneg (g t))).mp
    exact ne_of_lt (lt_of_le_of_lt hlintegralSq ENNReal.ofReal_lt_top)
  have hgMem : MemLp g 2 μT :=
    (memLp_two_iff_integrable_sq hgmeas.aestronglyMeasurable).2 hgSqIntegrable
  have hrealSq : ∫ t, g t ^ (2 : ℕ) ∂μT =
      ((∫⁻ t, ENNReal.ofReal (g t ^ (2 : ℕ)) ∂μT).toReal) := by
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => sq_nonneg (g t))
      (hgmeas.pow_const 2).aestronglyMeasurable
  have hrealBound : (∫ t, g t ^ (2 : ℕ) ∂μT) ≤ B ^ (2 : ℕ) / 2 := by
    rw [hrealSq]
    calc
      (∫⁻ t, ENNReal.ofReal (g t ^ (2 : ℕ)) ∂μT).toReal ≤
          (ENNReal.ofReal (B ^ (2 : ℕ) / 2)).toReal :=
        ENNReal.toReal_mono (ne_of_lt ENNReal.ofReal_lt_top) hlintegralSq
      _ = B ^ (2 : ℕ) / 2 := ENNReal.toReal_ofReal (by positivity)
  have hsetIntegral : (∫ t in Ioo (0 : ℝ) T, g t ^ (2 : ℕ) ∂volume) =
      ∫ t, g t ^ (2 : ℕ) ∂μT := by rfl
  refine ⟨hgMem, ?_, ?_⟩
  · rw [hsetIntegral]
    exact hrealBound
  · exact hHfinite

end CKN.Leray

end
