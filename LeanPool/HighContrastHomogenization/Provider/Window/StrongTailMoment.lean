/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.PsiShellIntegral
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# High-contrast homogenization: Provider.Window.StrongTailMoment

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace IndependentSums

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Interval

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An integer moment from a tail with the extra inverse power. -/
theorem lintegral_rpow_le_of_strongPsiTail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {B : ℝ} {W : Ω → ℝ} (N : ℕ)
    (hN : 1 ≤ N) (hB : 2 ≤ B) (hGrowth : HasPsiGrowth Ψ B)
    (hAdmissible : AdmissiblePsi Ψ) (hWm : AEMeasurable W μ)
    (hW0 : ∀ ω, 0 ≤ W ω)
    (htail : ∀ ⦃t : ℝ⦄, 1 ≤ t → μ.real {ω | t < W ω} ≤ (t * Ψ t)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (W ω ^ (N : ℝ)) ∂μ ≤
      ENNReal.ofReal
        (1 + 2 * (N : ℝ) * (1 + Real.log B) * B ^ natTriangular N) := by
  let n : ℕ := N - 1
  let G : ℝ → ℝ≥0∞ := fun t => μ {ω | t < W ω} *
    ENNReal.ofReal (t ^ ((N : ℝ) - 1))
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hLayer := lintegral_rpow_eq_lintegral_meas_lt_mul
    (μ := μ) (Eventually.of_forall hW0) hWm hNpos
  have hsplit :
      ∫⁻ t in Ioi 0, G t ∂volume =
        (∫⁻ t in Ioc 0 1, G t ∂volume) + ∫⁻ t in Ioi 1, G t ∂volume := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    exact lintegral_union measurableSet_Ioi
      (disjoint_left.2 fun t ht0 ht1 => not_lt_of_ge ht0.2 ht1)
  have hlow : ∫⁻ t in Ioc 0 1, G t ∂volume ≤ ENNReal.ofReal ((N : ℝ)⁻¹) := by
    let F : ℝ → ℝ := fun t => t ^ (N - 1)
    have hdom : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), G t ≤ ENNReal.ofReal (F t) := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall ?_
      intro t ht
      have hmeasure : μ {ω | t < W ω} ≤ 1 := by
        calc
          μ {ω | t < W ω} ≤ μ univ := measure_mono (subset_univ _)
          _ = 1 := by simp
      have hexp : (N : ℝ) - 1 = (N - 1 : ℕ) := by
        exact_mod_cast (show (N : ℤ) - 1 = (N - 1 : ℕ) by omega)
      calc
        G t = μ {ω | t < W ω} * ENNReal.ofReal (t ^ ((N : ℝ) - 1)) := rfl
        _ ≤ 1 * ENNReal.ofReal (t ^ ((N : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right hmeasure (by positivity)
        _ = ENNReal.ofReal (F t) := by rw [one_mul]; simp only [F, hexp, Real.rpow_natCast]
    have hFint : IntegrableOn F (Ioc (0 : ℝ) 1) := by
      exact (continuous_pow (N - 1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hF0 : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), 0 ≤ F t := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => pow_nonneg ht.1.le _
    calc
      ∫⁻ t in Ioc 0 1, G t ∂volume ≤
          ∫⁻ t in Ioc 0 1, ENNReal.ofReal (F t) ∂volume := lintegral_mono_ae hdom
      _ = ENNReal.ofReal (∫ t in Ioc 0 1, F t ∂volume) :=
        (ofReal_integral_eq_lintegral_ofReal hFint hF0).symm
      _ = ENNReal.ofReal ((N : ℝ)⁻¹) := by
        congr 1
        change (∫ t in Ioc 0 1, t ^ (N - 1) ∂volume) = (N : ℝ)⁻¹
        rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
          integral_pow, Nat.sub_add_cancel hN, Nat.cast_sub hN]
        norm_num
        rw [zero_pow (Nat.ne_of_gt (Nat.zero_lt_of_lt hN)), sub_zero, one_div]
  have hhigh : ∫⁻ t in Ioi 1, G t ∂volume ≤
      ENNReal.ofReal (2 * (1 + Real.log B) * B ^ natTriangular N) := by
    have hdom : ∀ᵐ t ∂volume.restrict (Ioi (1 : ℝ)), G t ≤
        ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall ?_
      intro t ht
      have htpos : 0 < t := zero_lt_one.trans ht
      have hψ : 0 < Ψ t := lt_of_lt_of_le zero_lt_one (hAdmissible.2 htpos.le)
      have hreal := htail ht.le
      have hmeasure : μ {ω | t < W ω} ≤ ENNReal.ofReal ((t * Ψ t)⁻¹) := by
        have heq : μ {ω | t < W ω} = ENNReal.ofReal (μ.real {ω | t < W ω}) := by
          rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _)]
        rw [heq]
        exact ENNReal.ofReal_le_ofReal hreal
      calc
        G t ≤ ENNReal.ofReal ((t * Ψ t)⁻¹) *
            ENNReal.ofReal (t ^ ((N : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right hmeasure (by positivity)
        _ = ENNReal.ofReal ((t * Ψ t)⁻¹ * t ^ ((N : ℝ) - 1)) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_pos htpos hψ).le)]
        _ = ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) := by
          congr 1
          rw [div_eq_mul_inv]
          have hncast : (n : ℝ) = (N : ℝ) - 1 := by
            dsimp only [n]
            exact_mod_cast (show (N - 1 : ℤ) = (N : ℤ) - 1 by omega)
          rw [hncast]
          have hrpow : t ^ ((N : ℝ) - 1) =
              t * t ^ ((N : ℝ) - 2) := by
            calc
              t ^ ((N : ℝ) - 1) = t ^ (1 + ((N : ℝ) - 2)) := by
                congr 1
                ring
              _ = t ^ (1 : ℝ) * t ^ ((N : ℝ) - 2) := by rw [Real.rpow_add htpos]
              _ = t * t ^ ((N : ℝ) - 2) := by rw [Real.rpow_one]
          rw [hrpow]
          field_simp [htpos.ne', hψ.ne']
          congr 1
          ring
    exact (lintegral_mono_ae hdom).trans (by
      simpa only [n, Nat.sub_add_cancel hN] using
        lintegral_rpow_div_psi_le (N - 1) hB hGrowth hAdmissible)
  have hC0 : 0 ≤ 2 * (1 + Real.log B) * B ^ natTriangular N := by
    have hlog : 0 ≤ Real.log B := Real.log_nonneg (one_le_two.trans hB)
    positivity
  have hNinv : 0 ≤ ((N : ℝ)⁻¹) := inv_nonneg.mpr hNpos.le
  have hcombine :
      ENNReal.ofReal (N : ℝ) *
          (ENNReal.ofReal ((N : ℝ)⁻¹) +
            ENNReal.ofReal (2 * (1 + Real.log B) * B ^ natTriangular N)) =
        ENNReal.ofReal
          (1 + 2 * (N : ℝ) * (1 + Real.log B) * B ^ natTriangular N) := by
    rw [← ENNReal.ofReal_add hNinv hC0, ← ENNReal.ofReal_mul hNpos.le]
    congr 1
    field_simp [hNpos.ne']
  calc
    ∫⁻ ω, ENNReal.ofReal (W ω ^ (N : ℝ)) ∂μ =
        ENNReal.ofReal (N : ℝ) * ∫⁻ t in Ioi 0, G t ∂volume := by
      simpa only [G] using hLayer
    _ = ENNReal.ofReal (N : ℝ) *
        ((∫⁻ t in Ioc 0 1, G t ∂volume) + ∫⁻ t in Ioi 1, G t ∂volume) := by rw [hsplit]
    _ ≤ ENNReal.ofReal (N : ℝ) *
        (ENNReal.ofReal ((N : ℝ)⁻¹) +
          ENNReal.ofReal (2 * (1 + Real.log B) * B ^ natTriangular N)) := by
      gcongr
    _ = ENNReal.ofReal
        (1 + 2 * (N : ℝ) * (1 + Real.log B) * B ^ natTriangular N) := hcombine

end
end IndependentSums
end HCPolySupport
