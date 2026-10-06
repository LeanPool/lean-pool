/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.PsiShellFinite
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# High-contrast homogenization: Provider.Window.PsiShellIntegral

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace IndependentSums

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Interval

noncomputable section

private theorem central_shell_le {Ψ : ℝ → ℝ} {B : ℝ} (n : ℕ)
    (hB : 2 ≤ B) (hΨ : HasPsiGrowth Ψ B) (hAdmissible : AdmissiblePsi Ψ) :
    ∫⁻ t in Ioc (B ^ n) (B ^ (n + 1)),
        ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume ≤
      ENNReal.ofReal (B ^ natTriangular (n + 1) * Real.log B) := by
  let T : ℕ := natTriangular (n + 1)
  let F : ℝ → ℝ := fun t => B ^ T * t⁻¹
  have hBpos : 0 < B := zero_lt_two.trans_le hB
  have hab : B ^ n ≤ B ^ (n + 1) := pow_le_pow_right₀ (one_le_two.trans hB) (by omega)
  have hdom : ∀ᵐ t ∂volume.restrict (Ioc (B ^ n) (B ^ (n + 1))),
      ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ≤ ENNReal.ofReal (F t) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall ?_
    intro t ht
    have hk := rpow_div_psi_le n n (one_le_two.trans hB) hΨ hAdmissible ht.1.le
    apply ENNReal.ofReal_le_ofReal
    simpa only [F, T, sub_self, zero_sub, Real.rpow_neg_one] using hk
  have hFint : IntegrableOn F (Ioc (B ^ n) (B ^ (n + 1))) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
    exact (intervalIntegral.intervalIntegrable_inv (f := fun t : ℝ => t)
      (fun t ht => by
        have ht' : t ∈ Icc (B ^ n) (B ^ (n + 1)) := by
          rwa [uIcc_of_le hab] at ht
        exact ne_of_gt ((pow_pos hBpos n).trans_le ht'.1))
      continuous_id.continuousOn).const_mul _
  have hF0 : ∀ᵐ t ∂volume.restrict (Ioc (B ^ n) (B ^ (n + 1))), 0 ≤ F t := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun t ht => mul_nonneg (by positivity)
      (inv_nonneg.mpr (lt_trans (pow_pos hBpos n) ht.1).le)
  have hratio : B ^ (n + 1) / B ^ n = B := by
    rw [pow_succ]
    field_simp [(pow_pos hBpos n).ne']
  calc
    ∫⁻ t in Ioc (B ^ n) (B ^ (n + 1)),
        ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume ≤
        ∫⁻ t in Ioc (B ^ n) (B ^ (n + 1)), ENNReal.ofReal (F t) ∂volume :=
      lintegral_mono_ae hdom
    _ = ENNReal.ofReal (∫ t in Ioc (B ^ n) (B ^ (n + 1)), F t ∂volume) := by
      exact (ofReal_integral_eq_lintegral_ofReal hFint hF0).symm
    _ = ENNReal.ofReal (B ^ T * Real.log B) := by
      congr 1
      rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul,
        integral_inv_of_pos (pow_pos hBpos n)
          (pow_pos hBpos (n + 1)), hratio]
    _ = ENNReal.ofReal (B ^ natTriangular (n + 1) * Real.log B) := by rfl

private theorem tail_shell_le {Ψ : ℝ → ℝ} {B : ℝ} (n : ℕ)
    (hB : 2 ≤ B) (hΨ : HasPsiGrowth Ψ B) (hAdmissible : AdmissiblePsi Ψ) :
    ∫⁻ t in Ioi (B ^ (n + 1)),
        ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume ≤
      ENNReal.ofReal (B ^ natTriangular (n + 1)) := by
  let U : ℕ := natTriangular (n + 2)
  let F : ℝ → ℝ := fun t => B ^ U * t ^ (-2 : ℝ)
  have hBpos : 0 < B := zero_lt_two.trans_le hB
  have hc : 0 < B ^ (n + 1) := pow_pos hBpos _
  have hdom : ∀ᵐ t ∂volume.restrict (Ioi (B ^ (n + 1))),
      ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ≤ ENNReal.ofReal (F t) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall ?_
    intro t ht
    have hk := rpow_div_psi_le n (n + 1) (one_le_two.trans hB)
      hΨ hAdmissible ht.le
    apply ENNReal.ofReal_le_ofReal
    have hexp : (n : ℝ) - ((n + 1 : ℕ) : ℝ) - 1 = -2 := by norm_num
    simpa only [F, U, hexp] using hk
  have hFint : IntegrableOn F (Ioi (B ^ (n + 1))) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc).const_mul _
  have hF0 : ∀ᵐ t ∂volume.restrict (Ioi (B ^ (n + 1))), 0 ≤ F t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun t ht =>
      mul_nonneg (by positivity) (Real.rpow_nonneg (lt_trans hc ht).le _)
  have hpow : B ^ U / B ^ (n + 1) = B ^ natTriangular (n + 1) := by
    have htri : U = natTriangular (n + 1) + (n + 1) := by
      dsimp only [U]
      rw [natTriangular_succ]
    rw [htri, pow_add]
    field_simp [(pow_pos hBpos (n + 1)).ne']
  calc
    ∫⁻ t in Ioi (B ^ (n + 1)),
        ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume ≤
        ∫⁻ t in Ioi (B ^ (n + 1)), ENNReal.ofReal (F t) ∂volume :=
      lintegral_mono_ae hdom
    _ = ENNReal.ofReal (∫ t in Ioi (B ^ (n + 1)), F t ∂volume) := by
      exact (ofReal_integral_eq_lintegral_ofReal hFint hF0).symm
    _ = ENNReal.ofReal (B ^ U / B ^ (n + 1)) := by
      congr 1
      rw [div_eq_mul_inv, integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num) hc]
      norm_num [Real.rpow_neg_one]
    _ = ENNReal.ofReal (B ^ natTriangular (n + 1)) := by rw [hpow]

/-- The shifted gauge tail has the exact natural-shell integral needed for
integer moments. -/
theorem lintegral_rpow_div_psi_le {Ψ : ℝ → ℝ} {B : ℝ} (n : ℕ)
    (hB : 2 ≤ B) (hΨ : HasPsiGrowth Ψ B) (hAdmissible : AdmissiblePsi Ψ) :
    ∫⁻ t in Ioi 1, ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume ≤
      ENNReal.ofReal
        (2 * (1 + Real.log B) * B ^ natTriangular (n + 1)) := by
  let T : ℕ := natTriangular (n + 1)
  have hB1 : 1 ≤ B := one_le_two.trans hB
  have hsplit := lintegral_Ioc_pow_le_shell_sum
    (fun t => ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t)) hB1 (n + 1)
  have hfirst :
      ∫⁻ t in Ioc 1 (B ^ (n + 1)),
          ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume ≤
        ENNReal.ofReal (B ^ T) + ENNReal.ofReal (B ^ T * Real.log B) := by
    calc
      ∫⁻ t in Ioc 1 (B ^ (n + 1)),
          ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume ≤
          ∑ j ∈ Finset.range (n + 1),
            ∫⁻ t in Ioc (B ^ j) (B ^ (j + 1)),
              ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume := hsplit
      _ = (∑ j ∈ Finset.range n,
            ∫⁻ t in Ioc (B ^ j) (B ^ (j + 1)),
              ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume) +
            ∫⁻ t in Ioc (B ^ n) (B ^ (n + 1)),
              ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume := by
        rw [Finset.sum_range_succ]
      _ ≤ ENNReal.ofReal (B ^ T) + ENNReal.ofReal (B ^ T * Real.log B) :=
        add_le_add (lintegral_finite_psi_shells_le n hB hΨ hAdmissible)
          (central_shell_le n hB hΨ hAdmissible)
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hpow0 : 0 ≤ B ^ T := by positivity
  have hpowlog0 : 0 ≤ B ^ T * Real.log B := mul_nonneg hpow0 hlog
  have htotal : B ^ T + B ^ T * Real.log B + B ^ T ≤
      2 * (1 + Real.log B) * B ^ T := by
    calc
      B ^ T + B ^ T * Real.log B + B ^ T =
          2 * B ^ T + B ^ T * Real.log B := by ring
      _ ≤ 2 * B ^ T + B ^ T * Real.log B + B ^ T * Real.log B :=
        le_add_of_nonneg_right hpowlog0
      _ = 2 * (1 + Real.log B) * B ^ T := by ring
  rw [← Ioc_union_Ioi_eq_Ioi (one_le_pow₀ hB1 : 1 ≤ B ^ (n + 1))]
  calc
    ∫⁻ t in Ioc 1 (B ^ (n + 1)) ∪ Ioi (B ^ (n + 1)),
        ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume ≤
        (∫⁻ t in Ioc 1 (B ^ (n + 1)),
          ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume) +
        ∫⁻ t in Ioi (B ^ (n + 1)),
          ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume :=
      lintegral_union_le _ _ _
    _ ≤ (ENNReal.ofReal (B ^ T) + ENNReal.ofReal (B ^ T * Real.log B)) +
          ENNReal.ofReal (B ^ T) :=
      add_le_add hfirst (tail_shell_le n hB hΨ hAdmissible)
    _ = ENNReal.ofReal (B ^ T + B ^ T * Real.log B + B ^ T) := by
      rw [← ENNReal.ofReal_add hpow0 hpowlog0,
        ← ENNReal.ofReal_add (add_nonneg hpow0 hpowlog0) hpow0]
    _ ≤ ENNReal.ofReal (2 * (1 + Real.log B) * B ^ T) :=
      ENNReal.ofReal_le_ofReal htotal
    _ = ENNReal.ofReal
        (2 * (1 + Real.log B) * B ^ natTriangular (n + 1)) := by rfl

end
end IndependentSums
end HCPolySupport
