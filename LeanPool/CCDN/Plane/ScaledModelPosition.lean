/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ScaledHomogenization
public import LeanPool.CCDN.Plane.LeadingPositionHeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.CCDN.Plane.HomogeneousLeadingCoefficient

/-!
Positioning a scaled homogeneous model while retaining a coefficient bound
for the original affine equation and the full scaling gain in its height.

A monotone scaled logarithmic-height ratio. A lower bound for the scaled
model height yields the saving needed to change the box exponent 2/d to 1/d.
-/

@[expose] public section
namespace CCDN
open Real

private lemma log_height_ratio_antitone {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (1 + v) / Real.exp v ≤ (1 + u) / Real.exp u := by
  have he : 1 + (v - u) ≤ Real.exp (v - u) := by
    simpa only [add_comm] using Real.add_one_le_exp (v - u)
  have hh : 1 + v ≤ (1 + u) * Real.exp (v - u) := by
    have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + u by linarith)
    nlinarith [mul_nonneg hu (sub_nonneg.mpr huv)]
  apply (div_le_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)).mpr
  have hp := mul_le_mul_of_nonneg_right hh (Real.exp_pos u).le
  rw [mul_assoc, ← Real.exp_add, sub_add_cancel] at hp
  exact hp

/-- Eliminate an upper coefficient height in favor of any lower model height,
retaining the exact exponent 1/d² and the position loss exp(T). -/
private theorem positioned_height_ratio_le {d H L Y T : ℝ}
    (hd : 0 < d) (hY : 1 ≤ Y) (hYH : Y ≤ H) (hL : 0 < L)
    (hposition : Real.log H ≤ Real.log L + T * d ^ 2) :
    (1 + Real.log H / d ^ 2) / L ^ (1 / d ^ 2) ≤
      Real.exp T * ((1 + Real.log Y / d ^ 2) / Y ^ (1 / d ^ 2)) := by
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  have hds : 0 < d ^ 2 := by positivity
  have hu : 0 ≤ Real.log Y / d ^ 2 := div_nonneg (Real.log_nonneg hY) hds.le
  have huv : Real.log Y / d ^ 2 ≤ Real.log H / d ^ 2 :=
    div_le_div_of_nonneg_right (Real.log_le_log hY0 hYH) hds.le
  have hmono := log_height_ratio_antitone hu huv
  have hpos : Real.log H / d ^ 2 ≤ Real.log L / d ^ 2 + T := by
    apply (div_le_iff₀ hds).mpr
    field_simp
    nlinarith only [hposition]
  have hexp : Real.exp (Real.log H / d ^ 2) ≤
      Real.exp T * Real.exp (Real.log L / d ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hnum : 0 ≤ 1 + Real.log H / d ^ 2 := by linarith
  have hstep : (1 + Real.log H / d ^ 2) / Real.exp (Real.log L / d ^ 2) ≤
      Real.exp T * ((1 + Real.log H / d ^ 2) / Real.exp (Real.log H / d ^ 2)) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    rw [← mul_div_assoc, div_mul_eq_mul_div]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hexp hnum]
  have hh := hstep.trans (mul_le_mul_of_nonneg_left hmono (Real.exp_pos T).le)
  rw [Real.rpow_def_of_pos hL, Real.rpow_def_of_pos hY0]
  simpa only [mul_one_div] using hh

end CCDN

namespace CCDN
noncomputable section
open MvPolynomial Real

private lemma leadingPositionHeightFactor_interpolation_le (d : ℕ) :
    ((d : ℝ) + 1) ^ (2 * (d + 1)) ≤ leadingPositionHeightFactor d := by
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hb : (1 : ℝ) ≤ d + 1 := by linarith
  have h₁ : 1 ≤ ((d : ℝ) + 2) ^ 2 := one_le_pow₀ (by linarith)
  have h₂ : 1 ≤ (2 * (d : ℝ) + 1) ^ d := one_le_pow₀ (by linarith)
  have hp := pow_le_pow_right₀ hb (show 2 * (d + 1) ≤ 4 * (d + 1) by omega)
  unfold leadingPositionHeightFactor
  nlinarith [show 0 ≤ ((d : ℝ) + 1) ^ (4 * (d + 1)) by positivity,
    mul_le_mul_of_nonneg_left h₁ (show 0 ≤ ((d : ℝ) + 1) ^ (4 * (d + 1)) by positivity)]

/-- The chosen height bounds both the original homogeneous coefficients and
the translated chart coefficients, with the same absolute position loss. -/
private theorem exists_translated_model_position {d : ℕ} (hd : 0 < d)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ (a : Fin 2 → ℤ) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧ 1 ≤ H ∧
      CoefficientHeightLE f H ∧
      CoefficientHeightLE (affineChart 2 (homogeneousTranslation ℤ a f)) H ∧
      Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| ≤
        Real.log H ∧
      Real.log H ≤
        Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| +
          14 * (d : ℝ) ^ 2 := by
  obtain ⟨a, ha, hne, hcoeff⟩ := exists_bounded_leading_coefficient_translation f hf hf0
  let L := |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)|
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast Int.one_le_abs hne
  have hP := leadingPositionHeightFactor_one_le d
  have hpos : 0 < leadingPositionHeightFactor d := by linarith
  have hLpos : 0 < L := by linarith
  refine ⟨a, leadingPositionHeightFactor d * L, ha, one_le_mul_of_one_le_of_one_le hP hL,
    ?_, homogeneousTranslation_chart_coefficient_bound f hf a ha hLpos.le hcoeff, ?_, ?_⟩
  · intro m
    exact (hcoeff m).trans (mul_le_mul_of_nonneg_right
      (leadingPositionHeightFactor_interpolation_le d) hLpos.le)
  · apply Real.log_le_log hLpos
    nlinarith
  · rw [Real.log_mul hpos.ne' hLpos.ne']
    have h := leadingPositionHeightFactor_log_le hd
    linarith

/-- The model height is at least h^d and also bounds every original affine
coefficient, even after leading-coefficient positioning of the scaled model. -/
theorem exists_scaled_model_position (f : MvPolynomial (Fin 2) ℤ)
    (hf0 : f ≠ 0) (hd : 0 < f.totalDegree) {h : ℤ} (hh : 1 ≤ h) :
    ∃ (a : Fin 2 → ℤ) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ f.totalDegree) ∧
      1 ≤ H ∧ (h : ℝ) ^ f.totalDegree ≤ H ∧
      CoefficientHeightLE f H ∧
      Real.log |((MonomialOrder.lex.leadingCoeff
        (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f)) : ℤ) : ℝ)| ≤ Real.log H ∧
      Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff
        (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f)) : ℤ) : ℝ)| +
        14 * (f.totalDegree : ℝ) ^ 2 := by
  have hh0 : h ≠ 0 := by omega
  obtain ⟨a, H, ha, hH, hc, _, hlo, hhi⟩ := exists_translated_model_position hd
    (scaledHomogenize f.totalDegree h f) (scaledHomogenize_homogeneous _ _ le_rfl)
    (scaledHomogenize_ne_zero _ hh0 hf0)
  obtain ⟨m, _, hm⟩ := exists_scaledHomogenize_top_coefficient f hf0 hh
  exact ⟨a, H, ha, hH, hm.trans (hc _),
    fun m => (scaledHomogenize_integer_coefficient_lower _ hh f m).trans (hc _), hlo, hhi⟩

/-- The exact height saving obtained from a scaling factor h. -/
theorem scaled_positioned_height_ratio_le {d : ℕ} (hd : 0 < d) {h H L : ℝ}
    (hh : 1 ≤ h) (hH : h ^ d ≤ H) (hL : 0 < L)
    (hposition : Real.log H ≤ Real.log L + 14 * (d : ℝ) ^ 2) :
    (1 + Real.log H / (d : ℝ) ^ 2) / L ^ (1 / (d : ℝ) ^ 2) ≤
      Real.exp 14 * ((1 + Real.log h / d) / h ^ (1 / (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hh0 : 0 < h := by linarith
  have hp : (h ^ d) ^ (1 / (d : ℝ) ^ 2) = h ^ (1 / (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh0.le]
    congr 1
    field_simp
  have he : Real.log (h ^ d) / (d : ℝ) ^ 2 = Real.log h / d := by
    rw [Real.log_pow]
    field_simp
  have ht := positioned_height_ratio_le hdR (one_le_pow₀ hh) hH hL hposition
  rw [hp, he] at ht
  exact ht

end
end CCDN
