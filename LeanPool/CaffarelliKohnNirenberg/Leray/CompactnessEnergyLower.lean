/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeakLower

/-!
# Compactness Energy Lower

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace CKN.Leray

/-- An exact uniform squared-energy bound passes to a weak `L²` limit. -/
theorem lintegral_enorm_sq_le_of_weak_l2_bounded
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} (f : ℕ → α → E) (g : Lp E 2 μ)
    (hf : ∀ k, MemLp (f k) 2 μ)
    (hweak : ∀ w, Tendsto
      (fun k => inner ℝ ((hf k).toLp (f k)) w) atTop
      (nhds (inner ℝ g w)))
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hbound : ∀ k, (∫⁻ x, ‖f k x‖ₑ ^ (2 : ℝ) ∂μ) ≤ B) :
    (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ≤ B := by
  have hpow (h : AEStronglyMeasurable (fun x : α => g x) μ) :
      eLpNorm (fun x => g x) 2 μ ^ (2 : ℝ) =
        ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
    convert eLpNorm_nnreal_pow_eq_lintegral
      (p := (2 : NNReal)) (by norm_num : (2 : NNReal) ≠ 0) h using 1 <;>
      norm_num
  have hsource (k : ℕ) :
      eLpNorm (f k) 2 μ ≤ B ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num) (by norm_num) (hf k).aestronglyMeasurable]
    simpa only [ENNReal.toReal_ofNat] using
      ENNReal.rpow_le_rpow (hbound k) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hroot := eLpNorm_le_of_weak_l2_bounded f g hf hweak
    (B ^ (1 / 2 : ℝ))
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne) hsource
  rw [← hpow (Lp.memLp g).aestronglyMeasurable]
  have hsquare := ENNReal.rpow_le_rpow hroot (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one] using hsquare

end CKN.Leray
