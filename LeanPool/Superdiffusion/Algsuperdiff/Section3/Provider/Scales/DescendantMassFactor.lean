/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Scales.BaseLoss
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.MultiscaleEllipticity
public import LeanPool.HighContrastHomogenization.Support.Deterministic.MultiscaleQuantitiesBasic.Foundation.Geometric

/-!
# DescendantMassFactor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Descendant-mass aggregation for the corrected Section 3.2 base case

At descendant depth `n`, the retained per-cube mass envelope contributes the
factor `1 + 3 d log(3) n`.  The normalized `q = 2` geometric weights have first
moment at most `2 / s`, so the weighted factor is bounded by `baseLoss d s = 1
+ 6 d log(3) / s`.

The mathematical source role is confined to the scalar aggregation behind ABK26
Proposition `p.base.case`, display `e.basecase.mathcal.E` at label and its
derivation. In particular, this file does not assert the false
global-root-supremum step. -/

open HCPolySupport HCPolySupport.Book
open scoped BigOperators

namespace Algsuperdiff.Section3.Provider.Scales

noncomputable section

/-- The linear loss factor contributed by descendants at depth `n`. -/
noncomputable def descendantMassFactor (d n : ℕ) : ℝ :=
  1 + 3 * (d : ℝ) * Real.log 3 * (n : ℝ)

/-- The descendant-mass factor is strictly positive. -/
theorem descendantMassFactor_pos (d n : ℕ) : 0 < descendantMassFactor d n := by
  rw [descendantMassFactor]
  have hterm : (0 : ℝ) ≤ 3 * (d : ℝ) * Real.log 3 * (n : ℝ) := by
    positivity
  linarith only [hterm]

/-- The common ratio `3 ^ (-2s)` of the `q = 2` scale weights. -/
noncomputable def geometricRatio (s : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (-s * 2)

private theorem geometricRatio_pos (s : ℝ) : 0 < geometricRatio s :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem geometricRatio_lt_one {s : ℝ} (hs : 0 < s) : geometricRatio s < 1 := by
  rw [geometricRatio]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])

/-- The Chapter 2 and deterministic-foundation scale weights agree definitionally. -/
private theorem geometricWeight_eq_foundation (s q : ℝ) (n : ℕ) :
    Ch02.geometricWeight s q n = HCPolySupport.geometricWeight s q n :=
  rfl

private theorem geometricWeight_eq_geometricRatio_pow (s : ℝ) (n : ℕ) :
    Ch02.geometricWeight s 2 n =
      (1 - geometricRatio s) * geometricRatio s ^ n := by
  rw [Ch02.geometricWeight, Ch02.geometricDiscount, geometricRatio]
  simp only [Real.rpow_eq_pow]
  congr 1
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-s * 2)) n,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

private theorem summable_geometricWeight_two {s : ℝ} (hs : 0 < s) :
    Summable (Ch02.geometricWeight s 2) := by
  have hs2 : 0 < s * (2 : ℝ) := mul_pos hs (by norm_num)
  simpa only [geometricWeight_eq_foundation] using!
    (HCPolySupport.summable_geometricWeight (s := s) (q := 2) hs2)

private theorem tsum_geometricWeight_two_eq_one {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, Ch02.geometricWeight s 2 n = 1 := by
  have hs2 : 0 < s * (2 : ℝ) := mul_pos hs (by norm_num)
  simpa only [geometricWeight_eq_foundation] using
    (HCPolySupport.tsum_geometricWeight_eq_one (s := s) (q := 2) hs2)

private theorem summable_geometricWeight_two_mul_natCast {s : ℝ} (hs : 0 < s) :
    Summable fun n : ℕ => Ch02.geometricWeight s 2 n * (n : ℝ) := by
  have hnorm : ‖geometricRatio s‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (geometricRatio_pos s)]
    exact geometricRatio_lt_one hs
  have hsum :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm).mul_left
      (1 - geometricRatio s)
  exact hsum.congr fun n => by
    rw [geometricWeight_eq_geometricRatio_pow]
    ring

private theorem tsum_geometricWeight_two_mul_natCast_eq_ratio {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, Ch02.geometricWeight s 2 n * (n : ℝ) =
      geometricRatio s / (1 - geometricRatio s) := by
  let q : ℝ := geometricRatio s
  have hq0 : 0 ≤ q := by
    exact (geometricRatio_pos s).le
  have hq1 : q < 1 := geometricRatio_lt_one hs
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have heq :
      ∑' n : ℕ, Ch02.geometricWeight s 2 n * (n : ℝ) =
        (1 - q) * ∑' n : ℕ, (n : ℝ) * q ^ n := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by
      rw [geometricWeight_eq_geometricRatio_pow]
      dsimp only [q]
      ring
  rw [heq, tsum_coe_mul_geometric_of_norm_lt_one hnorm]
  have hqdiff : 0 < 1 - q := sub_pos.mpr hq1
  dsimp only [q] at hqdiff ⊢
  field_simp

private theorem geometricRatio_le_one_sub_half {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    geometricRatio s ≤ 1 - s / 2 := by
  have hlog : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
      (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have hratio_exp : geometricRatio s = Real.exp (Real.log 3 * (-s * 2)) := by
    rw [geometricRatio]
    exact Real.rpow_def_of_pos (by norm_num) _
  have hexponent : Real.log 3 * (-s * 2) ≤ -(2 * s) := by
    calc
      Real.log 3 * (-s * 2) ≤ 1 * (-s * 2) :=
        mul_le_mul_of_nonpos_right hlog.le (by linarith only [hs])
      _ = -(2 * s) := by ring
  have hexp : Real.exp (Real.log 3 * (-s * 2)) ≤ Real.exp (-(2 * s)) :=
    Real.exp_le_exp.mpr hexponent
  have hone_add_pos : (0 : ℝ) < 1 + 2 * s := by
    linarith only [hs]
  have hexp_inv : Real.exp (-(2 * s)) ≤ (1 + 2 * s)⁻¹ := by
    rw [Real.exp_neg]
    have hone_add_le_exp : 1 + 2 * s ≤ Real.exp (2 * s) := by
      have hbasic := Real.add_one_le_exp (2 * s)
      linarith only [hbasic]
    exact inv_anti₀ hone_add_pos hone_add_le_exp
  have hproduct : (1 : ℝ) ≤ (1 - s / 2) * (1 + 2 * s) := by
    nlinarith only [hs, hs1]
  have hinv_le : (1 + 2 * s)⁻¹ ≤ 1 - s / 2 := by
    have hinv_nonneg : (0 : ℝ) ≤ (1 + 2 * s)⁻¹ := inv_nonneg.mpr hone_add_pos.le
    calc
      (1 + 2 * s)⁻¹ = 1 * (1 + 2 * s)⁻¹ := (one_mul _).symm
      _ ≤ ((1 - s / 2) * (1 + 2 * s)) * (1 + 2 * s)⁻¹ :=
        mul_le_mul_of_nonneg_right hproduct hinv_nonneg
      _ = 1 - s / 2 := by field_simp
  rw [hratio_exp]
  exact hexp.trans (hexp_inv.trans hinv_le)

private theorem tsum_geometricWeight_two_mul_natCast_le
    (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    ∑' n : ℕ, Ch02.geometricWeight (s : ℝ) 2 n * (n : ℝ) ≤ 2 / (s : ℝ) := by
  obtain ⟨hs, hs1⟩ := Set.mem_Ioo.mp s.2
  let q : ℝ := geometricRatio (s : ℝ)
  have hq0 : 0 ≤ q := by
    exact (geometricRatio_pos (s : ℝ)).le
  have hq1 : q < 1 := geometricRatio_lt_one hs
  have hqdiff : 0 < 1 - q := sub_pos.mpr hq1
  rw [tsum_geometricWeight_two_mul_natCast_eq_ratio hs]
  have hhalf : (s : ℝ) / 2 ≤ 1 - q := by
    have hratio := geometricRatio_le_one_sub_half hs hs1.le
    change geometricRatio (s : ℝ) ≤ 1 - (s : ℝ) / 2 at hratio
    change (s : ℝ) / 2 ≤ 1 - q
    dsimp only [q]
    linarith only [hratio]
  have hratio_le : q / (1 - q) ≤ 1 / (1 - q) := by
    rw [div_eq_mul_inv, one_div]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hq1.le (inv_nonneg.mpr hqdiff.le)
  have hinv_le : 1 / (1 - q) ≤ 1 / ((s : ℝ) / 2) :=
    one_div_le_one_div_of_le (by positivity) hhalf
  calc
    q / (1 - q) ≤ 1 / (1 - q) := hratio_le
    _ ≤ 1 / ((s : ℝ) / 2) := hinv_le
    _ = 2 / (s : ℝ) := one_div_div (s : ℝ) 2

/-- The normalized `q = 2` geometric weights make the descendant-mass factors summable. -/
theorem summable_geometricWeight_mul_descendantMassFactor
    (d : ℕ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Summable fun n : ℕ =>
      Ch02.geometricWeight (s : ℝ) 2 n * descendantMassFactor d n := by
  have hs : (0 : ℝ) < (s : ℝ) := (Set.mem_Ioo.mp s.2).1
  have hweight := summable_geometricWeight_two hs
  have hmoment := summable_geometricWeight_two_mul_natCast hs
  refine (hweight.add
    (hmoment.mul_left (3 * (d : ℝ) * Real.log 3))).congr fun n => ?_
  rw [descendantMassFactor]
  ring

/-- Exact collapse of the weighted descendant-mass factors through the first moment. -/
theorem tsum_geometricWeight_mul_descendantMassFactor_eq
    (d : ℕ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    ∑' n : ℕ, Ch02.geometricWeight (s : ℝ) 2 n * descendantMassFactor d n =
      1 + (3 * (d : ℝ) * Real.log 3) *
        (Real.rpow 3 (-(s : ℝ) * 2) / (1 - Real.rpow 3 (-(s : ℝ) * 2))) := by
  have hs : (0 : ℝ) < (s : ℝ) := (Set.mem_Ioo.mp s.2).1
  have hweight := summable_geometricWeight_two hs
  have hmoment := summable_geometricWeight_two_mul_natCast hs
  have hsplit :
      (fun n : ℕ =>
        Ch02.geometricWeight (s : ℝ) 2 n * descendantMassFactor d n) =
      fun n => Ch02.geometricWeight (s : ℝ) 2 n +
        (3 * (d : ℝ) * Real.log 3) *
          (Ch02.geometricWeight (s : ℝ) 2 n * (n : ℝ)) := by
    funext n
    rw [descendantMassFactor]
    ring
  rw [hsplit, Summable.tsum_add hweight (hmoment.mul_left _), tsum_mul_left,
    tsum_geometricWeight_two_eq_one hs,
    tsum_geometricWeight_two_mul_natCast_eq_ratio hs, geometricRatio]

/-- The exact weighted factor is bounded by the adopted Option-A base loss. -/
theorem tsum_geometricWeight_mul_descendantMassFactor_le_baseLoss
    (d : ℕ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    ∑' n : ℕ, Ch02.geometricWeight (s : ℝ) 2 n * descendantMassFactor d n ≤
      baseLoss d s := by
  rw [tsum_geometricWeight_mul_descendantMassFactor_eq, baseLoss_eq]
  have hcoefficient : (0 : ℝ) ≤ 3 * (d : ℝ) * Real.log 3 := by
    positivity
  have hmoment := tsum_geometricWeight_two_mul_natCast_le s
  rw [tsum_geometricWeight_two_mul_natCast_eq_ratio (Set.mem_Ioo.mp s.2).1] at hmoment
  rw [geometricRatio] at hmoment
  calc
    1 + (3 * (d : ℝ) * Real.log 3) *
          (Real.rpow 3 (-(s : ℝ) * 2) / (1 - Real.rpow 3 (-(s : ℝ) * 2)))
        ≤ 1 + (3 * (d : ℝ) * Real.log 3) * (2 / (s : ℝ)) :=
      by
        simpa only [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_left hmoment hcoefficient) 1
    _ = 1 + 6 * (d : ℝ) * Real.log 3 / (s : ℝ) := by ring

end

end Algsuperdiff.Section3.Provider.Scales
