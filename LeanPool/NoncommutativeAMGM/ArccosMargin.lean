/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # Quantitative inverse-cosine stability away from the endpoints -/

@[expose] public section

namespace NoncommutativeAMGM

/-- A positive lower bound for `1-u²` controls the inverse cosine on the full segment. -/
theorem arccos_sub_le_of_margin {c t a : ℝ} (ha : 0 < a)
    (hmargin : ∀ u ∈ Set.uIcc c t, a ≤ 1 - u ^ 2) :
    |Real.arccos t - Real.arccos c| ≤ (1 / Real.sqrt a) * |t - c| := by
  have hf (u : ℝ) (hu : u ∈ Set.uIcc c t) :
      HasDerivWithinAt Real.arccos (-(1 / Real.sqrt (1 - u ^ 2))) (Set.uIcc c t) u := by
    have h := hmargin u hu
    apply (Real.hasDerivAt_arccos (by intro he; rw [he] at h; norm_num at h; linarith)
      (by intro he; rw [he] at h; norm_num at h; linarith)).hasDerivWithinAt
  have hb (u : ℝ) (hu : u ∈ Set.uIcc c t) :
      ‖-(1 / Real.sqrt (1 - u ^ 2))‖ ≤ 1 / Real.sqrt a := by
    have hm := hmargin u hu
    have hs := Real.sqrt_le_sqrt hm
    simp only [Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (show 0 ≤ 1 / Real.sqrt (1 - u ^ 2) by positivity)]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr ha) hs
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hb (convex_uIcc c t)
      Set.left_mem_uIcc Set.right_mem_uIcc

/-- A small displacement from an interior point preserves half its squared sine margin. -/
theorem square_margin_on_segment {c t ε : ℝ}
    (hc : c ∈ Set.Icc (-1) 1) (ht : t ∈ Set.Icc (-1) 1)
    (he : |t - c| ≤ ε) (hmargin : 4 * ε ≤ 1 - c ^ 2) :
    ∀ u ∈ Set.uIcc c t, (1 - c ^ 2) / 2 ≤ 1 - u ^ 2 := by
  intro u hu
  have hu' : u ∈ Set.Icc (-1) 1 := (convex_Icc (-1 : ℝ) 1).ordConnected.uIcc_subset hc ht hu
  have huc : |u - c| ≤ |t - c| := by
    rcases le_total c t with hct | htc
    · rw [Set.uIcc_of_le hct] at hu
      rw [abs_of_nonneg (sub_nonneg.mpr hu.1), abs_of_nonneg (sub_nonneg.mpr hct)]
      linarith [hu.2]
    · rw [Set.uIcc_of_ge htc] at hu
      rw [abs_of_nonpos (sub_nonpos.mpr hu.2), abs_of_nonpos (sub_nonpos.mpr htc)]
      linarith [hu.1]
  have hsum : |u + c| ≤ 2 :=
    abs_le.mpr ⟨by linarith [hu'.1, hc.1], by linarith [hu'.2, hc.2]⟩
  have hdiff : |u ^ 2 - c ^ 2| ≤ 2 * ε := by
    calc
      _ = |u - c| * |u + c| := by rw [← abs_mul]; congr 1; ring
      _ ≤ ε * 2 := mul_le_mul (huc.trans he) hsum
        (abs_nonneg _) (by have := abs_nonneg (t - c); linarith)
      _ = _ := by ring
  have h := (abs_le.mp hdiff).2
  linarith

/-- Squared inverse-cosine error, with the factor two used in the paper. -/
theorem arccos_sub_sq_le {c t ε : ℝ}
    (hc : c ∈ Set.Icc (-1) 1) (ht : t ∈ Set.Icc (-1) 1)
    (he : |t - c| ≤ ε) (hpos : 0 < 1 - c ^ 2) (hmargin : 4 * ε ≤ 1 - c ^ 2) :
    (Real.arccos t - Real.arccos c) ^ 2 ≤ 2 * ε ^ 2 / (1 - c ^ 2) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans he
  have ha : 0 < (1 - c ^ 2) / 2 := by positivity
  have h := arccos_sub_le_of_margin ha (square_margin_on_segment hc ht he hmargin)
  have hb : |Real.arccos t - Real.arccos c| ≤ (1 / Real.sqrt ((1 - c ^ 2) / 2)) * ε :=
    h.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hs := mul_self_le_mul_self (abs_nonneg _) hb
  rw [← pow_two, sq_abs, ← pow_two, mul_pow, one_div_pow,
    Real.sq_sqrt ha.le] at hs
  convert hs using 1
  field_simp

end NoncommutativeAMGM
