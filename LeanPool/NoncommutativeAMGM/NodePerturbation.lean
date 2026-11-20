/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.RoundedCosineNodes
public import LeanPool.NoncommutativeAMGM.InterpolationWeights

/-! # Quantitative node-gap perturbations for the rounded interpolation rule -/

@[expose] public section

namespace NoncommutativeAMGM

/-- Perturbing each endpoint by at most `ε` changes its gap by at most `2ε`. -/
theorem node_gap_perturbation {x y t u ε : ℝ}
    (ht : |t - x| ≤ ε) (hu : |u - y| ≤ ε) :
    |(t - u) - (x - y)| ≤ 2 * ε := by
  calc
    _ = |(t - x) - (u - y)| := by congr 1; ring
    _ ≤ |t - x| + |u - y| := abs_sub _ _
    _ ≤ _ := by linarith

/-- Relative gap stability, in the form used in equation (24). -/
theorem node_gap_ratio_lower {x y t u ε : ℝ} (hxy : x ≠ y)
    (ht : |t - x| ≤ ε) (hu : |u - y| ≤ ε) :
    1 - 2 * ε / |x - y| ≤ |(t - u) / (x - y)| := by
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have he := node_gap_perturbation ht hu
  have hab := abs_sub_abs_le_abs_sub (x - y) (t - u)
  rw [abs_sub_comm (x - y) (t - u)] at hab
  rw [abs_div]
  apply (le_div_iff₀ hd).mpr
  have hcancel : (1 - 2 * ε / |x - y|) * |x - y| = |x - y| - 2 * ε := by
    field_simp
  rw [hcancel]
  linarith

/-- The quadratic cosine gap, with the same expression for either index order. -/
theorem chebyshevNode_abs_gap {m j l : ℕ} (hm : 0 < m) (hj : j ≤ m) (hl : l ≤ m) :
    2 / (m : ℝ) ^ 2 * ((j : ℝ) - l) ^ 2 ≤
      |chebyshevNode m j - chebyshevNode m l| := by
  rcases le_total j l with hjl | hlj
  · have h := chebyshevNode_gap hm hjl hl
    have he : ((l : ℝ) - j) ^ 2 = ((j : ℝ) - l) ^ 2 := by ring
    rw [he] at h
    exact h.trans (le_abs_self _)
  · have h := chebyshevNode_gap hm hlj hj
    rw [abs_sub_comm]
    exact h.trans (le_abs_self _)

/-- Distinct cosine nodes have a strictly positive gap. -/
theorem chebyshevNode_ne {m j l : ℕ} (hm : 0 < m) (hj : j ≤ m) (hl : l ≤ m)
    (hjl : j ≠ l) : chebyshevNode m j ≠ chebyshevNode m l := by
  have hdiff : (j : ℝ) - l ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjl)
  have hpos : 0 < 2 / (m : ℝ) ^ 2 * ((j : ℝ) - l) ^ 2 := by positivity
  have h := hpos.trans_le (chebyshevNode_abs_gap hm hj hl)
  exact sub_ne_zero.mp (abs_pos.mp h)

/-- Equation (24): a rounded gap loses at most `m²/(n|j-l|²)` relatively. -/
theorem roundedCosineNode_gap_ratio {n m j l : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hj : j ≤ m) (hl : l ≤ m) (hjl : j ≠ l) :
    1 - (m : ℝ) ^ 2 / ((n : ℝ) * ((j : ℝ) - l) ^ 2) ≤
      |(roundedCosineNode n m j - roundedCosineNode n m l) /
        (chebyshevNode m j - chebyshevNode m l)| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hdiff : (j : ℝ) - l ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjl)
  have hs : 0 < ((j : ℝ) - l) ^ 2 := sq_pos_of_ne_zero hdiff
  have hnode := chebyshevNode_ne hm hj hl hjl
  have hd : 0 < |chebyshevNode m j - chebyshevNode m l| :=
    abs_pos.mpr (sub_ne_zero.mpr hnode)
  have hgap := chebyshevNode_abs_gap hm hj hl
  have hbound : 2 * (1 / (n : ℝ)) /
      |chebyshevNode m j - chebyshevNode m l| ≤
        (m : ℝ) ^ 2 / ((n : ℝ) * ((j : ℝ) - l) ^ 2) := by
    apply (div_le_div_iff₀ hd (mul_pos hn' hs)).mpr
    have h := mul_le_mul_of_nonneg_left hgap (sq_nonneg (m : ℝ))
    have hc : (m : ℝ) ^ 2 * (2 / (m : ℝ) ^ 2 * ((j : ℝ) - l) ^ 2) =
        2 * ((j : ℝ) - l) ^ 2 := by field_simp
    rw [hc] at h
    have he : 2 * (1 / (n : ℝ)) * ((n : ℝ) * ((j : ℝ) - l) ^ 2) =
        2 * ((j : ℝ) - l) ^ 2 := by field_simp
    rw [he]
    exact h
  have hratio := node_gap_ratio_lower hnode (roundedCosineNode_error hn m j)
    (roundedCosineNode_error hn m l)
  linarith

/-- A lower exponential bound for the relative gap loss. -/
theorem exp_neg_two_mul_le_one_sub {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hy : 0 < 1 - x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hy
  have hlow : -2 * x ≤ 1 - (1 - x)⁻¹ := by
    apply (le_sub_iff_add_le).mpr
    have hmul : (1 - x)⁻¹ ≤ 1 + 2 * x := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hy).mpr
      nlinarith [mul_nonneg hx (sub_nonneg.mpr hxhalf)]
    linarith
  calc
    _ ≤ Real.exp (Real.log (1 - x)) := Real.exp_le_exp.mpr (hlow.trans hlog)
    _ = _ := Real.exp_log hy

/-- The square of the difference of distinct natural indices is at least one. -/
theorem nat_cast_gap_sq {j l : ℕ} (hjl : j ≠ l) : 1 ≤ ((j : ℝ) - l) ^ 2 := by
  rcases lt_or_gt_of_ne hjl with h | h
  · have hc : (j : ℝ) + 1 ≤ l := by exact_mod_cast (show j + 1 ≤ l by omega)
    nlinarith
  · have hc : (l : ℝ) + 1 ≤ j := by exact_mod_cast (show l + 1 ≤ j by omega)
    nlinarith

/-- The relative loss parameter is at most one quarter under the paper's threshold. -/
theorem roundedCosineNode_loss_le_quarter {n m j l : ℕ} (hm : 0 < m)
    (hn : 4 * m ^ 2 ≤ n) (hjl : j ≠ l) :
    (m : ℝ) ^ 2 / ((n : ℝ) * ((j : ℝ) - l) ^ 2) ≤ 1 / 4 := by
  have hn0 : 0 < n := by nlinarith [sq_pos_of_pos hm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR : 4 * (m : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
  have hs := nat_cast_gap_sq hjl
  apply (div_le_iff₀ (mul_pos hn' (by linarith))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hs hn'.le]

/-- The exponential gap-ratio lower bound immediately following equation (24). -/
theorem roundedCosineNode_gap_ratio_exp {n m j l : ℕ} (hm : 0 < m)
    (hn : 4 * m ^ 2 ≤ n) (hj : j ≤ m) (hl : l ≤ m) (hjl : j ≠ l) :
    Real.exp (-(2 * (m : ℝ) ^ 2 / ((n : ℝ) * ((j : ℝ) - l) ^ 2))) ≤
      |(roundedCosineNode n m j - roundedCosineNode n m l) /
        (chebyshevNode m j - chebyshevNode m l)| := by
  have hn0 : 0 < n := by nlinarith [sq_pos_of_pos hm]
  have hquarter := roundedCosineNode_loss_le_quarter hm hn hjl
  have hexp := exp_neg_two_mul_le_one_sub
    (show 0 ≤ (m : ℝ) ^ 2 / ((n : ℝ) * ((j : ℝ) - l) ^ 2) by positivity)
    (show (m : ℝ) ^ 2 / ((n : ℝ) * ((j : ℝ) - l) ^ 2) ≤ 1 / 2 by linarith)
  have he : -2 * ((m : ℝ) ^ 2 / ((n : ℝ) * ((j : ℝ) - l) ^ 2)) =
      -(2 * (m : ℝ) ^ 2 / ((n : ℝ) * ((j : ℝ) - l) ^ 2)) := by ring
  rw [he] at hexp
  exact hexp.trans (roundedCosineNode_gap_ratio hn0 hm hj hl hjl)

end NoncommutativeAMGM
