/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.ArccosMargin
public import LeanPool.NoncommutativeAMGM.CosineNodeMargin
public import LeanPool.NoncommutativeAMGM.RoundedCosineNodes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! # The quadratic Chebyshev error at rounded extrema -/

@[expose] public section

namespace NoncommutativeAMGM
open Polynomial

/-- The Chebyshev derivative vanishes at its extrema, giving a quadratic angle error. -/
theorem chebyshev_extremum_taylor {m j : ℕ} (hm : 0 < m) (hj : j ≤ m)
    {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    |(Chebyshev.T ℝ (m : ℤ)).eval t -
      (Chebyshev.T ℝ (m : ℤ)).eval (chebyshevNode m j)| ≤
        (m : ℝ) ^ 2 / 2 * (Real.arccos t - Real.arccos (chebyshevNode m j)) ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
  let θ := (j : ℝ) * Real.pi / m
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  have hθπ : θ ≤ Real.pi := by
    dsimp [θ]
    apply (div_le_iff₀ hm').mpr
    nlinarith [Real.pi_pos]
  have hc : Real.arccos (chebyshevNode m j) = θ := Real.arccos_cos hθ0 hθπ
  let δ := (m : ℝ) * (Real.arccos t - θ)
  have hphase : (m : ℝ) * θ = (j : ℝ) * Real.pi := by dsimp [θ]; field_simp
  have heval := Chebyshev.T_real_cos (Real.arccos t) (m : ℤ)
  rw [Real.cos_arccos ht.1 ht.2] at heval
  have hcos : Real.cos ((m : ℝ) * Real.arccos t) = (-1 : ℝ) ^ j * Real.cos δ := by
    rw [show (m : ℝ) * Real.arccos t = (j : ℝ) * Real.pi + δ by
      dsimp [δ]; nlinarith [hphase], Real.cos_add]
    rw [Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
    ring
  have hcval : (Chebyshev.T ℝ (m : ℤ)).eval (chebyshevNode m j) = (-1 : ℝ) ^ j := by
    simpa only [chebyshevNode, Int.cast_negOnePow_natCast] using
      Chebyshev.eval_T_real_cos_int_mul_pi_div (k := j) hm.ne'
  rw [heval, Int.cast_natCast, hcos, hcval, hc,
    show (-1 : ℝ) ^ j * Real.cos δ - (-1 : ℝ) ^ j =
      (-1 : ℝ) ^ j * (Real.cos δ - 1) by ring, abs_mul]
  simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_of_nonpos (by linarith [Real.cos_le_one δ] : Real.cos δ - 1 ≤ 0)]
  have hbound : 1 - Real.cos δ ≤ δ ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := δ)]
  dsimp [δ] at hbound
  convert hbound using 1 <;> ring

/-- The interior-node error before replacing the sine margin by an index estimate. -/
theorem roundedChebyshev_error_margin {n m j : ℕ} (hm : 0 < m)
    (hn : 4 * m ^ 2 ≤ n) (hj0 : 0 < j) (hjm : j < m) :
    |(Chebyshev.T ℝ (m : ℤ)).eval (roundedCosineNode n m j) -
      (Chebyshev.T ℝ (m : ℤ)).eval (chebyshevNode m j)| ≤
        (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * (1 - chebyshevNode m j ^ 2)) := by
  have hn0 : 0 < n := by nlinarith [sq_pos_of_pos hm]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR : 4 * (m : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
  have hnode := chebyshevNode_margin_interior hm hj0 hjm
  have hpos : 0 < 1 - chebyshevNode m j ^ 2 :=
    (by positivity : 0 < 4 / (m : ℝ) ^ 2).trans_le hnode
  have hε : 4 * (1 / (n : ℝ)) ≤ 1 - chebyshevNode m j ^ 2 := by
    apply le_trans _ hnode
    rw [mul_one_div]
    apply (div_le_div_iff₀ hn' (sq_pos_of_pos hm')).mpr
    nlinarith
  have hangle := arccos_sub_sq_le
    (show chebyshevNode m j ∈ Set.Icc (-1) 1 from
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    (roundedCosineNode_mem hn0 m j) (roundedCosineNode_error hn0 m j) hpos hε
  have h := mul_le_mul_of_nonneg_left hangle (show 0 ≤ (m : ℝ) ^ 2 / 2 by positivity)
  have he : (m : ℝ) ^ 2 / 2 * (2 * (1 / (n : ℝ)) ^ 2 /
      (1 - chebyshevNode m j ^ 2)) =
      (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * (1 - chebyshevNode m j ^ 2)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at h
  exact (chebyshev_extremum_taylor hm hjm.le (roundedCosineNode_mem hn0 m j)).trans h

/-- The paper's final interior-node estimate, with its index-dependent denominator. -/
theorem roundedChebyshev_error {n m j : ℕ} (hm : 0 < m)
    (hn : 4 * m ^ 2 ≤ n) (hj0 : 0 < j) (hjm : j < m) :
    |(Chebyshev.T ℝ (m : ℤ)).eval (roundedCosineNode n m j) -
      (Chebyshev.T ℝ (m : ℤ)).eval (chebyshevNode m j)| ≤
        (m : ℝ) ^ 4 / (4 * (n : ℝ) ^ 2 * ((min j (m - j) : ℕ) : ℝ) ^ 2) := by
  have hn0 : 0 < n := by nlinarith [sq_pos_of_pos hm]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hk : (0 : ℝ) < (min j (m - j) : ℕ) := by
    exact_mod_cast (show 0 < min j (m - j) by omega)
  have hmargin := chebyshevNode_margin hm hjm.le
  have hpos : 0 < 1 - chebyshevNode m j ^ 2 :=
    (by positivity : 0 < 4 / (m : ℝ) ^ 2 * ((min j (m - j) : ℕ) : ℝ) ^ 2).trans_le hmargin
  apply (roundedChebyshev_error_margin hm hn hj0 hjm).trans
  apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hn') hpos) (by positivity)).mpr
  have hnorm : 4 * ((min j (m - j) : ℕ) : ℝ) ^ 2 ≤
      (m : ℝ) ^ 2 * (1 - chebyshevNode m j ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hmargin (sq_nonneg (m : ℝ))
    have he : (m : ℝ) ^ 2 * (4 / (m : ℝ) ^ 2 * ((min j (m - j) : ℕ) : ℝ) ^ 2) =
        4 * ((min j (m - j) : ℕ) : ℝ) ^ 2 := by field_simp
    rwa [he] at h
  convert mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ (m : ℝ) ^ 2 * (n : ℝ) ^ 2 by positivity) using 1 <;> ring

end NoncommutativeAMGM
