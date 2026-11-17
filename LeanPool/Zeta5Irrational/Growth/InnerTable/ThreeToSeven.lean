/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Growth.TableGen
public import LeanPool.Zeta5Irrational.Growth.TablePrime

/-! # Inner piece formulas on `[3, 7)`

The floor bounds and minimum/maximum comparisons are reused in the shared count formulas.
Each piece needs only one final polynomial normalization.
-/

@[expose] public section

namespace Zeta5Irrational

theorem inPiece_0 (x : ℝ) (h1 : (3 : ℝ) ≤ x) (h2 : x < ((70) / 23 : ℝ)) :
    Ein x (2) = ((18) / 5 : ℝ) * x + ((-6) : ℝ) := by
  have hq0 : (3 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (3 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (2) (q := 3) (q' := 0) (μ := 5)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (3 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (3 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 3 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 3) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 3 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 3) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 3)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_1 (x : ℝ) (h1 : ((70) / 23 : ℝ) ≤ x) (h2 : x < ((120) / 37 : ℝ)) :
    Ein x (3) = ((49) / 20 : ℝ) * x + ((-5) / 2 : ℝ) := by
  have hq0 : (3 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (3 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (3) (q := 3) (q' := 0) (μ := 5)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (3 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (3 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 3 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 3) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 3 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 3) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 3)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_2 (x : ℝ) (h1 : ((120) / 37 : ℝ) ≤ x) (h2 : x < ((10) / 3 : ℝ)) :
    Ein x (3) = ((283) / 40 : ℝ) * x + ((-35) / 2 : ℝ) := by
  have hq0 : (3 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (3 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (3) (q := 3) (q' := 0) (μ := 6)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (3 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (3 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 3 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 3) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 3) := by linarith only [h1, h2]
  have hmax12 : (((x - 3) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 3)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_3 (x : ℝ) (h1 : ((10) / 3 : ℝ) ≤ x) (h2 : x < ((80) / 23 : ℝ)) :
    Ein x (4) = ((277) / 40 : ℝ) * x + ((-17) : ℝ) := by
  have hq0 : (3 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (3 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (4) (q := 3) (q' := 0) (μ := 6)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (3 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (3 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 3 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 3) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 3) := by linarith only [h1, h2]
  have hmax12 : (((x - 3) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 3)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_4 (x : ℝ) (h1 : ((80) / 23 : ℝ) ≤ x) (h2 : x < ((7) / 2 : ℝ)) :
    Ein x (5) = ((231) / 40 : ℝ) * x + ((-13) : ℝ) := by
  have hq0 : (3 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (3 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (5) (q := 3) (q' := 0) (μ := 6)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (3 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (3 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 3 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 3) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 3) := by linarith only [h1, h2]
  have hmax12 : (((x - 3) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 3)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_5 (x : ℝ) (h1 : ((7) / 2 : ℝ) ≤ x) (h2 : x < ((160) / 43 : ℝ)) :
    Ein x (5) = ((271) / 40 : ℝ) * x + ((-33) / 2 : ℝ) := by
  have hq0 : (3 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (3 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (5) (q := 3) (q' := 0) (μ := 6)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (3 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (3 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 3) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 3) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 3) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 3)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_6 (x : ℝ) (h1 : ((160) / 43 : ℝ) ≤ x) (h2 : x < ((140) / 37 : ℝ)) :
    Ein x (5) = ((71) / 20 : ℝ) * x + ((-9) / 2 : ℝ) := by
  have hq0 : (3 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (3 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (5) (q := 3) (q' := 0) (μ := 6)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (3 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (3 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 3) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 3) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 3) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((3 / 40 * x - 0) + (x - 3)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_7 (x : ℝ) (h1 : ((140) / 37 : ℝ) ≤ x) (h2 : x < ((90) / 23 : ℝ)) :
    Ein x (5) = ((27) / 5 : ℝ) * x + ((-23) / 2 : ℝ) := by
  have hq0 : (3 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (3 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (5) (q := 3) (q' := 0) (μ := 7)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (3 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (3 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 3) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 3) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 3) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((3 / 40 * x - 0) + (x - 3)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_8 (x : ℝ) (h1 : ((90) / 23 : ℝ) ≤ x) (h2 : x < (4 : ℝ)) :
    Ein x (6) = ((17) / 4 : ℝ) * x + ((-7) : ℝ) := by
  have hq0 : (3 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (3 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (6) (q := 3) (q' := 0) (μ := 7)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (3 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (3 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 3) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 3) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 3) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((3 / 40 * x - 0) + (x - 3)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_9 (x : ℝ) (h1 : (4 : ℝ) ≤ x) (h2 : x < ((160) / 37 : ℝ)) :
    Ein x (6) = ((17) / 5 : ℝ) * x + ((-11) : ℝ) := by
  have hq0 : (4 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (4 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (6) (q := 4) (q' := 0) (μ := 7)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (4 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (4 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 4 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 4) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 4 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 4) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 4)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_10 (x : ℝ) (h1 : ((160) / 37 : ℝ) ≤ x) (h2 : x < ((100) / 23 : ℝ)) :
    Ein x (6) = ((321) / 40 : ℝ) * x + ((-31) : ℝ) := by
  have hq0 : (4 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (4 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (6) (q := 4) (q' := 0) (μ := 8)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (4 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (4 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 4 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 4) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 4) := by linarith only [h1, h2]
  have hmax12 : (((x - 4) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 4)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_11 (x : ℝ) (h1 : ((100) / 23 : ℝ) ≤ x) (h2 : x < ((9) / 2 : ℝ)) :
    Ein x (7) = ((55) / 8 : ℝ) * x + ((-26) : ℝ) := by
  have hq0 : (4 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (4 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (7) (q := 4) (q' := 0) (μ := 8)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (4 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (4 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 4 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 4) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 4) := by linarith only [h1, h2]
  have hmax12 : (((x - 4) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 4)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_12 (x : ℝ) (h1 : ((9) / 2 : ℝ) ≤ x) (h2 : x < ((200) / 43 : ℝ)) :
    Ein x (7) = ((63) / 8 : ℝ) * x + ((-61) / 2 : ℝ) := by
  have hq0 : (4 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (4 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (7) (q := 4) (q' := 0) (μ := 8)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (4 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (4 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 4) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 4) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 4) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 4)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_13 (x : ℝ) (h1 : ((200) / 43 : ℝ) ≤ x) (h2 : x < ((110) / 23 : ℝ)) :
    Ein x (7) = ((93) / 20 : ℝ) * x + ((-31) / 2 : ℝ) := by
  have hq0 : (4 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (4 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (7) (q := 4) (q' := 0) (μ := 8)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (4 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (4 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 4) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 4) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 4) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((3 / 40 * x - 0) + (x - 4)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_14 (x : ℝ) (h1 : ((110) / 23 : ℝ) ≤ x) (h2 : x < ((180) / 37 : ℝ)) :
    Ein x (8) = ((7) / 2 : ℝ) * x + ((-10) : ℝ) := by
  have hq0 : (4 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (4 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (8) (q := 4) (q' := 0) (μ := 8)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (4 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (4 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 4) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 4) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 4) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((3 / 40 * x - 0) + (x - 4)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_15 (x : ℝ) (h1 : ((180) / 37 : ℝ) ≤ x) (h2 : x < (5 : ℝ)) :
    Ein x (8) = ((107) / 20 : ℝ) * x + ((-19) : ℝ) := by
  have hq0 : (4 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (4 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (8) (q := 4) (q' := 0) (μ := 9)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (4 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (4 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 4) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 4) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 4) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((3 / 40 * x - 0) + (x - 4)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_16 (x : ℝ) (h1 : (5 : ℝ) ≤ x) (h2 : x < ((120) / 23 : ℝ)) :
    Ein x (8) = ((9) / 2 : ℝ) * x + ((-24) : ℝ) := by
  have hq0 : (5 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (5 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (8) (q := 5) (q' := 0) (μ := 9)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (5 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (5 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 5 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 5) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 5 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 5) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 5)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_17 (x : ℝ) (h1 : ((120) / 23 : ℝ) ≤ x) (h2 : x < ((200) / 37 : ℝ)) :
    Ein x (9) = ((67) / 20 : ℝ) * x + ((-18) : ℝ) := by
  have hq0 : (5 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (5 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (9) (q := 5) (q' := 0) (μ := 9)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (5 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (5 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 5 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 5) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 5 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 5) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 5)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_18 (x : ℝ) (h1 : ((200) / 37 : ℝ) ≤ x) (h2 : x < ((11) / 2 : ℝ)) :
    Ein x (9) = ((319) / 40 : ℝ) * x + ((-43) : ℝ) := by
  have hq0 : (5 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (5 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (9) (q := 5) (q' := 0) (μ := 10)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (5 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (5 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 5 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 5) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 5) := by linarith only [h1, h2]
  have hmax12 : (((x - 5) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 5)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_19 (x : ℝ) (h1 : ((11) / 2 : ℝ) ≤ x) (h2 : x < ((240) / 43 : ℝ)) :
    Ein x (9) = ((359) / 40 : ℝ) * x + ((-97) / 2 : ℝ) := by
  have hq0 : (5 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (5 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (9) (q := 5) (q' := 0) (μ := 10)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (5 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (5 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 5) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 5) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 5) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 5)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_20 (x : ℝ) (h1 : ((240) / 43 : ℝ) ≤ x) (h2 : x < ((130) / 23 : ℝ)) :
    Ein x (9) = ((23) / 4 : ℝ) * x + ((-61) / 2 : ℝ) := by
  have hq0 : (5 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (5 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (9) (q := 5) (q' := 0) (μ := 10)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (5 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (5 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 5) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 5) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 5) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((3 / 40 * x - 0) + (x - 5)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_21 (x : ℝ) (h1 : ((130) / 23 : ℝ) ≤ x) (h2 : x < ((220) / 37 : ℝ)) :
    Ein x (10) = ((23) / 5 : ℝ) * x + ((-24) : ℝ) := by
  have hq0 : (5 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (5 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (10) (q := 5) (q' := 0) (μ := 10)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (5 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (5 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 5) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 5) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 5) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((3 / 40 * x - 0) + (x - 5)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_22 (x : ℝ) (h1 : ((220) / 37 : ℝ) ≤ x) (h2 : x < (6 : ℝ)) :
    Ein x (10) = ((129) / 20 : ℝ) * x + ((-35) : ℝ) := by
  have hq0 : (5 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (5 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (10) (q := 5) (q' := 0) (μ := 11)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (5 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (5 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 5) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 5) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 5) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((3 / 40 * x - 0) + (x - 5)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_23 (x : ℝ) (h1 : (6 : ℝ) ≤ x) (h2 : x < ((140) / 23 : ℝ)) :
    Ein x (10) = ((28) / 5 : ℝ) * x + ((-41) : ℝ) := by
  have hq0 : (6 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (6 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (10) (q := 6) (q' := 0) (μ := 11)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (6 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (6 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 6 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 6) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 6 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 6) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 6)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_24 (x : ℝ) (h1 : ((140) / 23 : ℝ) ≤ x) (h2 : x < ((240) / 37 : ℝ)) :
    Ein x (11) = ((89) / 20 : ℝ) * x + ((-34) : ℝ) := by
  have hq0 : (6 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (6 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (11) (q := 6) (q' := 0) (μ := 11)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (6 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (6 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 6 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 6) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 6 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 6) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 6)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_25 (x : ℝ) (h1 : ((240) / 37 : ℝ) ≤ x) (h2 : x < ((13) / 2 : ℝ)) :
    Ein x (11) = ((363) / 40 : ℝ) * x + ((-64) : ℝ) := by
  have hq0 : (6 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (6 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (11) (q := 6) (q' := 0) (μ := 12)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (6 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (6 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 6 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 6) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 6) := by linarith only [h1, h2]
  have hmax12 : (((x - 6) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 6)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_26 (x : ℝ) (h1 : ((13) / 2 : ℝ) ≤ x) (h2 : x < ((280) / 43 : ℝ)) :
    Ein x (11) = ((403) / 40 : ℝ) * x + ((-141) / 2 : ℝ) := by
  have hq0 : (6 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (6 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (11) (q := 6) (q' := 0) (μ := 12)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (6 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (6 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 6) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 6) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 6) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 6)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_27 (x : ℝ) (h1 : ((280) / 43 : ℝ) ≤ x) (h2 : x < ((150) / 23 : ℝ)) :
    Ein x (11) = ((137) / 20 : ℝ) * x + ((-99) / 2 : ℝ) := by
  have hq0 : (6 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (6 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (11) (q := 6) (q' := 0) (μ := 12)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (6 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (6 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 6) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 6) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 6) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((3 / 40 * x - 0) + (x - 6)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_28 (x : ℝ) (h1 : ((150) / 23 : ℝ) ≤ x) (h2 : x < ((20) / 3 : ℝ)) :
    Ein x (12) = ((57) / 10 : ℝ) * x + ((-42) : ℝ) := by
  have hq0 : (6 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (6 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (12) (q := 6) (q' := 0) (μ := 12)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (6 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (6 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 6) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 6) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 6) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((3 / 40 * x - 0) + (x - 6)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_left hmin01, cc02 hg1,
    max_eq_left hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_29 (x : ℝ) (h1 : ((20) / 3 : ℝ) ≤ x) (h2 : x < ((160) / 23 : ℝ)) :
    Ein x (13) = ((69) / 10 : ℝ) * x + ((-50) : ℝ) := by
  have hq0 : (6 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (6 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (13) (q := 6) (q' := 0) (μ := 12)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (6 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (6 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 6) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 6) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 6) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 6)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_30 (x : ℝ) (h1 : ((160) / 23 : ℝ) ≤ x) (h2 : x < (7 : ℝ)) :
    Ein x (14) = ((23) / 4 : ℝ) * x + ((-42) : ℝ) := by
  have hq0 : (6 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (6 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (14) (q := 6) (q' := 0) (μ := 12)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (6 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (6 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 6) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 6) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 6) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 6)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_right hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

end Zeta5Irrational
