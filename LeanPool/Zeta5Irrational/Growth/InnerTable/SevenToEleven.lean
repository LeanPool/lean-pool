/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Growth.TableGen
public import LeanPool.Zeta5Irrational.Growth.TablePrime

/-! # Inner piece formulas on `[7, 11)`

The floor bounds and minimum/maximum comparisons are reused in the shared count formulas.
Each piece needs only one final polynomial normalization.
-/

@[expose] public section

namespace Zeta5Irrational

theorem inPiece_31 (x : ℝ) (h1 : (7 : ℝ) ≤ x) (h2 : x < ((260) / 37 : ℝ)) :
    Ein x (14) = ((49) / 10 : ℝ) * x + ((-49) : ℝ) := by
  have hq0 : (7 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (7 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (14) (q := 7) (q' := 0) (μ := 12)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (7 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (7 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 7 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 7) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 7 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 7) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 7)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_32 (x : ℝ) (h1 : ((260) / 37 : ℝ) ≤ x) (h2 : x < ((170) / 23 : ℝ)) :
    Ein x (14) = ((27) / 4 : ℝ) * x + ((-62) : ℝ) := by
  have hq0 : (7 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (7 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (14) (q := 7) (q' := 0) (μ := 13)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (7 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (7 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 7 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 7) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 7 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 7) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 7)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_33 (x : ℝ) (h1 : ((170) / 23 : ℝ) ≤ x) (h2 : x < ((320) / 43 : ℝ)) :
    Ein x (15) = ((28) / 5 : ℝ) * x + ((-107) / 2 : ℝ) := by
  have hq0 : (7 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (7 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (15) (q := 7) (q' := 0) (μ := 13)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (7 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (7 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 7 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 7) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 7 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 7) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 7)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_34 (x : ℝ) (h1 : ((320) / 43 : ℝ) ≤ x) (h2 : x < ((15) / 2 : ℝ)) :
    Ein x (15) = ((19) / 8 : ℝ) * x + ((-59) / 2 : ℝ) := by
  have hq0 : (7 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (7 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (15) (q := 7) (q' := 0) (μ := 13)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (7 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (7 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 7 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 7) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 7 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((x - 7) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 7)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_35 (x : ℝ) (h1 : ((15) / 2 : ℝ) ≤ x) (h2 : x < ((280) / 37 : ℝ)) :
    Ein x (15) = ((27) / 8 : ℝ) * x + ((-37) : ℝ) := by
  have hq0 : (7 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (7 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (15) (q := 7) (q' := 0) (μ := 13)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (7 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (7 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 7) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 7) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (x - 7 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 7)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_36 (x : ℝ) (h1 : ((280) / 37 : ℝ) ≤ x) (h2 : x < ((180) / 23 : ℝ)) :
    Ein x (15) = (8 : ℝ) * x + ((-72) : ℝ) := by
  have hq0 : (7 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (7 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (15) (q := 7) (q' := 0) (μ := 14)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (7 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (7 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 7) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 7) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 7) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 7)) - 1) := by linarith only [h1, h2]
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

theorem inPiece_37 (x : ℝ) (h1 : ((180) / 23 : ℝ) ≤ x) (h2 : x < (8 : ℝ)) :
    Ein x (16) = ((137) / 20 : ℝ) * x + ((-63) : ℝ) := by
  have hq0 : (7 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (7 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (16) (q := 7) (q' := 0) (μ := 14)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (7 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (7 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 7) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 7) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 7) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 7)) - 1) := by linarith only [h1, h2]
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

theorem inPiece_38 (x : ℝ) (h1 : (8 : ℝ) ≤ x) (h2 : x < ((300) / 37 : ℝ)) :
    Ein x (16) = (6 : ℝ) * x + ((-71) : ℝ) := by
  have hq0 : (8 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (8 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (16) (q := 8) (q' := 0) (μ := 14)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (8 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (8 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 8 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 8) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 8 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 8) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 8)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_39 (x : ℝ) (h1 : ((300) / 37 : ℝ) ≤ x) (h2 : x < ((190) / 23 : ℝ)) :
    Ein x (16) = ((157) / 20 : ℝ) * x + ((-86) : ℝ) := by
  have hq0 : (8 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (8 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (16) (q := 8) (q' := 0) (μ := 15)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (8 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (8 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 8 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 8) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 8 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 8) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 8)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_40 (x : ℝ) (h1 : ((190) / 23 : ℝ) ≤ x) (h2 : x < ((360) / 43 : ℝ)) :
    Ein x (17) = ((67) / 10 : ℝ) * x + ((-153) / 2 : ℝ) := by
  have hq0 : (8 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (8 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (17) (q := 8) (q' := 0) (μ := 15)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (8 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (8 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 8 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 8) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 8 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 8) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 8)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_41 (x : ℝ) (h1 : ((360) / 43 : ℝ) ≤ x) (h2 : x < ((17) / 2 : ℝ)) :
    Ein x (17) = ((139) / 40 : ℝ) * x + ((-99) / 2 : ℝ) := by
  have hq0 : (8 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (8 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (17) (q := 8) (q' := 0) (μ := 15)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (8 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (8 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 8 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 8) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 8 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((x - 8) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 8)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_42 (x : ℝ) (h1 : ((17) / 2 : ℝ) ≤ x) (h2 : x < ((320) / 37 : ℝ)) :
    Ein x (17) = ((179) / 40 : ℝ) * x + ((-58) : ℝ) := by
  have hq0 : (8 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (8 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (17) (q := 8) (q' := 0) (μ := 15)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (8 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (8 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 8) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 8) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (x - 8 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 8)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_43 (x : ℝ) (h1 : ((320) / 37 : ℝ) ≤ x) (h2 : x < ((200) / 23 : ℝ)) :
    Ein x (17) = ((91) / 10 : ℝ) * x + ((-98) : ℝ) := by
  have hq0 : (8 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (8 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (17) (q := 8) (q' := 0) (μ := 16)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (8 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (8 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 8) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 8) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 8) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 8)) - 1) := by linarith only [h1, h2]
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

theorem inPiece_44 (x : ℝ) (h1 : ((200) / 23 : ℝ) ≤ x) (h2 : x < (9 : ℝ)) :
    Ein x (18) = ((159) / 20 : ℝ) * x + ((-88) : ℝ) := by
  have hq0 : (8 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (8 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (18) (q := 8) (q' := 0) (μ := 16)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (8 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (8 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 8) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 8) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 8) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 8)) - 1) := by linarith only [h1, h2]
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

theorem inPiece_45 (x : ℝ) (h1 : (9 : ℝ) ≤ x) (h2 : x < ((210) / 23 : ℝ)) :
    Ein x (18) = ((71) / 10 : ℝ) * x + ((-97) : ℝ) := by
  have hq0 : (9 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (9 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (18) (q := 9) (q' := 0) (μ := 16)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (9 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (9 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 9 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 9) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 9 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 9) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 9)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_46 (x : ℝ) (h1 : ((210) / 23 : ℝ) ≤ x) (h2 : x < ((340) / 37 : ℝ)) :
    Ein x (19) = ((119) / 20 : ℝ) * x + ((-173) / 2 : ℝ) := by
  have hq0 : (9 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (9 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (19) (q := 9) (q' := 0) (μ := 16)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (9 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (9 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 9 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 9) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 9 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 9) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 9)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_47 (x : ℝ) (h1 : ((340) / 37 : ℝ) ≤ x) (h2 : x < ((400) / 43 : ℝ)) :
    Ein x (19) = ((39) / 5 : ℝ) * x + ((-207) / 2 : ℝ) := by
  have hq0 : (9 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (9 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (19) (q := 9) (q' := 0) (μ := 17)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (9 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (9 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 9 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 9) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 9 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 9) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 9)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_48 (x : ℝ) (h1 : ((400) / 43 : ℝ) ≤ x) (h2 : x < ((19) / 2 : ℝ)) :
    Ein x (19) = ((183) / 40 : ℝ) * x + ((-147) / 2 : ℝ) := by
  have hq0 : (9 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (9 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (19) (q := 9) (q' := 0) (μ := 17)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (9 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (9 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 9 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 9) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 9 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((x - 9) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 9)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_49 (x : ℝ) (h1 : ((19) / 2 : ℝ) ≤ x) (h2 : x < ((220) / 23 : ℝ)) :
    Ein x (19) = ((223) / 40 : ℝ) * x + ((-83) : ℝ) := by
  have hq0 : (9 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (9 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (19) (q := 9) (q' := 0) (μ := 17)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (9 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (9 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 9) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 9) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (x - 9 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 9)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_50 (x : ℝ) (h1 : ((220) / 23 : ℝ) ≤ x) (h2 : x < ((360) / 37 : ℝ)) :
    Ein x (20) = ((177) / 40 : ℝ) * x + ((-72) : ℝ) := by
  have hq0 : (9 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (9 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (20) (q := 9) (q' := 0) (μ := 17)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (9 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (9 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 9) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 9) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (x - 9 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 9)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_51 (x : ℝ) (h1 : ((360) / 37 : ℝ) ≤ x) (h2 : x < (10 : ℝ)) :
    Ein x (20) = ((181) / 20 : ℝ) * x + ((-117) : ℝ) := by
  have hq0 : (9 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (9 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (20) (q := 9) (q' := 0) (μ := 18)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (9 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (9 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 9) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 9) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 9) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 9)) - 1) := by linarith only [h1, h2]
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

theorem inPiece_52 (x : ℝ) (h1 : (10 : ℝ) ≤ x) (h2 : x < ((440) / 43 : ℝ)) :
    Ein x (22) = ((69) / 10 : ℝ) * x + ((-114) : ℝ) := by
  have hq0 : (10 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (10 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (22) (q := 10) (q' := 0) (μ := 18)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (10 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (10 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 10 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 10) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 10 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 10) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 10)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_left hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_53 (x : ℝ) (h1 : ((440) / 43 : ℝ) ≤ x) (h2 : x < ((380) / 37 : ℝ)) :
    Ein x (22) = ((147) / 40 : ℝ) * x + ((-81) : ℝ) := by
  have hq0 : (10 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (10 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (22) (q := 10) (q' := 0) (μ := 18)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (10 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (10 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 10 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 10) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 10 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((x - 10) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 10)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_54 (x : ℝ) (h1 : ((380) / 37 : ℝ) ≤ x) (h2 : x < ((240) / 23 : ℝ)) :
    Ein x (22) = ((221) / 40 : ℝ) * x + ((-100) : ℝ) := by
  have hq0 : (10 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (10 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (22) (q := 10) (q' := 0) (μ := 19)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (10 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (10 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 10 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 10) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 10 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((x - 10) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 10)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_55 (x : ℝ) (h1 : ((240) / 23 : ℝ) ≤ x) (h2 : x < ((21) / 2 : ℝ)) :
    Ein x (23) = ((35) / 8 : ℝ) * x + ((-88) : ℝ) := by
  have hq0 : (10 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (10 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (23) (q := 10) (q' := 0) (μ := 19)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (10 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (10 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 10 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 10) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 10 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((x - 10) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 10)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_left hmin10, cc20 hf1, max_eq_left hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_left hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_56 (x : ℝ) (h1 : ((21) / 2 : ℝ) ≤ x) (h2 : x < ((400) / 37 : ℝ)) :
    Ein x (23) = ((43) / 8 : ℝ) * x + ((-197) / 2 : ℝ) := by
  have hq0 : (10 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (10 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (23) (q := 10) (q' := 0) (μ := 19)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (10 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (10 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 10) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 10) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (x - 10 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 10)) - 1) := by linarith only [h1, h2]
  push_cast
  simp only [Fin.sum_univ_three, cc00, cc01 hg0 hg1, min_eq_right hmin01, cc02 hg1,
    max_eq_right hmax02, cc10 hf0 hf1, min_eq_right hmin10, cc20 hf1, max_eq_right hmax20,
    cc11 hf0 hf1 hg0, min_eq_left hmin11, cc12 hg1, max_eq_right hmax12, cc21 hf1,
    max_eq_right hmax21, cc22 hg1]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num only [max_def, ite_true, ite_false]
  ring

theorem inPiece_57 (x : ℝ) (h1 : ((400) / 37 : ℝ) ≤ x) (h2 : x < ((250) / 23 : ℝ)) :
    Ein x (23) = (10 : ℝ) * x + ((-297) / 2 : ℝ) := by
  have hq0 : (10 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (10 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (23) (q := 10) (q' := 0) (μ := 20)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (10 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (10 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 10) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 10) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 10) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 10)) - 1) := by linarith only [h1, h2]
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

theorem inPiece_58 (x : ℝ) (h1 : ((250) / 23 : ℝ) ≤ x) (h2 : x < (11 : ℝ)) :
    Ein x (24) = ((177) / 20 : ℝ) * x + ((-136) : ℝ) := by
  have hq0 : (10 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (10 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (24) (q := 10) (q' := 0) (μ := 20)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (10 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (10 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 10) := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 10) - (1 / 2)) := sub_nonneg.mpr hmin10
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 10) := by linarith only [h1, h2]
  have hmax12 : (0 : ℝ) ≤ (((1 / 2) + (3 / 40 * x - 0)) - 1) := by linarith only [h1, h2]
  have hmax21 : (0 : ℝ) ≤ (((1 / 2) + (x - 10)) - 1) := by linarith only [h1, h2]
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
