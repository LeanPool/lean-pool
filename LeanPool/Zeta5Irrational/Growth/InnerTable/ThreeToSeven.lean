/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Growth.PieceCertificate
import LeanPool.Zeta5Irrational.Growth.TableGen
public import LeanPool.Zeta5Irrational.Growth.TablePrime

/-! # Inner piece formulas on `[3, 7)`

The rational endpoint checks use the floor values and affine coefficients of each piece.
The first proof also realizes the existing equation lemmas for this module.
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
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 70 / 23) (b := 120 / 37) (slope := 49 / 20)
      (offset := -5 / 2) (q := 3) (q' := 0) (μ := 5) (k := 3)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_2 (x : ℝ) (h1 : ((120) / 37 : ℝ) ≤ x) (h2 : x < ((10) / 3 : ℝ)) :
    Ein x (3) = ((283) / 40 : ℝ) * x + ((-35) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 120 / 37) (b := 10 / 3) (slope := 283 / 40)
      (offset := -35 / 2) (q := 3) (q' := 0) (μ := 6) (k := 3)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_3 (x : ℝ) (h1 : ((10) / 3 : ℝ) ≤ x) (h2 : x < ((80) / 23 : ℝ)) :
    Ein x (4) = ((277) / 40 : ℝ) * x + ((-17) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 10 / 3) (b := 80 / 23) (slope := 277 / 40)
      (offset := -17) (q := 3) (q' := 0) (μ := 6) (k := 4)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_4 (x : ℝ) (h1 : ((80) / 23 : ℝ) ≤ x) (h2 : x < ((7) / 2 : ℝ)) :
    Ein x (5) = ((231) / 40 : ℝ) * x + ((-13) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 80 / 23) (b := 7 / 2) (slope := 231 / 40)
      (offset := -13) (q := 3) (q' := 0) (μ := 6) (k := 5)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_5 (x : ℝ) (h1 : ((7) / 2 : ℝ) ≤ x) (h2 : x < ((160) / 43 : ℝ)) :
    Ein x (5) = ((271) / 40 : ℝ) * x + ((-33) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 7 / 2) (b := 160 / 43) (slope := 271 / 40)
      (offset := -33 / 2) (q := 3) (q' := 0) (μ := 6) (k := 5)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_6 (x : ℝ) (h1 : ((160) / 43 : ℝ) ≤ x) (h2 : x < ((140) / 37 : ℝ)) :
    Ein x (5) = ((71) / 20 : ℝ) * x + ((-9) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 160 / 43) (b := 140 / 37) (slope := 71 / 20)
      (offset := -9 / 2) (q := 3) (q' := 0) (μ := 6) (k := 5)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_7 (x : ℝ) (h1 : ((140) / 37 : ℝ) ≤ x) (h2 : x < ((90) / 23 : ℝ)) :
    Ein x (5) = ((27) / 5 : ℝ) * x + ((-23) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 140 / 37) (b := 90 / 23) (slope := 27 / 5)
      (offset := -23 / 2) (q := 3) (q' := 0) (μ := 7) (k := 5)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_8 (x : ℝ) (h1 : ((90) / 23 : ℝ) ≤ x) (h2 : x < (4 : ℝ)) :
    Ein x (6) = ((17) / 4 : ℝ) * x + ((-7) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 90 / 23) (b := 4) (slope := 17 / 4)
      (offset := -7) (q := 3) (q' := 0) (μ := 7) (k := 6)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_9 (x : ℝ) (h1 : (4 : ℝ) ≤ x) (h2 : x < ((160) / 37 : ℝ)) :
    Ein x (6) = ((17) / 5 : ℝ) * x + ((-11) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 4) (b := 160 / 37) (slope := 17 / 5)
      (offset := -11) (q := 4) (q' := 0) (μ := 7) (k := 6)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_10 (x : ℝ) (h1 : ((160) / 37 : ℝ) ≤ x) (h2 : x < ((100) / 23 : ℝ)) :
    Ein x (6) = ((321) / 40 : ℝ) * x + ((-31) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 160 / 37) (b := 100 / 23) (slope := 321 / 40)
      (offset := -31) (q := 4) (q' := 0) (μ := 8) (k := 6)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_11 (x : ℝ) (h1 : ((100) / 23 : ℝ) ≤ x) (h2 : x < ((9) / 2 : ℝ)) :
    Ein x (7) = ((55) / 8 : ℝ) * x + ((-26) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 100 / 23) (b := 9 / 2) (slope := 55 / 8)
      (offset := -26) (q := 4) (q' := 0) (μ := 8) (k := 7)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_12 (x : ℝ) (h1 : ((9) / 2 : ℝ) ≤ x) (h2 : x < ((200) / 43 : ℝ)) :
    Ein x (7) = ((63) / 8 : ℝ) * x + ((-61) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 9 / 2) (b := 200 / 43) (slope := 63 / 8)
      (offset := -61 / 2) (q := 4) (q' := 0) (μ := 8) (k := 7)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_13 (x : ℝ) (h1 : ((200) / 43 : ℝ) ≤ x) (h2 : x < ((110) / 23 : ℝ)) :
    Ein x (7) = ((93) / 20 : ℝ) * x + ((-31) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 200 / 43) (b := 110 / 23) (slope := 93 / 20)
      (offset := -31 / 2) (q := 4) (q' := 0) (μ := 8) (k := 7)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_14 (x : ℝ) (h1 : ((110) / 23 : ℝ) ≤ x) (h2 : x < ((180) / 37 : ℝ)) :
    Ein x (8) = ((7) / 2 : ℝ) * x + ((-10) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 110 / 23) (b := 180 / 37) (slope := 7 / 2)
      (offset := -10) (q := 4) (q' := 0) (μ := 8) (k := 8)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_15 (x : ℝ) (h1 : ((180) / 37 : ℝ) ≤ x) (h2 : x < (5 : ℝ)) :
    Ein x (8) = ((107) / 20 : ℝ) * x + ((-19) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 180 / 37) (b := 5) (slope := 107 / 20)
      (offset := -19) (q := 4) (q' := 0) (μ := 9) (k := 8)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_16 (x : ℝ) (h1 : (5 : ℝ) ≤ x) (h2 : x < ((120) / 23 : ℝ)) :
    Ein x (8) = ((9) / 2 : ℝ) * x + ((-24) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 5) (b := 120 / 23) (slope := 9 / 2)
      (offset := -24) (q := 5) (q' := 0) (μ := 9) (k := 8)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_17 (x : ℝ) (h1 : ((120) / 23 : ℝ) ≤ x) (h2 : x < ((200) / 37 : ℝ)) :
    Ein x (9) = ((67) / 20 : ℝ) * x + ((-18) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 120 / 23) (b := 200 / 37) (slope := 67 / 20)
      (offset := -18) (q := 5) (q' := 0) (μ := 9) (k := 9)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_18 (x : ℝ) (h1 : ((200) / 37 : ℝ) ≤ x) (h2 : x < ((11) / 2 : ℝ)) :
    Ein x (9) = ((319) / 40 : ℝ) * x + ((-43) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 200 / 37) (b := 11 / 2) (slope := 319 / 40)
      (offset := -43) (q := 5) (q' := 0) (μ := 10) (k := 9)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_19 (x : ℝ) (h1 : ((11) / 2 : ℝ) ≤ x) (h2 : x < ((240) / 43 : ℝ)) :
    Ein x (9) = ((359) / 40 : ℝ) * x + ((-97) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 11 / 2) (b := 240 / 43) (slope := 359 / 40)
      (offset := -97 / 2) (q := 5) (q' := 0) (μ := 10) (k := 9)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_20 (x : ℝ) (h1 : ((240) / 43 : ℝ) ≤ x) (h2 : x < ((130) / 23 : ℝ)) :
    Ein x (9) = ((23) / 4 : ℝ) * x + ((-61) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 240 / 43) (b := 130 / 23) (slope := 23 / 4)
      (offset := -61 / 2) (q := 5) (q' := 0) (μ := 10) (k := 9)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_21 (x : ℝ) (h1 : ((130) / 23 : ℝ) ≤ x) (h2 : x < ((220) / 37 : ℝ)) :
    Ein x (10) = ((23) / 5 : ℝ) * x + ((-24) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 130 / 23) (b := 220 / 37) (slope := 23 / 5)
      (offset := -24) (q := 5) (q' := 0) (μ := 10) (k := 10)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_22 (x : ℝ) (h1 : ((220) / 37 : ℝ) ≤ x) (h2 : x < (6 : ℝ)) :
    Ein x (10) = ((129) / 20 : ℝ) * x + ((-35) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 220 / 37) (b := 6) (slope := 129 / 20)
      (offset := -35) (q := 5) (q' := 0) (μ := 11) (k := 10)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_23 (x : ℝ) (h1 : (6 : ℝ) ≤ x) (h2 : x < ((140) / 23 : ℝ)) :
    Ein x (10) = ((28) / 5 : ℝ) * x + ((-41) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 6) (b := 140 / 23) (slope := 28 / 5)
      (offset := -41) (q := 6) (q' := 0) (μ := 11) (k := 10)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_24 (x : ℝ) (h1 : ((140) / 23 : ℝ) ≤ x) (h2 : x < ((240) / 37 : ℝ)) :
    Ein x (11) = ((89) / 20 : ℝ) * x + ((-34) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 140 / 23) (b := 240 / 37) (slope := 89 / 20)
      (offset := -34) (q := 6) (q' := 0) (μ := 11) (k := 11)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_25 (x : ℝ) (h1 : ((240) / 37 : ℝ) ≤ x) (h2 : x < ((13) / 2 : ℝ)) :
    Ein x (11) = ((363) / 40 : ℝ) * x + ((-64) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 240 / 37) (b := 13 / 2) (slope := 363 / 40)
      (offset := -64) (q := 6) (q' := 0) (μ := 12) (k := 11)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_26 (x : ℝ) (h1 : ((13) / 2 : ℝ) ≤ x) (h2 : x < ((280) / 43 : ℝ)) :
    Ein x (11) = ((403) / 40 : ℝ) * x + ((-141) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 13 / 2) (b := 280 / 43) (slope := 403 / 40)
      (offset := -141 / 2) (q := 6) (q' := 0) (μ := 12) (k := 11)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_27 (x : ℝ) (h1 : ((280) / 43 : ℝ) ≤ x) (h2 : x < ((150) / 23 : ℝ)) :
    Ein x (11) = ((137) / 20 : ℝ) * x + ((-99) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 280 / 43) (b := 150 / 23) (slope := 137 / 20)
      (offset := -99 / 2) (q := 6) (q' := 0) (μ := 12) (k := 11)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_28 (x : ℝ) (h1 : ((150) / 23 : ℝ) ≤ x) (h2 : x < ((20) / 3 : ℝ)) :
    Ein x (12) = ((57) / 10 : ℝ) * x + ((-42) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 150 / 23) (b := 20 / 3) (slope := 57 / 10)
      (offset := -42) (q := 6) (q' := 0) (μ := 12) (k := 12)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_29 (x : ℝ) (h1 : ((20) / 3 : ℝ) ≤ x) (h2 : x < ((160) / 23 : ℝ)) :
    Ein x (13) = ((69) / 10 : ℝ) * x + ((-50) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 20 / 3) (b := 160 / 23) (slope := 69 / 10)
      (offset := -50) (q := 6) (q' := 0) (μ := 12) (k := 13)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_30 (x : ℝ) (h1 : ((160) / 23 : ℝ) ≤ x) (h2 : x < (7 : ℝ)) :
    Ein x (14) = ((23) / 4 : ℝ) * x + ((-42) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 160 / 23) (b := 7) (slope := 23 / 4)
      (offset := -42) (q := 6) (q' := 0) (μ := 12) (k := 14)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

end Zeta5Irrational
