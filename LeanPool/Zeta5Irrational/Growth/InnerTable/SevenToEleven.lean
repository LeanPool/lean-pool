/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Growth.PieceCertificate
import LeanPool.Zeta5Irrational.Growth.TableGen
public import LeanPool.Zeta5Irrational.Growth.TablePrime

/-! # Inner piece formulas on `[7, 11)`

The rational endpoint checks use the floor values and affine coefficients of each piece.
The first proof also realizes the existing equation lemmas for this module.
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
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 260 / 37) (b := 170 / 23) (slope := 27 / 4)
      (offset := -62) (q := 7) (q' := 0) (μ := 13) (k := 14)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_33 (x : ℝ) (h1 : ((170) / 23 : ℝ) ≤ x) (h2 : x < ((320) / 43 : ℝ)) :
    Ein x (15) = ((28) / 5 : ℝ) * x + ((-107) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 170 / 23) (b := 320 / 43) (slope := 28 / 5)
      (offset := -107 / 2) (q := 7) (q' := 0) (μ := 13) (k := 15)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_34 (x : ℝ) (h1 : ((320) / 43 : ℝ) ≤ x) (h2 : x < ((15) / 2 : ℝ)) :
    Ein x (15) = ((19) / 8 : ℝ) * x + ((-59) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 320 / 43) (b := 15 / 2) (slope := 19 / 8)
      (offset := -59 / 2) (q := 7) (q' := 0) (μ := 13) (k := 15)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_35 (x : ℝ) (h1 : ((15) / 2 : ℝ) ≤ x) (h2 : x < ((280) / 37 : ℝ)) :
    Ein x (15) = ((27) / 8 : ℝ) * x + ((-37) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 15 / 2) (b := 280 / 37) (slope := 27 / 8)
      (offset := -37) (q := 7) (q' := 0) (μ := 13) (k := 15)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_36 (x : ℝ) (h1 : ((280) / 37 : ℝ) ≤ x) (h2 : x < ((180) / 23 : ℝ)) :
    Ein x (15) = (8 : ℝ) * x + ((-72) : ℝ) := by
  simpa only [Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 280 / 37) (b := 180 / 23) (slope := 8)
      (offset := -72) (q := 7) (q' := 0) (μ := 14) (k := 15)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_37 (x : ℝ) (h1 : ((180) / 23 : ℝ) ≤ x) (h2 : x < (8 : ℝ)) :
    Ein x (16) = ((137) / 20 : ℝ) * x + ((-63) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 180 / 23) (b := 8) (slope := 137 / 20)
      (offset := -63) (q := 7) (q' := 0) (μ := 14) (k := 16)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_38 (x : ℝ) (h1 : (8 : ℝ) ≤ x) (h2 : x < ((300) / 37 : ℝ)) :
    Ein x (16) = (6 : ℝ) * x + ((-71) : ℝ) := by
  simpa only [Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 8) (b := 300 / 37) (slope := 6)
      (offset := -71) (q := 8) (q' := 0) (μ := 14) (k := 16)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_39 (x : ℝ) (h1 : ((300) / 37 : ℝ) ≤ x) (h2 : x < ((190) / 23 : ℝ)) :
    Ein x (16) = ((157) / 20 : ℝ) * x + ((-86) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 300 / 37) (b := 190 / 23) (slope := 157 / 20)
      (offset := -86) (q := 8) (q' := 0) (μ := 15) (k := 16)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_40 (x : ℝ) (h1 : ((190) / 23 : ℝ) ≤ x) (h2 : x < ((360) / 43 : ℝ)) :
    Ein x (17) = ((67) / 10 : ℝ) * x + ((-153) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 190 / 23) (b := 360 / 43) (slope := 67 / 10)
      (offset := -153 / 2) (q := 8) (q' := 0) (μ := 15) (k := 17)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_41 (x : ℝ) (h1 : ((360) / 43 : ℝ) ≤ x) (h2 : x < ((17) / 2 : ℝ)) :
    Ein x (17) = ((139) / 40 : ℝ) * x + ((-99) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 360 / 43) (b := 17 / 2) (slope := 139 / 40)
      (offset := -99 / 2) (q := 8) (q' := 0) (μ := 15) (k := 17)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_42 (x : ℝ) (h1 : ((17) / 2 : ℝ) ≤ x) (h2 : x < ((320) / 37 : ℝ)) :
    Ein x (17) = ((179) / 40 : ℝ) * x + ((-58) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 17 / 2) (b := 320 / 37) (slope := 179 / 40)
      (offset := -58) (q := 8) (q' := 0) (μ := 15) (k := 17)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_43 (x : ℝ) (h1 : ((320) / 37 : ℝ) ≤ x) (h2 : x < ((200) / 23 : ℝ)) :
    Ein x (17) = ((91) / 10 : ℝ) * x + ((-98) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 320 / 37) (b := 200 / 23) (slope := 91 / 10)
      (offset := -98) (q := 8) (q' := 0) (μ := 16) (k := 17)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_44 (x : ℝ) (h1 : ((200) / 23 : ℝ) ≤ x) (h2 : x < (9 : ℝ)) :
    Ein x (18) = ((159) / 20 : ℝ) * x + ((-88) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 200 / 23) (b := 9) (slope := 159 / 20)
      (offset := -88) (q := 8) (q' := 0) (μ := 16) (k := 18)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_45 (x : ℝ) (h1 : (9 : ℝ) ≤ x) (h2 : x < ((210) / 23 : ℝ)) :
    Ein x (18) = ((71) / 10 : ℝ) * x + ((-97) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 9) (b := 210 / 23) (slope := 71 / 10)
      (offset := -97) (q := 9) (q' := 0) (μ := 16) (k := 18)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_46 (x : ℝ) (h1 : ((210) / 23 : ℝ) ≤ x) (h2 : x < ((340) / 37 : ℝ)) :
    Ein x (19) = ((119) / 20 : ℝ) * x + ((-173) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 210 / 23) (b := 340 / 37) (slope := 119 / 20)
      (offset := -173 / 2) (q := 9) (q' := 0) (μ := 16) (k := 19)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_47 (x : ℝ) (h1 : ((340) / 37 : ℝ) ≤ x) (h2 : x < ((400) / 43 : ℝ)) :
    Ein x (19) = ((39) / 5 : ℝ) * x + ((-207) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 340 / 37) (b := 400 / 43) (slope := 39 / 5)
      (offset := -207 / 2) (q := 9) (q' := 0) (μ := 17) (k := 19)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_48 (x : ℝ) (h1 : ((400) / 43 : ℝ) ≤ x) (h2 : x < ((19) / 2 : ℝ)) :
    Ein x (19) = ((183) / 40 : ℝ) * x + ((-147) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 400 / 43) (b := 19 / 2) (slope := 183 / 40)
      (offset := -147 / 2) (q := 9) (q' := 0) (μ := 17) (k := 19)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_49 (x : ℝ) (h1 : ((19) / 2 : ℝ) ≤ x) (h2 : x < ((220) / 23 : ℝ)) :
    Ein x (19) = ((223) / 40 : ℝ) * x + ((-83) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 19 / 2) (b := 220 / 23) (slope := 223 / 40)
      (offset := -83) (q := 9) (q' := 0) (μ := 17) (k := 19)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_50 (x : ℝ) (h1 : ((220) / 23 : ℝ) ≤ x) (h2 : x < ((360) / 37 : ℝ)) :
    Ein x (20) = ((177) / 40 : ℝ) * x + ((-72) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 220 / 23) (b := 360 / 37) (slope := 177 / 40)
      (offset := -72) (q := 9) (q' := 0) (μ := 17) (k := 20)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_51 (x : ℝ) (h1 : ((360) / 37 : ℝ) ≤ x) (h2 : x < (10 : ℝ)) :
    Ein x (20) = ((181) / 20 : ℝ) * x + ((-117) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 360 / 37) (b := 10) (slope := 181 / 20)
      (offset := -117) (q := 9) (q' := 0) (μ := 18) (k := 20)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_52 (x : ℝ) (h1 : (10 : ℝ) ≤ x) (h2 : x < ((440) / 43 : ℝ)) :
    Ein x (22) = ((69) / 10 : ℝ) * x + ((-114) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 10) (b := 440 / 43) (slope := 69 / 10)
      (offset := -114) (q := 10) (q' := 0) (μ := 18) (k := 22)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_53 (x : ℝ) (h1 : ((440) / 43 : ℝ) ≤ x) (h2 : x < ((380) / 37 : ℝ)) :
    Ein x (22) = ((147) / 40 : ℝ) * x + ((-81) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 440 / 43) (b := 380 / 37) (slope := 147 / 40)
      (offset := -81) (q := 10) (q' := 0) (μ := 18) (k := 22)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_54 (x : ℝ) (h1 : ((380) / 37 : ℝ) ≤ x) (h2 : x < ((240) / 23 : ℝ)) :
    Ein x (22) = ((221) / 40 : ℝ) * x + ((-100) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 380 / 37) (b := 240 / 23) (slope := 221 / 40)
      (offset := -100) (q := 10) (q' := 0) (μ := 19) (k := 22)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_55 (x : ℝ) (h1 : ((240) / 23 : ℝ) ≤ x) (h2 : x < ((21) / 2 : ℝ)) :
    Ein x (23) = ((35) / 8 : ℝ) * x + ((-88) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 240 / 23) (b := 21 / 2) (slope := 35 / 8)
      (offset := -88) (q := 10) (q' := 0) (μ := 19) (k := 23)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_56 (x : ℝ) (h1 : ((21) / 2 : ℝ) ≤ x) (h2 : x < ((400) / 37 : ℝ)) :
    Ein x (23) = ((43) / 8 : ℝ) * x + ((-197) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 21 / 2) (b := 400 / 37) (slope := 43 / 8)
      (offset := -197 / 2) (q := 10) (q' := 0) (μ := 19) (k := 23)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_57 (x : ℝ) (h1 : ((400) / 37 : ℝ) ≤ x) (h2 : x < ((250) / 23 : ℝ)) :
    Ein x (23) = (10 : ℝ) * x + ((-297) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 400 / 37) (b := 250 / 23) (slope := 10)
      (offset := -297 / 2) (q := 10) (q' := 0) (μ := 20) (k := 23)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_58 (x : ℝ) (h1 : ((250) / 23 : ℝ) ≤ x) (h2 : x < (11 : ℝ)) :
    Ein x (24) = ((177) / 20 : ℝ) * x + ((-136) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 250 / 23) (b := 11) (slope := 177 / 20)
      (offset := -136) (q := 10) (q' := 0) (μ := 20) (k := 24)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

end Zeta5Irrational
