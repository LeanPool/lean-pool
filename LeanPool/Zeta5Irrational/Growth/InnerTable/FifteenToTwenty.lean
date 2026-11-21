/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Growth.PieceCertificate
import LeanPool.Zeta5Irrational.Growth.TableGen
public import LeanPool.Zeta5Irrational.Growth.TablePrime

/-! # Inner piece formulas on `[15, 20)`

The rational endpoint checks use the floor values and affine coefficients of each piece.
The first proof also realizes the existing equation lemmas for this module.
-/

@[expose] public section

namespace Zeta5Irrational

theorem inPiece_89 (x : ℝ) (h1 : (15 : ℝ) ≤ x) (h2 : x < ((560) / 37 : ℝ)) :
    Ein x (34) = ((157) / 10 : ℝ) * x + ((-200) : ℝ) := by
  have hq0 : (15 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (15 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (1 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (1 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (34) (q := 15) (q' := 1) (μ := 27)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (15 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (15 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (1 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (1 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (3 / 40 * x - 1 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 1) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin01
  have hmin10 : (x - 15 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 15) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 15 : ℝ) ≤ (3 / 40 * x - 1) := by linarith only [h1, h2]
  have hmax12 : (((x - 15) + (3 / 40 * x - 1)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 1) + (x - 15)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
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

theorem inPiece_90 (x : ℝ) (h1 : ((560) / 37 : ℝ) ≤ x) (h2 : x < ((350) / 23 : ℝ)) :
    Ein x (34) = ((813) / 40 : ℝ) * x + ((-270) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 560 / 37) (b := 350 / 23) (slope := 813 / 40)
      (offset := -270) (q := 15) (q' := 1) (μ := 28) (k := 34)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_91 (x : ℝ) (h1 : ((350) / 23 : ℝ) ≤ x) (h2 : x < ((31) / 2 : ℝ)) :
    Ein x (35) = ((767) / 40 : ℝ) * x + ((-505) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 350 / 23) (b := 31 / 2) (slope := 767 / 40)
      (offset := -505 / 2) (q := 15) (q' := 1) (μ := 28) (k := 35)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_92 (x : ℝ) (h1 : ((31) / 2 : ℝ) ≤ x) (h2 : x < ((360) / 23 : ℝ)) :
    Ein x (35) = ((807) / 40 : ℝ) * x + ((-268) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 31 / 2) (b := 360 / 23) (slope := 807 / 40)
      (offset := -268) (q := 15) (q' := 1) (μ := 28) (k := 35)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_93 (x : ℝ) (h1 : ((360) / 23 : ℝ) ≤ x) (h2 : x < ((580) / 37 : ℝ)) :
    Ein x (36) = ((761) / 40 : ℝ) * x + ((-250) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 360 / 23) (b := 580 / 37) (slope := 761 / 40)
      (offset := -250) (q := 15) (q' := 1) (μ := 28) (k := 36)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_94 (x : ℝ) (h1 : ((580) / 37 : ℝ) ≤ x) (h2 : x < ((680) / 43 : ℝ)) :
    Ein x (36) = ((167) / 8 : ℝ) * x + ((-279) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 580 / 37) (b := 680 / 43) (slope := 167 / 8)
      (offset := -279) (q := 15) (q' := 1) (μ := 29) (k := 36)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_95 (x : ℝ) (h1 : ((680) / 43 : ℝ) ≤ x) (h2 : x < (16 : ℝ)) :
    Ein x (36) = ((353) / 20 : ℝ) * x + ((-228) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 680 / 43) (b := 16) (slope := 353 / 20)
      (offset := -228) (q := 15) (q' := 1) (μ := 29) (k := 36)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_96 (x : ℝ) (h1 : (16 : ℝ) ≤ x) (h2 : x < ((370) / 23 : ℝ)) :
    Ein x (36) = ((84) / 5 : ℝ) * x + ((-244) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 16) (b := 370 / 23) (slope := 84 / 5)
      (offset := -244) (q := 16) (q' := 1) (μ := 29) (k := 36)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_97 (x : ℝ) (h1 : ((370) / 23 : ℝ) ≤ x) (h2 : x < ((600) / 37 : ℝ)) :
    Ein x (37) = ((313) / 20 : ℝ) * x + ((-451) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 370 / 23) (b := 600 / 37) (slope := 313 / 20)
      (offset := -451 / 2) (q := 16) (q' := 1) (μ := 29) (k := 37)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_98 (x : ℝ) (h1 : ((600) / 37 : ℝ) ≤ x) (h2 : x < ((33) / 2 : ℝ)) :
    Ein x (37) = ((811) / 40 : ℝ) * x + ((-601) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 600 / 37) (b := 33 / 2) (slope := 811 / 40)
      (offset := -601 / 2) (q := 16) (q' := 1) (μ := 30) (k := 37)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_99 (x : ℝ) (h1 : ((33) / 2 : ℝ) ≤ x) (h2 : x < ((380) / 23 : ℝ)) :
    Ein x (37) = ((851) / 40 : ℝ) * x + ((-317) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 33 / 2) (b := 380 / 23) (slope := 851 / 40)
      (offset := -317) (q := 16) (q' := 1) (μ := 30) (k := 37)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_100 (x : ℝ) (h1 : ((380) / 23 : ℝ) ≤ x) (h2 : x < ((50) / 3 : ℝ)) :
    Ein x (38) = ((161) / 8 : ℝ) * x + ((-298) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 380 / 23) (b := 50 / 3) (slope := 161 / 8)
      (offset := -298) (q := 16) (q' := 1) (μ := 30) (k := 38)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_101 (x : ℝ) (h1 : ((50) / 3 : ℝ) ≤ x) (h2 : x < ((720) / 43 : ℝ)) :
    Ein x (39) = ((799) / 40 : ℝ) * x + ((-591) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 50 / 3) (b := 720 / 43) (slope := 799 / 40)
      (offset := -591 / 2) (q := 16) (q' := 1) (μ := 30) (k := 39)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_102 (x : ℝ) (h1 : ((720) / 43 : ℝ) ≤ x) (h2 : x < ((620) / 37 : ℝ)) :
    Ein x (39) = ((67) / 4 : ℝ) * x + ((-483) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 720 / 43) (b := 620 / 37) (slope := 67 / 4)
      (offset := -483 / 2) (q := 16) (q' := 1) (μ := 30) (k := 39)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_103 (x : ℝ) (h1 : ((620) / 37 : ℝ) ≤ x) (h2 : x < ((390) / 23 : ℝ)) :
    Ein x (39) = ((93) / 5 : ℝ) * x + ((-545) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 620 / 37) (b := 390 / 23) (slope := 93 / 5)
      (offset := -545 / 2) (q := 16) (q' := 1) (μ := 31) (k := 39)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_104 (x : ℝ) (h1 : ((390) / 23 : ℝ) ≤ x) (h2 : x < (17 : ℝ)) :
    Ein x (40) = ((349) / 20 : ℝ) * x + ((-253) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 390 / 23) (b := 17) (slope := 349 / 20)
      (offset := -253) (q := 16) (q' := 1) (μ := 31) (k := 40)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_105 (x : ℝ) (h1 : (17 : ℝ) ≤ x) (h2 : x < ((640) / 37 : ℝ)) :
    Ein x (40) = ((83) / 5 : ℝ) * x + ((-270) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 17) (b := 640 / 37) (slope := 83 / 5)
      (offset := -270) (q := 17) (q' := 1) (μ := 31) (k := 40)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_106 (x : ℝ) (h1 : ((640) / 37 : ℝ) ≤ x) (h2 : x < ((400) / 23 : ℝ)) :
    Ein x (40) = ((849) / 40 : ℝ) * x + ((-350) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 640 / 37) (b := 400 / 23) (slope := 849 / 40)
      (offset := -350) (q := 17) (q' := 1) (μ := 32) (k := 40)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_107 (x : ℝ) (h1 : ((400) / 23 : ℝ) ≤ x) (h2 : x < ((35) / 2 : ℝ)) :
    Ein x (41) = ((803) / 40 : ℝ) * x + ((-330) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 400 / 23) (b := 35 / 2) (slope := 803 / 40)
      (offset := -330) (q := 17) (q' := 1) (μ := 32) (k := 41)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_108 (x : ℝ) (h1 : ((35) / 2 : ℝ) ≤ x) (h2 : x < ((760) / 43 : ℝ)) :
    Ein x (41) = ((843) / 40 : ℝ) * x + ((-695) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 35 / 2) (b := 760 / 43) (slope := 843 / 40)
      (offset := -695 / 2) (q := 17) (q' := 1) (μ := 32) (k := 41)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_109 (x : ℝ) (h1 : ((760) / 43 : ℝ) ≤ x) (h2 : x < ((410) / 23 : ℝ)) :
    Ein x (41) = ((357) / 20 : ℝ) * x + ((-581) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 760 / 43) (b := 410 / 23) (slope := 357 / 20)
      (offset := -581 / 2) (q := 17) (q' := 1) (μ := 32) (k := 41)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_110 (x : ℝ) (h1 : ((410) / 23 : ℝ) ≤ x) (h2 : x < ((660) / 37 : ℝ)) :
    Ein x (42) = ((167) / 10 : ℝ) * x + ((-270) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 410 / 23) (b := 660 / 37) (slope := 167 / 10)
      (offset := -270) (q := 17) (q' := 1) (μ := 32) (k := 42)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_111 (x : ℝ) (h1 : ((660) / 37 : ℝ) ≤ x) (h2 : x < (18 : ℝ)) :
    Ein x (42) = ((371) / 20 : ℝ) * x + ((-303) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 660 / 37) (b := 18) (slope := 371 / 20)
      (offset := -303) (q := 17) (q' := 1) (μ := 33) (k := 42)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_112 (x : ℝ) (h1 : (18 : ℝ) ≤ x) (h2 : x < ((420) / 23 : ℝ)) :
    Ein x (42) = ((177) / 10 : ℝ) * x + ((-321) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 18) (b := 420 / 23) (slope := 177 / 10)
      (offset := -321) (q := 18) (q' := 1) (μ := 33) (k := 42)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_113 (x : ℝ) (h1 : ((420) / 23 : ℝ) ≤ x) (h2 : x < ((680) / 37 : ℝ)) :
    Ein x (43) = ((331) / 20 : ℝ) * x + ((-300) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 420 / 23) (b := 680 / 37) (slope := 331 / 20)
      (offset := -300) (q := 18) (q' := 1) (μ := 33) (k := 43)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_114 (x : ℝ) (h1 : ((680) / 37 : ℝ) ≤ x) (h2 : x < ((37) / 2 : ℝ)) :
    Ein x (43) = ((847) / 40 : ℝ) * x + ((-385) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 680 / 37) (b := 37 / 2) (slope := 847 / 40)
      (offset := -385) (q := 18) (q' := 1) (μ := 34) (k := 43)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_115 (x : ℝ) (h1 : ((37) / 2 : ℝ) ≤ x) (h2 : x < ((800) / 43 : ℝ)) :
    Ein x (43) = ((887) / 40 : ℝ) * x + ((-807) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 37 / 2) (b := 800 / 43) (slope := 887 / 40)
      (offset := -807 / 2) (q := 18) (q' := 1) (μ := 34) (k := 43)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_116 (x : ℝ) (h1 : ((800) / 43 : ℝ) ≤ x) (h2 : x < ((430) / 23 : ℝ)) :
    Ein x (43) = ((379) / 20 : ℝ) * x + ((-687) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 800 / 43) (b := 430 / 23) (slope := 379 / 20)
      (offset := -687 / 2) (q := 18) (q' := 1) (μ := 34) (k := 43)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_117 (x : ℝ) (h1 : ((430) / 23 : ℝ) ≤ x) (h2 : x < ((700) / 37 : ℝ)) :
    Ein x (44) = ((89) / 5 : ℝ) * x + ((-322) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 430 / 23) (b := 700 / 37) (slope := 89 / 5)
      (offset := -322) (q := 18) (q' := 1) (μ := 34) (k := 44)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_118 (x : ℝ) (h1 : ((700) / 37 : ℝ) ≤ x) (h2 : x < (19 : ℝ)) :
    Ein x (44) = ((393) / 20 : ℝ) * x + ((-357) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 700 / 37) (b := 19) (slope := 393 / 20)
      (offset := -357) (q := 18) (q' := 1) (μ := 35) (k := 44)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_119 (x : ℝ) (h1 : (19 : ℝ) ≤ x) (h2 : x < ((440) / 23 : ℝ)) :
    Ein x (44) = ((94) / 5 : ℝ) * x + ((-376) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 19) (b := 440 / 23) (slope := 94 / 5)
      (offset := -376) (q := 19) (q' := 1) (μ := 35) (k := 44)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_120 (x : ℝ) (h1 : ((440) / 23 : ℝ) ≤ x) (h2 : x < ((720) / 37 : ℝ)) :
    Ein x (45) = ((353) / 20 : ℝ) * x + ((-354) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 440 / 23) (b := 720 / 37) (slope := 353 / 20)
      (offset := -354) (q := 19) (q' := 1) (μ := 35) (k := 45)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_121 (x : ℝ) (h1 : ((720) / 37 : ℝ) ≤ x) (h2 : x < ((39) / 2 : ℝ)) :
    Ein x (45) = ((891) / 40 : ℝ) * x + ((-444) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 720 / 37) (b := 39 / 2) (slope := 891 / 40)
      (offset := -444) (q := 19) (q' := 1) (μ := 36) (k := 45)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_122 (x : ℝ) (h1 : ((39) / 2 : ℝ) ≤ x) (h2 : x < ((840) / 43 : ℝ)) :
    Ein x (45) = ((931) / 40 : ℝ) * x + ((-927) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 39 / 2) (b := 840 / 43) (slope := 931 / 40)
      (offset := -927 / 2) (q := 19) (q' := 1) (μ := 36) (k := 45)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_123 (x : ℝ) (h1 : ((840) / 43 : ℝ) ≤ x) (h2 : x < ((450) / 23 : ℝ)) :
    Ein x (45) = ((401) / 20 : ℝ) * x + ((-801) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 840 / 43) (b := 450 / 23) (slope := 401 / 20)
      (offset := -801 / 2) (q := 19) (q' := 1) (μ := 36) (k := 45)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_124 (x : ℝ) (h1 : ((450) / 23 : ℝ) ≤ x) (h2 : x < (20 : ℝ)) :
    Ein x (46) = ((189) / 10 : ℝ) * x + ((-378) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 450 / 23) (b := 20) (slope := 189 / 10)
      (offset := -378) (q := 19) (q' := 1) (μ := 36) (k := 46)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

end Zeta5Irrational
