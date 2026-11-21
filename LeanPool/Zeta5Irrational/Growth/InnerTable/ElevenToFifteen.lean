/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Growth.PieceCertificate
import LeanPool.Zeta5Irrational.Growth.TableGen
public import LeanPool.Zeta5Irrational.Growth.TablePrime

/-! # Inner piece formulas on `[11, 15)`

The rational endpoint checks use the floor values and affine coefficients of each piece.
The first proof also realizes the existing equation lemmas for this module.
-/

@[expose] public section

namespace Zeta5Irrational

theorem inPiece_59 (x : ℝ) (h1 : (11 : ℝ) ≤ x) (h2 : x < ((480) / 43 : ℝ)) :
    Ein x (24) = (8 : ℝ) * x + ((-147) : ℝ) := by
  have hq0 : (11 : ℝ) ≤ x := by linarith only [h1, h2]
  have hq1 : x < (11 : ℝ) + 1 := by linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ 3 / 40 * x := by linarith only [h1, h2]
  have hr1 : 3 / 40 * x < (0 : ℝ) + 1 := by linarith only [h1, h2]
  rw [Ein_expand (24) (q := 11) (q' := 0) (μ := 20)
      (by norm_num only at hq0 ⊢; exact hq0)
      (by norm_num only at hq1 ⊢; exact hq1)
      (by norm_num only at hr0 ⊢; exact hr0)
      (by norm_num only at hr1 ⊢; exact hr1)
      (by norm_num only; linarith only [h1, h2])
      (by norm_num only; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (11 : ℝ) := sub_nonneg.mpr hq0
  have hf1 : x - (11 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hq1.trans_eq (add_comm _ _))
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := sub_nonneg.mpr hr0
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := sub_lt_iff_lt_add.mpr (hr1.trans_eq (add_comm _ _))
  have hmin01 : (1 / 2 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax02 : (0 : ℝ) ≤ ((3 / 40 * x - 0) - (1 / 2)) := sub_nonneg.mpr hmin01
  have hmin10 : (x - 11 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax20 : ((x - 11) - (1 / 2) : ℝ) ≤ 0 := sub_nonpos.mpr hmin10
  have hmin11 : (x - 11 : ℝ) ≤ (3 / 40 * x - 0) := by linarith only [h1, h2]
  have hmax12 : (((x - 11) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax21 : (((1 / 2) + (x - 11)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
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

theorem inPiece_60 (x : ℝ) (h1 : ((480) / 43 : ℝ) ≤ x) (h2 : x < ((260) / 23 : ℝ)) :
    Ein x (24) = ((191) / 40 : ℝ) * x + ((-111) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 480 / 43) (b := 260 / 23) (slope := 191 / 40)
      (offset := -111) (q := 11) (q' := 0) (μ := 20) (k := 24)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_61 (x : ℝ) (h1 : ((260) / 23 : ℝ) ≤ x) (h2 : x < ((420) / 37 : ℝ)) :
    Ein x (25) = ((29) / 8 : ℝ) * x + ((-98) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 260 / 23) (b := 420 / 37) (slope := 29 / 8)
      (offset := -98) (q := 11) (q' := 0) (μ := 20) (k := 25)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_62 (x : ℝ) (h1 : ((420) / 37 : ℝ) ≤ x) (h2 : x < ((23) / 2 : ℝ)) :
    Ein x (25) = ((219) / 40 : ℝ) * x + ((-119) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 420 / 37) (b := 23 / 2) (slope := 219 / 40)
      (offset := -119) (q := 11) (q' := 0) (μ := 21) (k := 25)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_63 (x : ℝ) (h1 : ((23) / 2 : ℝ) ≤ x) (h2 : x < ((270) / 23 : ℝ)) :
    Ein x (25) = ((259) / 40 : ℝ) * x + ((-261) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 23 / 2) (b := 270 / 23) (slope := 259 / 40)
      (offset := -261 / 2) (q := 11) (q' := 0) (μ := 21) (k := 25)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_64 (x : ℝ) (h1 : ((270) / 23 : ℝ) ≤ x) (h2 : x < ((440) / 37 : ℝ)) :
    Ein x (26) = ((213) / 40 : ℝ) * x + ((-117) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 270 / 23) (b := 440 / 37) (slope := 213 / 40)
      (offset := -117) (q := 11) (q' := 0) (μ := 21) (k := 26)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_65 (x : ℝ) (h1 : ((440) / 37 : ℝ) ≤ x) (h2 : x < (12 : ℝ)) :
    Ein x (26) = ((199) / 20 : ℝ) * x + ((-172) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 440 / 37) (b := 12) (slope := 199 / 20)
      (offset := -172) (q := 11) (q' := 0) (μ := 22) (k := 26)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_66 (x : ℝ) (h1 : (12 : ℝ) ≤ x) (h2 : x < ((520) / 43 : ℝ)) :
    Ein x (26) = ((91) / 10 : ℝ) * x + ((-184) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 12) (b := 520 / 43) (slope := 91 / 10)
      (offset := -184) (q := 12) (q' := 0) (μ := 22) (k := 26)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_67 (x : ℝ) (h1 : ((520) / 43 : ℝ) ≤ x) (h2 : x < ((280) / 23 : ℝ)) :
    Ein x (26) = ((47) / 8 : ℝ) * x + ((-145) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 520 / 43) (b := 280 / 23) (slope := 47 / 8)
      (offset := -145) (q := 12) (q' := 0) (μ := 22) (k := 26)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_68 (x : ℝ) (h1 : ((280) / 23 : ℝ) ≤ x) (h2 : x < ((460) / 37 : ℝ)) :
    Ein x (27) = ((189) / 40 : ℝ) * x + ((-131) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 280 / 23) (b := 460 / 37) (slope := 189 / 40)
      (offset := -131) (q := 12) (q' := 0) (μ := 22) (k := 27)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_69 (x : ℝ) (h1 : ((460) / 37 : ℝ) ≤ x) (h2 : x < ((25) / 2 : ℝ)) :
    Ein x (27) = ((263) / 40 : ℝ) * x + ((-154) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 460 / 37) (b := 25 / 2) (slope := 263 / 40)
      (offset := -154) (q := 12) (q' := 0) (μ := 23) (k := 27)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_70 (x : ℝ) (h1 : ((25) / 2 : ℝ) ≤ x) (h2 : x < ((290) / 23 : ℝ)) :
    Ein x (27) = ((303) / 40 : ℝ) * x + ((-333) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 25 / 2) (b := 290 / 23) (slope := 303 / 40)
      (offset := -333 / 2) (q := 12) (q' := 0) (μ := 23) (k := 27)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_71 (x : ℝ) (h1 : ((290) / 23 : ℝ) ≤ x) (h2 : x < ((480) / 37 : ℝ)) :
    Ein x (28) = ((257) / 40 : ℝ) * x + ((-152) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 290 / 23) (b := 480 / 37) (slope := 257 / 40)
      (offset := -152) (q := 12) (q' := 0) (μ := 23) (k := 28)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_72 (x : ℝ) (h1 : ((480) / 37 : ℝ) ≤ x) (h2 : x < (13 : ℝ)) :
    Ein x (28) = ((221) / 20 : ℝ) * x + ((-212) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 480 / 37) (b := 13) (slope := 221 / 20)
      (offset := -212) (q := 12) (q' := 0) (μ := 24) (k := 28)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_73 (x : ℝ) (h1 : (13 : ℝ) ≤ x) (h2 : x < ((560) / 43 : ℝ)) :
    Ein x (28) = ((51) / 5 : ℝ) * x + ((-225) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 13) (b := 560 / 43) (slope := 51 / 5)
      (offset := -225) (q := 13) (q' := 0) (μ := 24) (k := 28)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_74 (x : ℝ) (h1 : ((560) / 43 : ℝ) ≤ x) (h2 : x < ((300) / 23 : ℝ)) :
    Ein x (28) = ((279) / 40 : ℝ) * x + ((-183) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 560 / 43) (b := 300 / 23) (slope := 279 / 40)
      (offset := -183) (q := 13) (q' := 0) (μ := 24) (k := 28)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_75 (x : ℝ) (h1 : ((300) / 23 : ℝ) ≤ x) (h2 : x < ((40) / 3 : ℝ)) :
    Ein x (29) = ((233) / 40 : ℝ) * x + ((-168) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 300 / 23) (b := 40 / 3) (slope := 233 / 40)
      (offset := -168) (q := 13) (q' := 0) (μ := 24) (k := 29)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_76 (x : ℝ) (h1 : ((40) / 3 : ℝ) ≤ x) (h2 : x < ((310) / 23 : ℝ)) :
    Ein x (30) = ((145) / 8 : ℝ) * x + ((-184) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 40 / 3) (b := 310 / 23) (slope := 145 / 8)
      (offset := -184) (q := 13) (q' := 1) (μ := 24) (k := 30)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_77 (x : ℝ) (h1 : ((310) / 23 : ℝ) ≤ x) (h2 : x < ((27) / 2 : ℝ)) :
    Ein x (31) = ((679) / 40 : ℝ) * x + ((-337) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 310 / 23) (b := 27 / 2) (slope := 679 / 40)
      (offset := -337 / 2) (q := 13) (q' := 1) (μ := 24) (k := 31)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_78 (x : ℝ) (h1 : ((27) / 2 : ℝ) ≤ x) (h2 : x < ((500) / 37 : ℝ)) :
    Ein x (31) = ((719) / 40 : ℝ) * x + ((-182) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 27 / 2) (b := 500 / 37) (slope := 719 / 40)
      (offset := -182) (q := 13) (q' := 1) (μ := 24) (k := 31)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_79 (x : ℝ) (h1 : ((500) / 37 : ℝ) ≤ x) (h2 : x < ((320) / 23 : ℝ)) :
    Ein x (31) = ((793) / 40 : ℝ) * x + ((-207) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 500 / 37) (b := 320 / 23) (slope := 793 / 40)
      (offset := -207) (q := 13) (q' := 1) (μ := 25) (k := 31)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_80 (x : ℝ) (h1 : ((320) / 23 : ℝ) ≤ x) (h2 : x < ((600) / 43 : ℝ)) :
    Ein x (32) = ((747) / 40 : ℝ) * x + ((-191) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 320 / 23) (b := 600 / 43) (slope := 747 / 40)
      (offset := -191) (q := 13) (q' := 1) (μ := 25) (k := 32)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_81 (x : ℝ) (h1 : ((600) / 43 : ℝ) ≤ x) (h2 : x < (14 : ℝ)) :
    Ein x (32) = ((309) / 20 : ℝ) * x + ((-146) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 600 / 43) (b := 14) (slope := 309 / 20)
      (offset := -146) (q := 13) (q' := 1) (μ := 25) (k := 32)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem inPiece_82 (x : ℝ) (h1 : (14 : ℝ) ≤ x) (h2 : x < ((520) / 37 : ℝ)) :
    Ein x (32) = ((73) / 5 : ℝ) * x + ((-160) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 14) (b := 520 / 37) (slope := 73 / 5)
      (offset := -160) (q := 14) (q' := 1) (μ := 25) (k := 32)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_83 (x : ℝ) (h1 : ((520) / 37 : ℝ) ≤ x) (h2 : x < ((330) / 23 : ℝ)) :
    Ein x (32) = ((769) / 40 : ℝ) * x + ((-225) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 520 / 37) (b := 330 / 23) (slope := 769 / 40)
      (offset := -225) (q := 14) (q' := 1) (μ := 26) (k := 32)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_84 (x : ℝ) (h1 : ((330) / 23 : ℝ) ≤ x) (h2 : x < ((29) / 2 : ℝ)) :
    Ein x (33) = ((723) / 40 : ℝ) * x + ((-417) / 2 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 330 / 23) (b := 29 / 2) (slope := 723 / 40)
      (offset := -417 / 2) (q := 14) (q' := 1) (μ := 26) (k := 33)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_85 (x : ℝ) (h1 : ((29) / 2 : ℝ) ≤ x) (h2 : x < ((540) / 37 : ℝ)) :
    Ein x (33) = ((763) / 40 : ℝ) * x + ((-223) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 29 / 2) (b := 540 / 37) (slope := 763 / 40)
      (offset := -223) (q := 14) (q' := 1) (μ := 26) (k := 33)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_86 (x : ℝ) (h1 : ((540) / 37 : ℝ) ≤ x) (h2 : x < ((340) / 23 : ℝ)) :
    Ein x (33) = ((837) / 40 : ℝ) * x + ((-250) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 540 / 37) (b := 340 / 23) (slope := 837 / 40)
      (offset := -250) (q := 14) (q' := 1) (μ := 27) (k := 33)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_87 (x : ℝ) (h1 : ((340) / 23 : ℝ) ≤ x) (h2 : x < ((640) / 43 : ℝ)) :
    Ein x (34) = ((791) / 40 : ℝ) * x + ((-233) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 340 / 23) (b := 640 / 43) (slope := 791 / 40)
      (offset := -233) (q := 14) (q' := 1) (μ := 27) (k := 34)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem inPiece_88 (x : ℝ) (h1 : ((640) / 43 : ℝ) ≤ x) (h2 : x < (15 : ℝ)) :
    Ein x (34) = ((331) / 20 : ℝ) * x + ((-185) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.innerPiece (a := 640 / 43) (b := 15) (slope := 331 / 20)
      (offset := -185) (q := 14) (q' := 1) (μ := 27) (k := 34)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

end Zeta5Irrational
