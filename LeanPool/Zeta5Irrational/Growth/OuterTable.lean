/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Growth.PieceCertificate
import LeanPool.Zeta5Irrational.Growth.TableGen
public import LeanPool.Zeta5Irrational.Growth.OuterPrime
import Mathlib.Tactic.IntervalCases -- shake: keep
import Mathlib.Tactic.Linarith -- shake: keep
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.Ring.RingNF -- shake: keep

/-! # The outer piece table on `[20/37, 3]`

The interval and coefficient data originate in `gen_lean_outer.py`. Each row uses the
rational endpoint checks to prove its affine formula.
The first proof also realizes the existing equation lemmas for this module.
-/

@[expose] public section

namespace Zeta5Irrational

theorem outPiece_0 (x : ℝ) (h1 : ((20) / 37 : ℝ) ≤ x) (h2 : x < ((40) / 43 : ℝ)) :
    Eout x = ((37) / 20 : ℝ) * x + ((-1) : ℝ) := by
  rw [Eout_expand (q := 0) (q' := 0) (μ := 1)
      (by norm_num; linarith only [h1, h2])
      (by norm_num; linarith only [h1, h2])
      (by norm_num; linarith only [h1, h2])
      (by norm_num; linarith only [h1, h2])
      (by norm_num; linarith only [h1, h2])
      (by norm_num; linarith only [h1, h2])
      (by linarith only [h1, h2])]
  have hf0 : (0 : ℝ) ≤ x - (0 : ℝ) := by linarith only [h1, h2]
  have hf1 : x - (0 : ℝ) < 1 := by linarith only [h1, h2]
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - (0 : ℝ) := by linarith only [h1, h2]
  have hg1 : 3 / 40 * x - (0 : ℝ) < 1 := by linarith only [h1, h2]
  have hmin01 : (3 / 40 * x - 0 : ℝ) ≤ (1 / 2) := by linarith only [h1, h2]
  have hmax02 : ((3 / 40 * x - 0) - (1 / 2) : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmin10 : (1 / 2 : ℝ) ≤ (x - 0) := by linarith only [h1, h2]
  have hmin11 : (3 / 40 * x - 0 : ℝ) ≤ (x - 0) := by linarith only [h1, h2]
  have hmax12 : (((1 / 2) + (3 / 40 * x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmax20 : (0 : ℝ) ≤ ((x - 0) - (1 / 2)) := by linarith only [h1, h2]
  have hmax21 : (((3 / 40 * x - 0) + (x - 0)) - 1 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have hmaxm : (13 / 10 * x - 2 : ℝ) ≤ 0 := by linarith only [h1, h2]
  have e00 :
    ccount (x - (0 : ℝ)) (3 / 40 * x - (0 : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00]
    ring
  have e01 :
    ccount (x - (0 : ℝ)) (3 / 40 * x - (0 : ℝ)) 0 1 =
      (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc01 hg0 hg1, min_eq_left hmin01]
    ring
  have e02 :
    ccount (x - (0 : ℝ)) (3 / 40 * x - (0 : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hg1, max_eq_left hmax02]
    ring
  have e10 :
    ccount (x - (0 : ℝ)) (3 / 40 * x - (0 : ℝ)) 1 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc10 hf0 hf1, min_eq_right hmin10]
    ring
  have e11 :
    ccount (x - (0 : ℝ)) (3 / 40 * x - (0 : ℝ)) 1 1 =
      (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc11 hf0 hf1 hg0, min_eq_right hmin11, min_eq_left hmin01]
    ring
  have e12 :
    ccount (x - (0 : ℝ)) (3 / 40 * x - (0 : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hg1, min_eq_right hmin10, max_eq_left hmax12]
    ring
  have e20 :
    ccount (x - (0 : ℝ)) (3 / 40 * x - (0 : ℝ)) 2 0 =
      ((1 : ℝ) * x + ((-1) / 2 : ℝ)) := by
    rw [cc20 hf1, max_eq_right hmax20]
    ring
  have e21 :
    ccount (x - (0 : ℝ)) (3 / 40 * x - (0 : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf1, min_eq_left hmin01, max_eq_left hmax21]
    ring
  have e22 :
    ccount (x - (0 : ℝ)) (3 / 40 * x - (0 : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hg1, min_eq_right hmin11, max_eq_left hmax02]
    ring
  have em : max 0 (13 / 10 * x - 2) = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [max_eq_left hmaxm]
    ring
  push_cast
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22, em]
  simp only [bGO, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, GO]
  norm_num
  ring_nf

theorem outPiece_1 (x : ℝ) (h1 : ((40) / 43 : ℝ) ≤ x) (h2 : x < (1 : ℝ)) :
    Eout x = ((37) / 20 : ℝ) * x + ((-1) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 40 / 43) (b := 1) (slope := 37 / 20)
      (offset := -1) (q := 0) (q' := 0) (μ := 1)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_one] using h2)

theorem outPiece_2 (x : ℝ) (h1 : (1 : ℝ) ≤ x) (h2 : x < ((40) / 37 : ℝ)) :
    Eout x = (1 : ℝ) * x + ((-2) : ℝ) := by
  simpa only [Rat.cast_ofNat, Rat.cast_one, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 1) (b := 40 / 37) (slope := 1)
      (offset := -2) (q := 1) (q' := 0) (μ := 1)
      (by decide +kernel)
      (by simpa only [Rat.cast_one] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem outPiece_3 (x : ℝ) (h1 : ((40) / 37 : ℝ) ≤ x) (h2 : x < ((3) / 2 : ℝ)) :
    Eout x = ((42) / 5 : ℝ) * x + ((-10) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 40 / 37) (b := 3 / 2) (slope := 42 / 5)
      (offset := -10) (q := 1) (q' := 0) (μ := 2)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem outPiece_4 (x : ℝ) (h1 : ((3) / 2 : ℝ) ≤ x) (h2 : x < ((20) / 13 : ℝ)) :
    Eout x = ((42) / 5 : ℝ) * x + ((-10) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 3 / 2) (b := 20 / 13) (slope := 42 / 5)
      (offset := -10) (q := 1) (q' := 0) (μ := 2)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem outPiece_5 (x : ℝ) (h1 : ((20) / 13 : ℝ) ≤ x) (h2 : x < ((60) / 37 : ℝ)) :
    Eout x = ((97) / 10 : ℝ) * x + ((-12) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 20 / 13) (b := 60 / 37) (slope := 97 / 10)
      (offset := -12) (q := 1) (q' := 0) (μ := 2)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem outPiece_6 (x : ℝ) (h1 : ((60) / 37 : ℝ) ≤ x) (h2 : x < ((80) / 43 : ℝ)) :
    Eout x = ((231) / 20 : ℝ) * x + ((-15) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 60 / 37) (b := 80 / 43) (slope := 231 / 20)
      (offset := -15) (q := 1) (q' := 0) (μ := 3)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem outPiece_7 (x : ℝ) (h1 : ((80) / 43 : ℝ) ≤ x) (h2 : x < (2 : ℝ)) :
    Eout x = ((51) / 10 : ℝ) * x + ((-3) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 80 / 43) (b := 2) (slope := 51 / 10)
      (offset := -3) (q := 1) (q' := 0) (μ := 3)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

theorem outPiece_8 (x : ℝ) (h1 : (2 : ℝ) ≤ x) (h2 : x < ((80) / 37 : ℝ)) :
    Eout x = ((17) / 4 : ℝ) * x + ((-5) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 2) (b := 80 / 37) (slope := 17 / 4)
      (offset := -5) (q := 2) (q' := 0) (μ := 3)
      (by decide +kernel)
      (by simpa only [Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem outPiece_9 (x : ℝ) (h1 : ((80) / 37 : ℝ) ≤ x) (h2 : x < ((5) / 2 : ℝ)) :
    Eout x = ((429) / 40 : ℝ) * x + ((-19) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 80 / 37) (b := 5 / 2) (slope := 429 / 40)
      (offset := -19) (q := 2) (q' := 0) (μ := 4)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem outPiece_10 (x : ℝ) (h1 : ((5) / 2 : ℝ) ≤ x) (h2 : x < ((100) / 37 : ℝ)) :
    Eout x = ((429) / 40 : ℝ) * x + ((-19) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 5 / 2) (b := 100 / 37) (slope := 429 / 40)
      (offset := -19) (q := 2) (q' := 0) (μ := 4)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem outPiece_11 (x : ℝ) (h1 : ((100) / 37 : ℝ) ≤ x) (h2 : x < ((120) / 43 : ℝ)) :
    Eout x = ((503) / 40 : ℝ) * x + ((-24) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 100 / 37) (b := 120 / 43) (slope := 503 / 40)
      (offset := -24) (q := 2) (q' := 0) (μ := 5)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h2)

theorem outPiece_12 (x : ℝ) (h1 : ((120) / 43 : ℝ) ≤ x) (h2 : x < (3 : ℝ)) :
    Eout x = ((36) / 5 : ℝ) * x + ((-9) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    PieceCertificate.outerPiece (a := 120 / 43) (b := 3) (slope := 36 / 5)
      (offset := -9) (q := 2) (q' := 0) (μ := 5)
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h1)
      (by simpa only [Rat.cast_ofNat] using h2)

/-- The 14 rational endpoints of the 13 outer-range linear pieces. -/
def tOutL : List ℚ :=
  [(20 / 37), (40 / 43), (1), (40 / 37), (3 / 2), (20 / 13), (60 / 37), (80 / 43), (2), (80 / 37),
    (5 / 2), (100 / 37), (120 / 43), (3)]

/-- Rational slopes of the 13 outer-range linear pieces. -/
def aOutL : List ℚ :=
  [(37 / 20), (37 / 20), (1), (42 / 5), (42 / 5), (97 / 10), (231 / 20), (51 / 10), (17 / 4),
    (429 / 40), (429 / 40), (503 / 40), (36 / 5)]

/-- Rational intercepts of the 13 outer-range linear pieces. -/
def bOutL : List ℚ :=
  [(-1), (-1), (-2), (-10), (-10), (-12), (-15), (-3), (-5), (-19), (-19), (-24), (-9)]

/-- The `i`th outer-range endpoint as a real number; zero outside the table. -/
noncomputable def tOut (i : ℕ) : ℝ :=
  ((tOutL.getD i 0 : ℚ) : ℝ)

/-- The affine bound on outer piece `i`, with coefficients from `aOutL` and `bOutL`. -/
noncomputable def gOut (i : ℕ) (x : ℝ) : ℝ :=
  ((aOutL.getD i 0 : ℚ) : ℝ) * x + ((bOutL.getD i 0 : ℚ) : ℝ)

theorem tOut_mono : ∀ i < 13, tOut i < tOut (i + 1) := by
  intro i hi
  interval_cases i <;> simp only [tOut, tOutL, List.getD_cons_succ, List.getD_cons_zero] <;>
    norm_num

theorem outer_table : ∀ i < 13, ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  intro i hi x hx
  interval_cases i
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_0 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_1 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_2 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_3 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_4 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_5 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_6 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_7 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_8 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_9 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_10 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_11 x hx.1 hx.2
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero,
      Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    exact outPiece_12 x hx.1 hx.2

end Zeta5Irrational
