/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.ArctangentCertificate
import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries
import LeanPool.Zeta5Irrational.Table.LowerCertificate

public import LeanPool.Zeta5Irrational.Energy
import LeanPool.Zeta5Irrational.Certificates
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # V25: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped ArctangentCertificates LogarithmCertificates

lemma V_301 :
    ((1240130691140485734679 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12478605076626120675669 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5305595421098193 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (152436035464757284741 / 625000000000000000000 : ℝ))) -
              6 * (175537173293389352119 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (9007789687161 / 32000000000000 : ℝ) := by
  have hL1 :
    (1240130691140485734679 / 5000000000000000000000 : ℝ) ≤
      Real.log (41007789687161 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (41007789687161 / 32000000000000 : ℚ))
        (L := (1240130691140485734679 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (9187789687161 / 32000000000000 : ℝ) ≤
      (-(12478605076626120675669 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9187789687161 / 32000000000000 : ℚ))
        (r' := (9187789687161 / 8000000000000 : ℚ))
        (U := (-(12478605076626120675669 / 10000000000000000000000 : ℚ)))
        (U' := (1384338529373879324331 / 10000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau374 :
    Real.arctan (1326398855274549 / 5330076663850934 : ℝ) ≤
      (152436035464757284741 / 625000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1326398855274549 / 5330076663850934 : ℚ))
        (U := (152436035464757284741 / 625000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau373 :
    Real.arctan (1326398855274549 / 2500000000000000 : ℝ) ≤
      (2 * (152436035464757284741 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1415038331925467 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (1326398855274549 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1326398855274549 / 2500000000000000 : ℝ) /
                (1 + (1415038331925467 / 1250000000000000 : ℝ)) =
              (1326398855274549 / 5330076663850934 : ℝ)
            by
        norm_num];
        exact hau374)
  have hat1 :
    (Real.pi / 2 - (2 * (152436035464757284741 / 625000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1326398855274549 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1326398855274549 : ℝ) =
              (1326398855274549 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau373)
  have hat2 :
    Real.arctan (250000000000000 / 1768531807032731 : ℝ) ≤
      (175537173293389352119 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1768531807032731 : ℚ))
        (U := (175537173293389352119 / 1250000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (9007789687161 / 32000000000000 : ℚ))
      (lo := (5305595421098193 / 10000000000000000 : ℚ))
      (hi := (1326398855274549 / 2500000000000000 : ℚ))
      (s := (5305595421098193 / 10000000000000000 : ℚ))
      (r₁ := (41007789687161 / 32000000000000 : ℚ))
      (r₂ := (9187789687161 / 32000000000000 : ℚ))
      (z₁ := (2500000000000000 / 1326398855274549 : ℚ))
      (z₂ := (250000000000000 / 1768531807032731 : ℚ))
      (L := (1240130691140485734679 / 5000000000000000000000 : ℚ))
      (U := (-(12478605076626120675669 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_302 :
    ((1244868006543635756541 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12436386238777361036033 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5317030851949791 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2443436214313161845841 / 10000000000000000000000 : ℝ))) -
              6 * (10947785663169174833 / 78125000000000000000 : ℝ)))) ≤
      Vfield (723732917263 / 2560000000000 : ℝ) := by
  have hL1 :
    (1244868006543635756541 / 5000000000000000000000 : ℝ) ≤
      Real.log (3283732917263 / 2560000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (3283732917263 / 2560000000000 : ℚ))
        (L := (1244868006543635756541 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (738132917263 / 2560000000000 : ℝ) ≤
      (-(12436386238777361036033 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (738132917263 / 2560000000000 : ℚ))
        (r' := (738132917263 / 640000000000 : ℚ))
        (U := (-(12436386238777361036033 / 10000000000000000000000 : ℚ)))
        (U' := (1426557367222638963967 / 10000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau376 :
    Real.arctan (2658515425974897 / 10662835356086779 : ℝ) ≤
      (2443436214313161845841 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2658515425974897 / 10662835356086779 : ℚ))
        (U := (2443436214313161845841 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau375 :
    Real.arctan (2658515425974897 / 5000000000000000 : ℝ) ≤
      (2 * (2443436214313161845841 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5662835356086779 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2658515425974897 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2658515425974897 / 5000000000000000 : ℝ) /
                (1 + (5662835356086779 / 5000000000000000 : ℝ)) =
              (2658515425974897 / 10662835356086779 : ℝ)
            by
        norm_num];
        exact hau376)
  have hat1 :
    (Real.pi / 2 - (2 * (2443436214313161845841 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2658515425974897 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2658515425974897 : ℝ) =
              (2658515425974897 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau375)
  have hat2 :
    Real.arctan (250000000000000 / 1772343617316597 : ℝ) ≤
      (10947785663169174833 / 78125000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1772343617316597 : ℚ))
        (U := (10947785663169174833 / 78125000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (723732917263 / 2560000000000 : ℚ))
      (lo := (5317030851949791 / 10000000000000000 : ℚ))
      (hi := (2658515425974897 / 5000000000000000 : ℚ))
      (s := (5317030851949791 / 10000000000000000 : ℚ))
      (r₁ := (3283732917263 / 2560000000000 : ℚ))
      (r₂ := (738132917263 / 2560000000000 : ℚ))
      (z₁ := (5000000000000000 / 2658515425974897 : ℚ))
      (z₂ := (250000000000000 / 1772343617316597 : ℚ))
      (L := (1244868006543635756541 / 5000000000000000000000 : ℚ))
      (U := (-(12436386238777361036033 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_303 :
    ((2499201675527205748003 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6197172447429658443921 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((532844174114663 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2447882078016176642779 / 10000000000000000000000 : ℝ))) -
              6 * (349588661375526816723 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (4542766622207 / 16000000000000 : ℝ) := by
  have hL1 :
    (2499201675527205748003 / 10000000000000000000000 : ℝ) ≤
      Real.log (20542766622207 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (20542766622207 / 16000000000000 : ℚ))
        (L := (2499201675527205748003 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (4632766622207 / 16000000000000 : ℝ) ≤
      (-(6197172447429658443921 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4632766622207 / 16000000000000 : ℚ))
        (r' := (4632766622207 / 4000000000000 : ℚ))
        (U := (-(6197172447429658443921 / 5000000000000000000000 : ℚ)))
        (U' := (734299355570341556079 / 5000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau378 :
    Real.arctan (5328441741146633 / 21331032229624701 : ℝ) ≤
      (2447882078016176642779 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5328441741146633 / 21331032229624701 : ℚ))
        (U := (2447882078016176642779 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau377 :
    Real.arctan (5328441741146633 / 10000000000000000 : ℝ) ≤
      (2 * (2447882078016176642779 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11331032229624701 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5328441741146633 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5328441741146633 / 10000000000000000 : ℝ) /
                (1 + (11331032229624701 / 10000000000000000 : ℝ)) =
              (5328441741146633 / 21331032229624701 : ℝ)
            by
        norm_num];
        exact hau378)
  have hat1 :
    (Real.pi / 2 - (2 * (2447882078016176642779 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5328441741146633 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5328441741146633 : ℝ) =
              (5328441741146633 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau377)
  have hat2 :
    Real.arctan (75000000000000 / 532844174114663 : ℝ) ≤
      (349588661375526816723 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (75000000000000 / 532844174114663 : ℚ))
        (U := (349588661375526816723 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4542766622207 / 16000000000000 : ℚ))
      (lo := (532844174114663 / 1000000000000000 : ℚ))
      (hi := (5328441741146633 / 10000000000000000 : ℚ))
      (s := (532844174114663 / 1000000000000000 : ℚ))
      (r₁ := (20542766622207 / 16000000000000 : ℚ))
      (r₂ := (4632766622207 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 5328441741146633 : ℚ))
      (z₂ := (75000000000000 / 532844174114663 : ℚ))
      (L := (2499201675527205748003 / 10000000000000000000000 : ℚ))
      (U := (-(6197172447429658443921 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_304 :
    ((62598278722809241977 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6186695158982756371369 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((666767253982059 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1225049934248501779659 / 5000000000000000000000 : ℝ))) -
              6 * (698440355903575839597 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (36419876534909 / 128000000000000 : ℝ) := by
  have hL1 :
    (62598278722809241977 / 250000000000000000000 : ℝ) ≤
      Real.log (164419876534909 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (164419876534909 / 128000000000000 : ℚ))
        (L := (62598278722809241977 / 250000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (37139876534909 / 128000000000000 : ℝ) ≤
      (-(6186695158982756371369 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (37139876534909 / 128000000000000 : ℚ))
        (r' := (37139876534909 / 32000000000000 : ℚ))
        (U := (-(6186695158982756371369 / 5000000000000000000000 : ℚ)))
        (U' := (744776644017243628631 / 5000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau380 :
    Real.arctan (1066827606371295 / 4266742407446401 : ℝ) ≤
      (1225049934248501779659 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1066827606371295 / 4266742407446401 : ℚ))
        (U := (1225049934248501779659 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau379 :
    Real.arctan (213365521274259 / 400000000000000 : ℝ) ≤
      (2 * (1225049934248501779659 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2266742407446401 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (213365521274259 / 400000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (213365521274259 / 400000000000000 : ℝ) /
                (1 + (2266742407446401 / 2000000000000000 : ℝ)) =
              (1066827606371295 / 4266742407446401 : ℝ)
            by
        norm_num];
        exact hau380)
  have hat1 :
    (Real.pi / 2 - (2 * (1225049934248501779659 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (400000000000000 / 213365521274259 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (400000000000000 / 213365521274259 : ℝ) =
              (213365521274259 / 400000000000000 : ℝ)
            by
        norm_num];
        exact hau379)
  have hat2 :
    Real.arctan (31250000000000 / 222255751327353 : ℝ) ≤
      (698440355903575839597 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (31250000000000 / 222255751327353 : ℚ))
        (U := (698440355903575839597 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (36419876534909 / 128000000000000 : ℚ))
      (lo := (666767253982059 / 1250000000000000 : ℚ))
      (hi := (213365521274259 / 400000000000000 : ℚ))
      (s := (666767253982059 / 1250000000000000 : ℚ))
      (r₁ := (164419876534909 / 128000000000000 : ℚ))
      (r₂ := (37139876534909 / 128000000000000 : ℚ))
      (z₁ := (400000000000000 / 213365521274259 : ℚ))
      (z₂ := (31250000000000 / 222255751327353 : ℚ))
      (L := (62598278722809241977 / 250000000000000000000 : ℚ))
      (U := (-(6186695158982756371369 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_305 :
    ((1254329193281513271393 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2470495911739800849337 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5339828246020797 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (245231424585502598539 / 1000000000000000000000 : ℝ))) -
              6 * (348852857314937662517 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (18248810046081 / 64000000000000 : ℝ) := by
  have hL1 :
    (1254329193281513271393 / 5000000000000000000000 : ℝ) ≤
      Real.log (82248810046081 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (82248810046081 / 64000000000000 : ℚ))
        (L := (1254329193281513271393 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (18608810046081 / 64000000000000 : ℝ) ≤
      (-(2470495911739800849337 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18608810046081 / 64000000000000 : ℚ))
        (r' := (18608810046081 / 16000000000000 : ℚ))
        (U := (-(2470495911739800849337 / 2000000000000000000000 : ℚ)))
        (U' := (302092809460199150663 / 2000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau382 :
    Real.arctan (762832606574400 / 3048055887337151 : ℝ) ≤
      (245231424585502598539 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (762832606574400 / 3048055887337151 : ℚ))
        (U := (245231424585502598539 / 1000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau381 :
    Real.arctan (3337392653763 / 6250000000000 : ℝ) ≤
      (2 * (245231424585502598539 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11336391211360057 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3337392653763 / 6250000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3337392653763 / 6250000000000 : ℝ) /
                (1 + (11336391211360057 / 10000000000000000 : ℝ)) =
              (762832606574400 / 3048055887337151 : ℝ)
            by
        norm_num];
        exact hau382)
  have hat1 :
    (Real.pi / 2 - (2 * (245231424585502598539 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (6250000000000 / 3337392653763 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (6250000000000 / 3337392653763 : ℝ) = (3337392653763 / 6250000000000 : ℝ) by
            norm_num];
        exact hau381)
  have hat2 :
    Real.arctan (250000000000000 / 1779942748673599 : ℝ) ≤
      (348852857314937662517 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1779942748673599 : ℚ))
        (U := (348852857314937662517 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (18248810046081 / 64000000000000 : ℚ))
      (lo := (5339828246020797 / 10000000000000000 : ℚ))
      (hi := (3337392653763 / 6250000000000 : ℚ))
      (s := (5339828246020797 / 10000000000000000 : ℚ))
      (r₁ := (82248810046081 / 64000000000000 : ℚ))
      (r₂ := (18608810046081 / 64000000000000 : ℚ))
      (z₁ := (6250000000000 / 3337392653763 : ℚ))
      (z₂ := (250000000000000 / 1779942748673599 : ℚ))
      (L := (1254329193281513271393 / 5000000000000000000000 : ℚ))
      (U := (-(2470495911739800849337 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_306 :
    ((2513383390591947328477 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6165806217095040688203 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((167047262595149 / 312500000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2454525220863704290673 / 10000000000000000000000 : ℝ))) -
              6 * (1393946773448474205463 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (7315072729883 / 25600000000000 : ℝ) := by
  have hL1 :
    (2513383390591947328477 / 10000000000000000000000 : ℝ) ≤
      Real.log (32915072729883 / 25600000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (32915072729883 / 25600000000000 : ℚ))
        (L := (2513383390591947328477 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (7459072729883 / 25600000000000 : ℝ) ≤
      (-(6165806217095040688203 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7459072729883 / 25600000000000 : ℚ))
        (r' := (7459072729883 / 6400000000000 : ℚ))
        (U := (-(6165806217095040688203 / 5000000000000000000000 : ℚ)))
        (U' := (765665585904959311797 / 5000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau384 :
    Real.arctan (5345512403044771 / 21339069752457891 : ℝ) ≤
      (2454525220863704290673 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5345512403044771 / 21339069752457891 : ℚ))
        (U := (2454525220863704290673 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau383 :
    Real.arctan (5345512403044771 / 10000000000000000 : ℝ) ≤
      (2 * (2454525220863704290673 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11339069752457891 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5345512403044771 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5345512403044771 / 10000000000000000 : ℝ) /
                (1 + (11339069752457891 / 10000000000000000 : ℝ)) =
              (5345512403044771 / 21339069752457891 : ℝ)
            by
        norm_num];
        exact hau384)
  have hat1 :
    (Real.pi / 2 - (2 * (2454525220863704290673 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5345512403044771 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5345512403044771 : ℝ) =
              (5345512403044771 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau383)
  have hat2 :
    Real.arctan (23437500000000 / 167047262595149 : ℝ) ≤
      (1393946773448474205463 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (23437500000000 / 167047262595149 : ℚ))
        (U := (1393946773448474205463 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (7315072729883 / 25600000000000 : ℚ))
      (lo := (167047262595149 / 312500000000000 : ℚ))
      (hi := (5345512403044771 / 10000000000000000 : ℚ))
      (s := (167047262595149 / 312500000000000 : ℚ))
      (r₁ := (32915072729883 / 25600000000000 : ℚ))
      (r₂ := (7459072729883 / 25600000000000 : ℚ))
      (z₁ := (10000000000000000 / 5345512403044771 : ℚ))
      (z₂ := (23437500000000 / 167047262595149 : ℚ))
      (L := (2513383390591947328477 / 10000000000000000000000 : ℚ))
      (U := (-(6165806217095040688203 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_307 :
    ((314763270388613698039 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6155394381355720490859 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1337797630557621 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1228366402120582497673 / 5000000000000000000000 : ℝ))) -
              6 * (278497344028178964147 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (9163276801667 / 32000000000000 : ℝ) := by
  have hL1 :
    (314763270388613698039 / 1250000000000000000000 : ℝ) ≤
      Real.log (41163276801667 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (41163276801667 / 32000000000000 : ℚ))
        (L := (314763270388613698039 / 1250000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (9343276801667 / 32000000000000 : ℝ) ≤
      (-(6155394381355720490859 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9343276801667 / 32000000000000 : ℚ))
        (r' := (9343276801667 / 8000000000000 : ℚ))
        (U := (-(6155394381355720490859 / 5000000000000000000000 : ℚ)))
        (U' := (776077421644279509141 / 5000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau386 :
    Real.arctan (5351190522230487 / 21341747660974007 : ℝ) ≤
      (1228366402120582497673 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5351190522230487 / 21341747660974007 : ℚ))
        (U := (1228366402120582497673 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau385 :
    Real.arctan (5351190522230487 / 10000000000000000 : ℝ) ≤
      (2 * (1228366402120582497673 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11341747660974007 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5351190522230487 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5351190522230487 / 10000000000000000 : ℝ) /
                (1 + (11341747660974007 / 10000000000000000 : ℝ)) =
              (5351190522230487 / 21341747660974007 : ℝ)
            by
        norm_num];
        exact hau386)
  have hat1 :
    (Real.pi / 2 - (2 * (1228366402120582497673 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5351190522230487 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5351190522230487 : ℝ) =
              (5351190522230487 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau385)
  have hat2 :
    Real.arctan (62500000000000 / 445932543519207 : ℝ) ≤
      (278497344028178964147 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (62500000000000 / 445932543519207 : ℚ))
        (U := (278497344028178964147 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (9163276801667 / 32000000000000 : ℚ))
      (lo := (1337797630557621 / 2500000000000000 : ℚ))
      (hi := (5351190522230487 / 10000000000000000 : ℚ))
      (s := (1337797630557621 / 2500000000000000 : ℚ))
      (r₁ := (41163276801667 / 32000000000000 : ℚ))
      (r₂ := (9343276801667 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 5351190522230487 : ℚ))
      (z₂ := (62500000000000 / 445932543519207 : ℚ))
      (L := (314763270388613698039 / 1250000000000000000000 : ℚ))
      (U := (-(6155394381355720490859 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_308 :
    ((2522826706220703069523 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12290008363668690903519 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1071372524555549 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2458937006650601874589 / 10000000000000000000000 : ℝ))) -
              6 * (347757811320475804929 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (36730850763921 / 128000000000000 : ℝ) := by
  have hL1 :
    (2522826706220703069523 / 10000000000000000000000 : ℝ) ≤
      Real.log (164730850763921 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (164730850763921 / 128000000000000 : ℚ))
        (L := (2522826706220703069523 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (37450850763921 / 128000000000000 : ℝ) ≤
      (-(12290008363668690903519 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (37450850763921 / 128000000000000 : ℚ))
        (r' := (37450850763921 / 32000000000000 : ℚ))
        (U := (-(12290008363668690903519 / 10000000000000000000000 : ℚ)))
        (U' := (1572935242331309096481 / 10000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau388 :
    Real.arctan (2678431311388874 / 10672212468678189 : ℝ) ≤
      (2458937006650601874589 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2678431311388874 / 10672212468678189 : ℚ))
        (U := (2458937006650601874589 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau387 :
    Real.arctan (1339215655694437 / 2500000000000000 : ℝ) ≤
      (2 * (2458937006650601874589 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5672212468678189 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1339215655694437 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1339215655694437 / 2500000000000000 : ℝ) /
                (1 + (5672212468678189 / 5000000000000000 : ℝ)) =
              (2678431311388874 / 10672212468678189 : ℝ)
            by
        norm_num];
        exact hau388)
  have hat1 :
    (Real.pi / 2 - (2 * (2458937006650601874589 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1339215655694437 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1339215655694437 : ℝ) =
              (1339215655694437 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau387)
  have hat2 :
    Real.arctan (150000000000000 / 1071372524555549 : ℝ) ≤
      (347757811320475804929 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 1071372524555549 : ℚ))
        (U := (347757811320475804929 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (36730850763921 / 128000000000000 : ℚ))
      (lo := (1071372524555549 / 2000000000000000 : ℚ))
      (hi := (1339215655694437 / 2500000000000000 : ℚ))
      (s := (1071372524555549 / 2000000000000000 : ℚ))
      (r₁ := (164730850763921 / 128000000000000 : ℚ))
      (r₂ := (37450850763921 / 128000000000000 : ℚ))
      (z₁ := (2500000000000000 / 1339215655694437 : ℚ))
      (z₂ := (150000000000000 / 1071372524555549 : ℚ))
      (L := (2522826706220703069523 / 10000000000000000000000 : ℚ))
      (U := (-(12290008363668690903519 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_309 :
    ((2527545022031135393343 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12269271057590952551449 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5362528723784813 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (492227567740135145223 / 2000000000000000000000 : ℝ))) -
              6 * (1389580324992042662019 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (18404297160587 / 64000000000000 : ℝ) := by
  have hL1 :
    (2527545022031135393343 / 10000000000000000000000 : ℝ) ≤
      Real.log (82404297160587 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (82404297160587 / 64000000000000 : ℚ))
        (L := (2527545022031135393343 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (18764297160587 / 64000000000000 : ℝ) ≤
      (-(12269271057590952551449 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18764297160587 / 64000000000000 : ℚ))
        (r' := (18764297160587 / 16000000000000 : ℚ))
        (U := (-(12269271057590952551449 / 10000000000000000000000 : ℚ)))
        (U' := (1593672548409047448551 / 10000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau390 :
    Real.arctan (335158045236551 / 1334193848878278 : ℝ) ≤
      (492227567740135145223 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (335158045236551 / 1334193848878278 : ℚ))
        (U := (492227567740135145223 / 2000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau389 :
    Real.arctan (335158045236551 / 625000000000000 : ℝ) ≤
      (2 * (492227567740135145223 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (354596924439139 / 312500000000000 : ℝ) ≤
          Real.sqrt (1 + (335158045236551 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (335158045236551 / 625000000000000 : ℝ) /
                (1 + (354596924439139 / 312500000000000 : ℝ)) =
              (335158045236551 / 1334193848878278 : ℝ)
            by
        norm_num];
        exact hau390)
  have hat1 :
    (Real.pi / 2 - (2 * (492227567740135145223 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 335158045236551 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 335158045236551 : ℝ) =
              (335158045236551 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau389)
  have hat2 :
    Real.arctan (750000000000000 / 5362528723784813 : ℝ) ≤
      (1389580324992042662019 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 5362528723784813 : ℚ))
        (U := (1389580324992042662019 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (18404297160587 / 64000000000000 : ℚ))
      (lo := (5362528723784813 / 10000000000000000 : ℚ))
      (hi := (335158045236551 / 625000000000000 : ℚ))
      (s := (5362528723784813 / 10000000000000000 : ℚ))
      (r₁ := (82404297160587 / 64000000000000 : ℚ))
      (r₂ := (18764297160587 / 64000000000000 : ℚ))
      (z₁ := (625000000000000 / 335158045236551 : ℚ))
      (z₂ := (750000000000000 / 5362528723784813 : ℚ))
      (L := (2527545022031135393343 / 10000000000000000000000 : ℚ))
      (U := (-(12269271057590952551449 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_310 :
    ((50645222252820752813 / 200000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(122485766661215607187 / 100000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1073637768849831 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (24633353109459053127 / 100000000000000000000 : ℝ))) -
              6 * (277626787113173012921 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (36886337878427 / 128000000000000 : ℝ) := by
  have hL1 :
    (50645222252820752813 / 200000000000000000000 : ℝ) ≤
      Real.log (164886337878427 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (164886337878427 / 128000000000000 : ℚ))
        (L := (50645222252820752813 / 200000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (37606337878427 / 128000000000000 : ℝ) ≤
      (-(122485766661215607187 / 100000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (37606337878427 / 128000000000000 : ℚ))
        (r' := (37606337878427 / 32000000000000 : ℚ))
        (U := (-(122485766661215607187 / 100000000000000000000 : ℚ)))
        (U' := (16143669398784392813 / 100000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau392 :
    Real.arctan (5368188844249158 / 21349777595509133 : ℝ) ≤
      (24633353109459053127 / 100000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5368188844249158 / 21349777595509133 : ℚ))
        (U := (24633353109459053127 / 100000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau391 :
    Real.arctan (2684094422124579 / 5000000000000000 : ℝ) ≤
      (2 * (24633353109459053127 / 100000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11349777595509133 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2684094422124579 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2684094422124579 / 5000000000000000 : ℝ) /
                (1 + (11349777595509133 / 10000000000000000 : ℝ)) =
              (5368188844249158 / 21349777595509133 : ℝ)
            by
        norm_num];
        exact hau392)
  have hat1 :
    (Real.pi / 2 - (2 * (24633353109459053127 / 100000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2684094422124579 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2684094422124579 : ℝ) =
              (2684094422124579 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau391)
  have hat2 :
    Real.arctan (50000000000000 / 357879256283277 : ℝ) ≤
      (277626787113173012921 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (50000000000000 / 357879256283277 : ℚ))
        (U := (277626787113173012921 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (36886337878427 / 128000000000000 : ℚ))
      (lo := (1073637768849831 / 2000000000000000 : ℚ))
      (hi := (2684094422124579 / 5000000000000000 : ℚ))
      (s := (1073637768849831 / 2000000000000000 : ℚ))
      (r₁ := (164886337878427 / 128000000000000 : ℚ))
      (r₂ := (37606337878427 / 128000000000000 : ℚ))
      (z₁ := (5000000000000000 / 2684094422124579 : ℚ))
      (z₂ := (50000000000000 / 357879256283277 : ℚ))
      (L := (50645222252820752813 / 200000000000000000000 : ℚ))
      (U := (-(122485766661215607187 / 100000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_311 :
    ((2536974980148269984337 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12227925012008859438829 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2686921501534097 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (308191179235882659497 / 1250000000000000000000 : ℝ))) -
              6 * (693346026735151028923 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (231025508973 / 800000000000 : ℝ) := by
  have hL1 :
    (2536974980148269984337 / 10000000000000000000000 : ℝ) ≤
      Real.log (1031025508973 / 800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1031025508973 / 800000000000 : ℚ))
        (L := (2536974980148269984337 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (235525508973 / 800000000000 : ℝ) ≤
      (-(12227925012008859438829 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (235525508973 / 800000000000 : ℚ))
        (r' := (235525508973 / 200000000000 : ℚ))
        (U := (-(12227925012008859438829 / 10000000000000000000000 : ℚ)))
        (U' := (1635018593991140561171 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau394 :
    Real.arctan (5373843003068197 / 21352452978172822 : ℝ) ≤
      (308191179235882659497 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5373843003068197 / 21352452978172822 : ℚ))
        (U := (308191179235882659497 / 1250000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau393 :
    Real.arctan (5373843003068197 / 10000000000000000 : ℝ) ≤
      (2 * (308191179235882659497 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5676226489086411 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5373843003068197 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5373843003068197 / 10000000000000000 : ℝ) /
                (1 + (5676226489086411 / 5000000000000000 : ℝ)) =
              (5373843003068197 / 21352452978172822 : ℝ)
            by
        norm_num];
        exact hau394)
  have hat1 :
    (Real.pi / 2 - (2 * (308191179235882659497 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5373843003068197 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5373843003068197 : ℝ) =
              (5373843003068197 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau393)
  have hat2 :
    Real.arctan (375000000000000 / 2686921501534097 : ℝ) ≤
      (693346026735151028923 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 2686921501534097 : ℚ))
        (U := (693346026735151028923 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (231025508973 / 800000000000 : ℚ))
      (lo := (2686921501534097 / 5000000000000000 : ℚ))
      (hi := (5373843003068197 / 10000000000000000 : ℚ))
      (s := (2686921501534097 / 5000000000000000 : ℚ))
      (r₁ := (1031025508973 / 800000000000 : ℚ))
      (r₂ := (235525508973 / 800000000000 : ℚ))
      (z₁ := (10000000000000000 / 5373843003068197 : ℚ))
      (z₂ := (375000000000000 / 2686921501534097 : ℚ))
      (L := (2536974980148269984337 / 10000000000000000000000 : ℚ))
      (U := (-(12227925012008859438829 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_312 :
    ((2541686626647727284469 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3051828979774273160183 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5379491219040039 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1233860108985775068049 / 5000000000000000000000 : ℝ))) -
              6 * (277050931068611634373 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (37041824992933 / 128000000000000 : ℝ) := by
  have hL1 :
    (2541686626647727284469 / 10000000000000000000000 : ℝ) ≤
      Real.log (165041824992933 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (165041824992933 / 128000000000000 : ℚ))
        (L := (2541686626647727284469 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (37761824992933 / 128000000000000 : ℝ) ≤
      (-(3051828979774273160183 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (37761824992933 / 128000000000000 : ℚ))
        (r' := (37761824992933 / 32000000000000 : ℚ))
        (U := (-(3051828979774273160183 / 2500000000000000000000 : ℚ)))
        (U' := (413906921725726839817 / 2500000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau396 :
    Real.arctan (5379491219040042 / 21355127730489379 : ℝ) ≤
      (1233860108985775068049 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5379491219040042 / 21355127730489379 : ℚ))
        (U := (1233860108985775068049 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau395 :
    Real.arctan (2689745609520021 / 5000000000000000 : ℝ) ≤
      (2 * (1233860108985775068049 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11355127730489379 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2689745609520021 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2689745609520021 / 5000000000000000 : ℝ) /
                (1 + (11355127730489379 / 10000000000000000 : ℝ)) =
              (5379491219040042 / 21355127730489379 : ℝ)
            by
        norm_num];
        exact hau396)
  have hat1 :
    (Real.pi / 2 - (2 * (1233860108985775068049 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2689745609520021 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2689745609520021 : ℝ) =
              (2689745609520021 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau395)
  have hat2 :
    Real.arctan (250000000000000 / 1793163739680013 : ℝ) ≤
      (277050931068611634373 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1793163739680013 : ℚ))
        (U := (277050931068611634373 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (37041824992933 / 128000000000000 : ℚ))
      (lo := (5379491219040039 / 10000000000000000 : ℚ))
      (hi := (2689745609520021 / 5000000000000000 : ℚ))
      (s := (5379491219040039 / 10000000000000000 : ℚ))
      (r₁ := (165041824992933 / 128000000000000 : ℚ))
      (r₂ := (37761824992933 / 128000000000000 : ℚ))
      (z₁ := (5000000000000000 / 2689745609520021 : ℚ))
      (z₂ := (250000000000000 / 1793163739680013 : ℚ))
      (L := (2541686626647727284469 / 10000000000000000000000 : ℚ))
      (U := (-(3051828979774273160183 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
