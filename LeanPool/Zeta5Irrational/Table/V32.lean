/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalSeries
import LeanPool.Zeta5Irrational.Table.LowerCertificate

public import LeanPool.Zeta5Irrational.Energy
import LeanPool.Zeta5Irrational.Certificates
import LeanPool.Zeta5Irrational.PotentialV
import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # V32: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

lemma V_385 :
    ((403007937624435709943 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9517350080763106229959 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6168027287652999 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2763414600899822286143 / 10000000000000000000000 : ℝ))) -
              6 * (605003909804122796891 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (48697037595177 / 128000000000000 : ℝ) := by
  have hL1 :
    (403007937624435709943 / 1250000000000000000000 : ℝ) ≤
      Real.log (176697037595177 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (176697037595177 / 128000000000000 : ℚ))
        (L := (403007937624435709943 / 1250000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (49417037595177 / 128000000000000 : ℝ) ≤
      (-(9517350080763106229959 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (49417037595177 / 128000000000000 : ℝ) = (49417037595177 / 32000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (49417037595177 / 32000000000000 : ℚ))
             (U := (4345593525236893770041 / 10000000000000000000000 : ℚ))
             10 (by decide +kernel)) :
          Real.log (49417037595177 / 32000000000000 : ℝ) ≤
            (4345593525236893770041 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau542 :
    Real.arctan (6168027287653002 / 21749236597380785 : ℝ) ≤
      (2763414600899822286143 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6168027287653002 / 21749236597380785 : ℚ))
        (U := (2763414600899822286143 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau541 :
    Real.arctan (3084013643826501 / 5000000000000000 : ℝ) ≤
      (2 * (2763414600899822286143 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2349847319476157 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3084013643826501 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3084013643826501 / 5000000000000000 : ℝ) /
                (1 + (2349847319476157 / 2000000000000000 : ℝ)) =
              (6168027287653002 / 21749236597380785 : ℝ)
            by
        norm_num];
        exact hau542)
  have hat1 :
    (Real.pi / 2 - (2 * (2763414600899822286143 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3084013643826501 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3084013643826501 : ℝ) =
              (3084013643826501 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau541)
  have hat2 :
    Real.arctan (250000000000000 / 2056009095884333 : ℝ) ≤
      (605003909804122796891 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2056009095884333 : ℚ))
        (U := (605003909804122796891 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (48697037595177 / 128000000000000 : ℚ))
      (lo := (6168027287652999 / 10000000000000000 : ℚ))
      (hi := (3084013643826501 / 5000000000000000 : ℚ))
      (s := (6168027287652999 / 10000000000000000 : ℚ))
      (r₁ := (176697037595177 / 128000000000000 : ℚ))
      (r₂ := (49417037595177 / 128000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3084013643826501 : ℚ))
      (z₂ := (250000000000000 / 2056009095884333 : ℚ))
      (L := (403007937624435709943 / 1250000000000000000000 : ℚ))
      (U := (-(9517350080763106229959 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_386 :
    ((3228800271091844667397 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4750211732793883134469 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((617332687008163 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2765333665127458345457 / 10000000000000000000000 : ℝ))) -
              6 * (1208979167261253981733 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (12195188686359 / 32000000000000 : ℝ) := by
  have hL1 :
    (3228800271091844667397 / 10000000000000000000000 : ℝ) ≤
      Real.log (44195188686359 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (44195188686359 / 32000000000000 : ℚ))
        (L := (3228800271091844667397 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (12375188686359 / 32000000000000 : ℝ) ≤
      (-(4750211732793883134469 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (12375188686359 / 32000000000000 : ℝ) = (12375188686359 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (12375188686359 / 8000000000000 : ℚ))
             (U := (2181260070206116865531 / 5000000000000000000000 : ℚ))
             10 (by decide +kernel)) :
          Real.log (12375188686359 / 8000000000000 : ℝ) ≤
            (2181260070206116865531 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau544 :
    Real.arctan (6173326870081633 / 21752019598557171 : ℝ) ≤
      (2765333665127458345457 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6173326870081633 / 21752019598557171 : ℚ))
        (U := (2765333665127458345457 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau543 :
    Real.arctan (6173326870081633 / 10000000000000000 : ℝ) ≤
      (2 * (2765333665127458345457 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11752019598557171 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6173326870081633 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6173326870081633 / 10000000000000000 : ℝ) /
                (1 + (11752019598557171 / 10000000000000000 : ℝ)) =
              (6173326870081633 / 21752019598557171 : ℝ)
            by
        norm_num];
        exact hau544)
  have hat1 :
    (Real.pi / 2 - (2 * (2765333665127458345457 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6173326870081633 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6173326870081633 : ℝ) =
              (6173326870081633 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau543)
  have hat2 :
    Real.arctan (75000000000000 / 617332687008163 : ℝ) ≤
      (1208979167261253981733 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (75000000000000 / 617332687008163 : ℚ))
        (U := (1208979167261253981733 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (12195188686359 / 32000000000000 : ℚ))
      (lo := (617332687008163 / 1000000000000000 : ℚ))
      (hi := (6173326870081633 / 10000000000000000 : ℚ))
      (s := (617332687008163 / 1000000000000000 : ℚ))
      (r₁ := (44195188686359 / 32000000000000 : ℚ))
      (r₂ := (12375188686359 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6173326870081633 : ℚ))
      (z₂ := (75000000000000 / 617332687008163 : ℚ))
      (L := (3228800271091844667397 / 10000000000000000000000 : ℚ))
      (U := (-(4750211732793883134469 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_387 :
    ((202095924909459542751 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4741762726517407558013 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6178621906907049 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1383625087755914228753 / 5000000000000000000000 : ℝ))) -
              6 * (301988283486676190467 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (9772894379139 / 25600000000000 : ℝ) := by
  have hL1 :
    (202095924909459542751 / 625000000000000000000 : ℝ) ≤
      Real.log (35372894379139 / 25600000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (35372894379139 / 25600000000000 : ℚ))
        (L := (202095924909459542751 / 625000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (9916894379139 / 25600000000000 : ℝ) ≤
      (-(4741762726517407558013 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (9916894379139 / 25600000000000 : ℝ) = (9916894379139 / 6400000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (9916894379139 / 6400000000000 : ℚ))
             (U := (2189709076482592441987 / 5000000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (9916894379139 / 6400000000000 : ℝ) ≤
            (2189709076482592441987 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau546 :
    Real.arctan (2059540635635684 / 7251600646948593 : ℝ) ≤
      (1383625087755914228753 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2059540635635684 / 7251600646948593 : ℚ))
        (U := (1383625087755914228753 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau545 :
    Real.arctan (1544655476726763 / 2500000000000000 : ℝ) ≤
      (2 * (1383625087755914228753 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11754801940845779 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1544655476726763 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1544655476726763 / 2500000000000000 : ℝ) /
                (1 + (11754801940845779 / 10000000000000000 : ℝ)) =
              (2059540635635684 / 7251600646948593 : ℝ)
            by
        norm_num];
        exact hau546)
  have hat1 :
    (Real.pi / 2 - (2 * (1383625087755914228753 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1544655476726763 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1544655476726763 : ℝ) =
              (1544655476726763 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau545)
  have hat2 :
    Real.arctan (250000000000000 / 2059540635635683 : ℝ) ≤
      (301988283486676190467 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2059540635635683 : ℚ))
        (U := (301988283486676190467 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (9772894379139 / 25600000000000 : ℚ))
      (lo := (6178621906907049 / 10000000000000000 : ℚ))
      (hi := (1544655476726763 / 2500000000000000 : ℚ))
      (s := (6178621906907049 / 10000000000000000 : ℚ))
      (r₁ := (35372894379139 / 25600000000000 : ℚ))
      (r₂ := (9916894379139 / 25600000000000 : ℚ))
      (z₁ := (2500000000000000 / 1544655476726763 : ℚ))
      (z₂ := (250000000000000 / 2059540635635683 : ℚ))
      (L := (202095924909459542751 / 625000000000000000000 : ℚ))
      (U := (-(4741762726517407558013 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_388 :
    ((323826708549657002721 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9466655946601782328347 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6183912409805911 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (173072758668396268933 / 625000000000000000000 : ℝ))) -
              6 * (1206929708569435187719 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (24474094522977 / 64000000000000 : ℝ) := by
  have hL1 :
    (323826708549657002721 / 1000000000000000000000 : ℝ) ≤
      Real.log (88474094522977 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (88474094522977 / 64000000000000 : ℚ))
        (L := (323826708549657002721 / 1000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (24834094522977 / 64000000000000 : ℝ) ≤
      (-(9466655946601782328347 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (24834094522977 / 64000000000000 : ℝ) = (24834094522977 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (24834094522977 / 16000000000000 : ℚ))
             (U := (4396287659398217671653 / 10000000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (24834094522977 / 16000000000000 : ℝ) ≤
            (4396287659398217671653 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau548 :
    Real.arctan (3091956204902957 / 10878791812357186 : ℝ) ≤
      (173072758668396268933 / 625000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3091956204902957 / 10878791812357186 : ℚ))
        (U := (173072758668396268933 / 625000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau547 :
    Real.arctan (3091956204902957 / 5000000000000000 : ℝ) ≤
      (2 * (173072758668396268933 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2939395906178593 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (3091956204902957 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3091956204902957 / 5000000000000000 : ℝ) /
                (1 + (2939395906178593 / 2500000000000000 : ℝ)) =
              (3091956204902957 / 10878791812357186 : ℝ)
            by
        norm_num];
        exact hau548)
  have hat1 :
    (Real.pi / 2 - (2 * (173072758668396268933 / 625000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3091956204902957 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3091956204902957 : ℝ) =
              (3091956204902957 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau547)
  have hat2 :
    Real.arctan (750000000000000 / 6183912409805911 : ℝ) ≤
      (1206929708569435187719 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 6183912409805911 : ℚ))
        (U := (1206929708569435187719 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (24474094522977 / 64000000000000 : ℚ))
      (lo := (6183912409805911 / 10000000000000000 : ℚ))
      (hi := (3091956204902957 / 5000000000000000 : ℚ))
      (s := (6183912409805911 / 10000000000000000 : ℚ))
      (r₁ := (88474094522977 / 64000000000000 : ℚ))
      (r₂ := (24834094522977 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3091956204902957 : ℚ))
      (z₂ := (750000000000000 / 6183912409805911 : ℚ))
      (L := (323826708549657002721 / 1000000000000000000000 : ℚ))
      (U := (-(9466655946601782328347 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_389 :
    ((405965618289914982473 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9433002068520124417443 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1548619965070337 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (554596889976445321921 / 2000000000000000000000 : ℝ))) -
              6 * (1204890637574057060631 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (6139452918309 / 16000000000000 : ℝ) := by
  have hL1 :
    (405965618289914982473 / 1250000000000000000000 : ℝ) ≤
      Real.log (22139452918309 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (22139452918309 / 16000000000000 : ℚ))
        (L := (405965618289914982473 / 1250000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (6229452918309 / 16000000000000 : ℝ) ≤
      (-(9433002068520124417443 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (6229452918309 / 16000000000000 : ℝ) = (6229452918309 / 4000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (6229452918309 / 4000000000000 : ℚ))
             (U := (4429941537479875582557 / 10000000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (6229452918309 / 4000000000000 : ℝ) ≤
            (4429941537479875582557 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau550 :
    Real.arctan (6194479860281351 / 21763145019059794 : ℝ) ≤
      (554596889976445321921 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6194479860281351 / 21763145019059794 : ℚ))
        (U := (554596889976445321921 / 2000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau549 :
    Real.arctan (6194479860281351 / 10000000000000000 : ℝ) ≤
      (2 * (554596889976445321921 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5881572509529897 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6194479860281351 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6194479860281351 / 10000000000000000 : ℝ) /
                (1 + (5881572509529897 / 5000000000000000 : ℝ)) =
              (6194479860281351 / 21763145019059794 : ℝ)
            by
        norm_num];
        exact hau550)
  have hat1 :
    (Real.pi / 2 - (2 * (554596889976445321921 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6194479860281351 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6194479860281351 : ℝ) =
              (6194479860281351 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau549)
  have hat2 :
    Real.arctan (187500000000000 / 1548619965070337 : ℝ) ≤
      (1204890637574057060631 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 1548619965070337 : ℚ))
        (U := (1204890637574057060631 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (6139452918309 / 16000000000000 : ℚ))
      (lo := (1548619965070337 / 2500000000000000 : ℚ))
      (hi := (6194479860281351 / 10000000000000000 : ℚ))
      (s := (1548619965070337 / 2500000000000000 : ℚ))
      (r₁ := (22139452918309 / 16000000000000 : ℚ))
      (r₂ := (6229452918309 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6194479860281351 : ℚ))
      (z₂ := (187500000000000 / 1548619965070337 : ℚ))
      (L := (405965618289914982473 / 1250000000000000000000 : ℚ))
      (U := (-(9433002068520124417443 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_390 :
    ((203573366905027506113 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4699730534507726419707 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3102514656964207 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2776794651275838889401 / 10000000000000000000000 : ℝ))) -
              6 * (240572373363749729447 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (4928305764699 / 12800000000000 : ℝ) := by
  have hL1 :
    (203573366905027506113 / 625000000000000000000 : ℝ) ≤
      Real.log (17728305764699 / 12800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (17728305764699 / 12800000000000 : ℚ))
        (L := (203573366905027506113 / 625000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (5000305764699 / 12800000000000 : ℝ) ≤
      (-(4699730534507726419707 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (5000305764699 / 12800000000000 : ℝ) = (5000305764699 / 3200000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (5000305764699 / 3200000000000 : ℚ))
             (U := (2231741268492273580293 / 5000000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (5000305764699 / 3200000000000 : ℝ) ≤
            (2231741268492273580293 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau552 :
    Real.arctan (6205029313928417 / 21768703785324488 : ℝ) ≤
      (2776794651275838889401 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6205029313928417 / 21768703785324488 : ℚ))
        (U := (2776794651275838889401 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau551 :
    Real.arctan (6205029313928417 / 10000000000000000 : ℝ) ≤
      (2 * (2776794651275838889401 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1471087973165561 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (6205029313928417 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6205029313928417 / 10000000000000000 : ℝ) /
                (1 + (1471087973165561 / 1250000000000000 : ℝ)) =
              (6205029313928417 / 21768703785324488 : ℝ)
            by
        norm_num];
        exact hau552)
  have hat1 :
    (Real.pi / 2 - (2 * (2776794651275838889401 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6205029313928417 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6205029313928417 : ℝ) =
              (6205029313928417 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau551)
  have hat2 :
    Real.arctan (375000000000000 / 3102514656964207 : ℝ) ≤
      (240572373363749729447 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 3102514656964207 : ℚ))
        (U := (240572373363749729447 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4928305764699 / 12800000000000 : ℚ))
      (lo := (3102514656964207 / 5000000000000000 : ℚ))
      (hi := (6205029313928417 / 10000000000000000 : ℚ))
      (s := (3102514656964207 / 5000000000000000 : ℚ))
      (r₁ := (17728305764699 / 12800000000000 : ℚ))
      (r₂ := (5000305764699 / 12800000000000 : ℚ))
      (z₁ := (10000000000000000 / 6205029313928417 : ℚ))
      (z₂ := (375000000000000 / 3102514656964207 : ℚ))
      (L := (203573366905027506113 / 625000000000000000000 : ℚ))
      (U := (-(4699730534507726419707 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_391 :
    ((816653468713089555349 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2341508048351393276649 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3107780431191633 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (86893587344624066073 / 312500000000000000000 : ℝ))) -
              6 * (1200843309874540748747 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (12362622986877 / 32000000000000 : ℝ) := by
  have hL1 :
    (816653468713089555349 / 2500000000000000000000 : ℝ) ≤
      Real.log (44362622986877 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (44362622986877 / 32000000000000 : ℚ))
        (L := (816653468713089555349 / 2500000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (12542622986877 / 32000000000000 : ℝ) ≤
      (-(2341508048351393276649 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (12542622986877 / 32000000000000 : ℝ) = (12542622986877 / 8000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (12542622986877 / 8000000000000 : ℚ))
             (U := (1124227853148606723351 / 2500000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (12542622986877 / 8000000000000 : ℝ) ≤
            (1124227853148606723351 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau554 :
    Real.arctan (6215560862383269 / 21774259927230697 : ℝ) ≤
      (86893587344624066073 / 312500000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6215560862383269 / 21774259927230697 : ℚ))
        (U := (86893587344624066073 / 312500000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau553 :
    Real.arctan (6215560862383269 / 10000000000000000 : ℝ) ≤
      (2 * (86893587344624066073 / 312500000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11774259927230697 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6215560862383269 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6215560862383269 / 10000000000000000 : ℝ) /
                (1 + (11774259927230697 / 10000000000000000 : ℝ)) =
              (6215560862383269 / 21774259927230697 : ℝ)
            by
        norm_num];
        exact hau554)
  have hat1 :
    (Real.pi / 2 - (2 * (86893587344624066073 / 312500000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6215560862383269 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6215560862383269 : ℝ) =
              (6215560862383269 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau553)
  have hat2 :
    Real.arctan (125000000000000 / 1035926810397211 : ℝ) ≤
      (1200843309874540748747 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (125000000000000 / 1035926810397211 : ℚ))
        (U := (1200843309874540748747 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (12362622986877 / 32000000000000 : ℚ))
      (lo := (3107780431191633 / 5000000000000000 : ℚ))
      (hi := (6215560862383269 / 10000000000000000 : ℚ))
      (s := (3107780431191633 / 5000000000000000 : ℚ))
      (r₁ := (44362622986877 / 32000000000000 : ℚ))
      (r₂ := (12542622986877 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6215560862383269 : ℚ))
      (z₂ := (125000000000000 / 1035926810397211 : ℚ))
      (L := (816653468713089555349 / 2500000000000000000000 : ℚ))
      (U := (-(2341508048351393276649 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_392 :
    ((3276044976259764027657 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9332714694551548750447 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6226074596507039 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (21753007288003625813 / 78125000000000000000 : ℝ))) -
              6 * (299708720331099562257 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (24808963124013 / 64000000000000 : ℝ) := by
  have hL1 :
    (3276044976259764027657 / 10000000000000000000000 : ℝ) ≤
      Real.log (88808963124013 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (88808963124013 / 64000000000000 : ℚ))
        (L := (3276044976259764027657 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (25168963124013 / 64000000000000 : ℝ) ≤
      (-(9332714694551548750447 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (25168963124013 / 64000000000000 : ℝ) = (25168963124013 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (25168963124013 / 16000000000000 : ℚ))
             (U := (4530228911448451249553 / 10000000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (25168963124013 / 16000000000000 : ℝ) ≤
            (4530228911448451249553 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau556 :
    Real.arctan (3113037298253521 / 10889906724245943 : ℝ) ≤
      (21753007288003625813 / 78125000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3113037298253521 / 10889906724245943 : ℚ))
        (U := (21753007288003625813 / 78125000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau555 :
    Real.arctan (3113037298253521 / 5000000000000000 : ℝ) ≤
      (2 * (21753007288003625813 / 78125000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5889906724245943 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3113037298253521 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3113037298253521 / 5000000000000000 : ℝ) /
                (1 + (5889906724245943 / 5000000000000000 : ℝ)) =
              (3113037298253521 / 10889906724245943 : ℝ)
            by
        norm_num];
        exact hau556)
  have hat1 :
    (Real.pi / 2 - (2 * (21753007288003625813 / 78125000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3113037298253521 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3113037298253521 : ℝ) =
              (3113037298253521 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau555)
  have hat2 :
    Real.arctan (750000000000000 / 6226074596507039 : ℝ) ≤
      (299708720331099562257 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 6226074596507039 : ℚ))
        (U := (299708720331099562257 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (24808963124013 / 64000000000000 : ℚ))
      (lo := (6226074596507039 / 10000000000000000 : ℚ))
      (hi := (3113037298253521 / 5000000000000000 : ℚ))
      (s := (6226074596507039 / 10000000000000000 : ℚ))
      (r₁ := (88808963124013 / 64000000000000 : ℚ))
      (r₂ := (25168963124013 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3113037298253521 : ℚ))
      (z₂ := (750000000000000 / 6226074596507039 : ℚ))
      (L := (3276044976259764027657 / 10000000000000000000000 : ℚ))
      (U := (-(9332714694551548750447 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_393 :
    ((657093438295957909727 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2324876958189376444893 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6236570606394991 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2788165116089121008927 / 10000000000000000000000 : ℝ))) -
              6 * (1196836496748037631457 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (777896258571 / 2000000000000 : ℝ) := by
  have hL1 :
    (657093438295957909727 / 2000000000000000000000 : ℝ) ≤
      Real.log (2777896258571 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2777896258571 / 2000000000000 : ℚ))
        (L := (657093438295957909727 / 2000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (789146258571 / 2000000000000 : ℝ) ≤
      (-(2324876958189376444893 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (789146258571 / 2000000000000 : ℝ) = (789146258571 / 500000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (789146258571 / 500000000000 : ℚ))
             (U := (1140858943310623555107 / 2500000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (789146258571 / 500000000000 : ℝ) ≤
            (1140858943310623555107 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau558 :
    Real.arctan (6236570606394994 / 21785364352812771 : ℝ) ≤
      (2788165116089121008927 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6236570606394994 / 21785364352812771 : ℚ))
        (U := (2788165116089121008927 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau557 :
    Real.arctan (3118285303197497 / 5000000000000000 : ℝ) ≤
      (2 * (2788165116089121008927 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11785364352812771 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3118285303197497 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3118285303197497 / 5000000000000000 : ℝ) /
                (1 + (11785364352812771 / 10000000000000000 : ℝ)) =
              (6236570606394994 / 21785364352812771 : ℝ)
            by
        norm_num];
        exact hau558)
  have hat1 :
    (Real.pi / 2 - (2 * (2788165116089121008927 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3118285303197497 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3118285303197497 : ℝ) =
              (3118285303197497 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau557)
  have hat2 :
    Real.arctan (750000000000000 / 6236570606394991 : ℝ) ≤
      (1196836496748037631457 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 6236570606394991 : ℚ))
        (U := (1196836496748037631457 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (777896258571 / 2000000000000 : ℚ))
      (lo := (6236570606394991 / 10000000000000000 : ℚ))
      (hi := (3118285303197497 / 5000000000000000 : ℚ))
      (s := (6236570606394991 / 10000000000000000 : ℚ))
      (r₁ := (2777896258571 / 2000000000000 : ℚ))
      (r₂ := (789146258571 / 2000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3118285303197497 : ℚ))
      (z₂ := (750000000000000 / 6236570606394991 : ℚ))
      (L := (657093438295957909727 / 2000000000000000000000 : ℚ))
      (U := (-(2324876958189376444893 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_394 :
    ((1647440268621094061217 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9266410875672095229157 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((195220280668297 / 312500000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2791935395588520664673 / 10000000000000000000000 : ℝ))) -
              6 * (1194848072707023067937 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (24976397424531 / 64000000000000 : ℝ) := by
  have hL1 :
    (1647440268621094061217 / 5000000000000000000000 : ℝ) ≤
      Real.log (88976397424531 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (88976397424531 / 64000000000000 : ℚ))
        (L := (1647440268621094061217 / 5000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (25336397424531 / 64000000000000 : ℝ) ≤
      (-(9266410875672095229157 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (25336397424531 / 64000000000000 : ℝ) = (25336397424531 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (25336397424531 / 16000000000000 : ℚ))
             (U := (4596532730327904770843 / 10000000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (25336397424531 / 16000000000000 : ℝ) ≤
            (4596532730327904770843 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau560 :
    Real.arctan (6247048981385507 / 21790912643889347 : ℝ) ≤
      (2791935395588520664673 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6247048981385507 / 21790912643889347 : ℚ))
        (U := (2791935395588520664673 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau559 :
    Real.arctan (6247048981385507 / 10000000000000000 : ℝ) ≤
      (2 * (2791935395588520664673 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11790912643889347 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6247048981385507 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6247048981385507 / 10000000000000000 : ℝ) /
                (1 + (11790912643889347 / 10000000000000000 : ℝ)) =
              (6247048981385507 / 21790912643889347 : ℝ)
            by
        norm_num];
        exact hau560)
  have hat1 :
    (Real.pi / 2 - (2 * (2791935395588520664673 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6247048981385507 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6247048981385507 : ℝ) =
              (6247048981385507 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau559)
  have hat2 :
    Real.arctan (23437500000000 / 195220280668297 : ℝ) ≤
      (1194848072707023067937 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (23437500000000 / 195220280668297 : ℚ))
        (U := (1194848072707023067937 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (24976397424531 / 64000000000000 : ℚ))
      (lo := (195220280668297 / 312500000000000 : ℚ))
      (hi := (6247048981385507 / 10000000000000000 : ℚ))
      (s := (195220280668297 / 312500000000000 : ℚ))
      (r₁ := (88976397424531 / 64000000000000 : ℚ))
      (r₂ := (25336397424531 / 64000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6247048981385507 : ℚ))
      (z₂ := (23437500000000 / 195220280668297 : ℚ))
      (L := (1647440268621094061217 / 5000000000000000000000 : ℚ))
      (U := (-(9266410875672095229157 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_395 :
    ((660857006045902524463 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(923342309819158098361 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6257509810068967 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (139784791091839437819 / 500000000000000000000 : ℝ))) -
              6 * (596434763365065326249 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (2506011457479 / 6400000000000 : ℝ) := by
  have hL1 :
    (660857006045902524463 / 2000000000000000000000 : ℝ) ≤
      Real.log (8906011457479 / 6400000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (8906011457479 / 6400000000000 : ℚ))
        (L := (660857006045902524463 / 2000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (2542011457479 / 6400000000000 : ℝ) ≤
      (-(923342309819158098361 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show (2542011457479 / 6400000000000 : ℝ) = (2542011457479 / 1600000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (2542011457479 / 1600000000000 : ℚ))
             (U := (462952050780841901639 / 1000000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (2542011457479 / 1600000000000 : ℝ) ≤
            (462952050780841901639 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau562 :
    Real.arctan (6257509810068970 / 21796458325408917 : ℝ) ≤
      (139784791091839437819 / 500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6257509810068970 / 21796458325408917 : ℚ))
        (U := (139784791091839437819 / 500000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau561 :
    Real.arctan (625750981006897 / 1000000000000000 : ℝ) ≤
      (2 * (139784791091839437819 / 500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11796458325408917 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (625750981006897 / 1000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (625750981006897 / 1000000000000000 : ℝ) /
                (1 + (11796458325408917 / 10000000000000000 : ℝ)) =
              (6257509810068970 / 21796458325408917 : ℝ)
            by
        norm_num];
        exact hau562)
  have hat1 :
    (Real.pi / 2 - (2 * (139784791091839437819 / 500000000000000000000 : ℝ))) ≤
      Real.arctan (1000000000000000 / 625750981006897 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 625750981006897 : ℝ) =
              (625750981006897 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau561)
  have hat2 :
    Real.arctan (750000000000000 / 6257509810068967 : ℝ) ≤
      (596434763365065326249 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 6257509810068967 : ℚ))
        (U := (596434763365065326249 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2506011457479 / 6400000000000 : ℚ))
      (lo := (6257509810068967 / 10000000000000000 : ℚ))
      (hi := (625750981006897 / 1000000000000000 : ℚ))
      (s := (6257509810068967 / 10000000000000000 : ℚ))
      (r₁ := (8906011457479 / 6400000000000 : ℚ))
      (r₂ := (2542011457479 / 6400000000000 : ℚ))
      (z₁ := (1000000000000000 / 625750981006897 : ℚ))
      (z₂ := (750000000000000 / 6257509810068967 : ℚ))
      (L := (660857006045902524463 / 2000000000000000000000 : ℚ))
      (U := (-(923342309819158098361 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_396 :
    ((828420171769323212123 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4600271891182260404739 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6267953180296503 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (349930805612534943393 / 1250000000000000000000 : ℝ))) -
              6 * (1190900777298982651693 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (25143831725049 / 64000000000000 : ℝ) := by
  have hL1 :
    (828420171769323212123 / 2500000000000000000000 : ℝ) ≤
      Real.log (89143831725049 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (89143831725049 / 64000000000000 : ℚ))
        (L := (828420171769323212123 / 2500000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (25503831725049 / 64000000000000 : ℝ) ≤
      (-(4600271891182260404739 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (25503831725049 / 64000000000000 : ℝ) = (25503831725049 / 16000000000000 : ℝ) / 2 ^ 2 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (25503831725049 / 16000000000000 : ℚ))
             (U := (2331199911817739595261 / 5000000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (25503831725049 / 16000000000000 : ℝ) ≤
            (2331199911817739595261 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau564 :
    Real.arctan (3133976590148253 / 10901000700525061 : ℝ) ≤
      (349930805612534943393 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3133976590148253 / 10901000700525061 : ℚ))
        (U := (349930805612534943393 / 1250000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau563 :
    Real.arctan (3133976590148253 / 5000000000000000 : ℝ) ≤
      (2 * (349930805612534943393 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5901000700525061 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3133976590148253 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3133976590148253 / 5000000000000000 : ℝ) /
                (1 + (5901000700525061 / 5000000000000000 : ℝ)) =
              (3133976590148253 / 10901000700525061 : ℝ)
            by
        norm_num];
        exact hau564)
  have hat1 :
    (Real.pi / 2 - (2 * (349930805612534943393 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3133976590148253 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3133976590148253 : ℝ) =
              (3133976590148253 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau563)
  have hat2 :
    Real.arctan (250000000000000 / 2089317726765501 : ℝ) ≤
      (1190900777298982651693 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2089317726765501 : ℚ))
        (U := (1190900777298982651693 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (25143831725049 / 64000000000000 : ℚ))
      (lo := (6267953180296503 / 10000000000000000 : ℚ))
      (hi := (3133976590148253 / 5000000000000000 : ℚ))
      (s := (6267953180296503 / 10000000000000000 : ℚ))
      (r₁ := (89143831725049 / 64000000000000 : ℚ))
      (r₂ := (25503831725049 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3133976590148253 : ℚ))
      (z₂ := (250000000000000 / 2089317726765501 : ℚ))
      (L := (828420171769323212123 / 2500000000000000000000 : ℚ))
      (U := (-(4600271891182260404739 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
