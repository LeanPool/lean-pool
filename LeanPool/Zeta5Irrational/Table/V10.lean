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

/-! # V10: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

lemma V_121 :
    ((358153637420051856447 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(505436999038738140509 / 200000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((681260672591859 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2660444724297807303401 / 10000000000000000000000 : ℝ)) -
              6 * (2685754224056738553489 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (297034306573 / 4000000000000 : ℝ) := by
  have hL1 :
    (358153637420051856447 / 5000000000000000000000 : ℝ) ≤
      Real.log (4297034306573 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (4297034306573 / 4000000000000 : ℚ))
        (L := (358153637420051856447 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (319534306573 / 4000000000000 : ℝ) ≤
      (-(505436999038738140509 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (319534306573 / 4000000000000 : ℝ) = (319534306573 / 250000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (319534306573 / 250000000000 : ℚ))
             (U := (49080745201261859491 / 200000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (319534306573 / 250000000000 : ℝ) ≤
            (49080745201261859491 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau183 :
    Real.arctan (2725042690367439 / 10000000000000000 : ℝ) ≤
      (2660444724297807303401 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2725042690367439 / 10000000000000000 : ℚ))
        (U := (2660444724297807303401 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2660444724297807303401 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2725042690367439 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2725042690367439 : ℝ) =
              (2725042690367439 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau183)
  have hat2 :
    Real.arctan (62500000000000 / 227086890863953 : ℝ) ≤
      (2685754224056738553489 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (62500000000000 / 227086890863953 : ℚ))
        (U := (2685754224056738553489 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (297034306573 / 4000000000000 : ℚ))
      (lo := (681260672591859 / 2500000000000000 : ℚ))
      (hi := (2725042690367439 / 10000000000000000 : ℚ))
      (s := (681260672591859 / 2500000000000000 : ℚ))
      (r₁ := (4297034306573 / 4000000000000 : ℚ))
      (r₂ := (319534306573 / 4000000000000 : ℚ))
      (z₁ := (10000000000000000 / 2725042690367439 : ℚ))
      (z₂ := (62500000000000 / 227086890863953 : ℚ))
      (L := (358153637420051856447 / 5000000000000000000000 : ℚ))
      (U := (-(505436999038738140509 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_122 :
    ((143750539911760461247 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25239014309567609724181 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2729859165131193 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1332463855095506303277 / 5000000000000000000000 : ℝ)) -
              6 * (2681239616034587774699 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (9538727758657 / 128000000000000 : ℝ) := by
  have hL1 :
    (143750539911760461247 / 2000000000000000000000 : ℝ) ≤
      Real.log (137538727758657 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (137538727758657 / 128000000000000 : ℚ))
        (L := (143750539911760461247 / 2000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (10258727758657 / 128000000000000 : ℝ) ≤
      (-(25239014309567609724181 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (10258727758657 / 128000000000000 : ℝ) = (10258727758657 / 8000000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (10258727758657 / 8000000000000 : ℚ))
             (U := (2486872902432390275819 / 10000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (10258727758657 / 8000000000000 : ℝ) ≤
            (2486872902432390275819 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau184 :
    Real.arctan (682464791282799 / 2500000000000000 : ℝ) ≤
      (1332463855095506303277 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (682464791282799 / 2500000000000000 : ℚ))
        (U := (1332463855095506303277 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1332463855095506303277 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 682464791282799 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 682464791282799 : ℝ) =
              (682464791282799 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau184)
  have hat2 :
    Real.arctan (250000000000000 / 909953055043731 : ℝ) ≤
      (2681239616034587774699 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 909953055043731 : ℚ))
        (U := (2681239616034587774699 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (9538727758657 / 128000000000000 : ℚ))
      (lo := (2729859165131193 / 10000000000000000 : ℚ))
      (hi := (682464791282799 / 2500000000000000 : ℚ))
      (s := (2729859165131193 / 10000000000000000 : ℚ))
      (r₁ := (137538727758657 / 128000000000000 : ℚ))
      (r₂ := (10258727758657 / 128000000000000 : ℚ))
      (z₁ := (2500000000000000 / 682464791282799 : ℚ))
      (z₂ := (250000000000000 / 909953055043731 : ℚ))
      (L := (143750539911760461247 / 2000000000000000000000 : ℚ))
      (U := (-(25239014309567609724181 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_123 :
    ((180299381603373895023 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25206286132366748618349 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((546933431363509 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2669401706285649911771 / 10000000000000000000000 : ℝ)) -
              6 * (2676747708916748668133 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4786178853489 / 64000000000000 : ℝ) := by
  have hL1 :
    (180299381603373895023 / 2500000000000000000000 : ℝ) ≤
      Real.log (68786178853489 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (68786178853489 / 64000000000000 : ℚ))
        (L := (180299381603373895023 / 2500000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (5146178853489 / 64000000000000 : ℝ) ≤
      (-(25206286132366748618349 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (5146178853489 / 64000000000000 : ℝ) = (5146178853489 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (5146178853489 / 4000000000000 : ℚ))
             (U := (2519601079633251381651 / 10000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (5146178853489 / 4000000000000 : ℝ) ≤
            (2519601079633251381651 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau185 :
    Real.arctan (683666789204387 / 2500000000000000 : ℝ) ≤
      (2669401706285649911771 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (683666789204387 / 2500000000000000 : ℚ))
        (U := (2669401706285649911771 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2669401706285649911771 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 683666789204387 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 683666789204387 : ℝ) =
              (683666789204387 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau185)
  have hat2 :
    Real.arctan (150000000000000 / 546933431363509 : ℝ) ≤
      (2676747708916748668133 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 546933431363509 : ℚ))
        (U := (2676747708916748668133 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4786178853489 / 64000000000000 : ℚ))
      (lo := (546933431363509 / 2000000000000000 : ℚ))
      (hi := (683666789204387 / 2500000000000000 : ℚ))
      (s := (546933431363509 / 2000000000000000 : ℚ))
      (r₁ := (68786178853489 / 64000000000000 : ℚ))
      (r₂ := (5146178853489 / 64000000000000 : ℚ))
      (z₁ := (2500000000000000 / 683666789204387 : ℚ))
      (z₂ := (150000000000000 / 546933431363509 : ℚ))
      (L := (180299381603373895023 / 2500000000000000000000 : ℚ))
      (U := (-(25206286132366748618349 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_124 :
    ((180910438924111719793 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6293416179799985485973 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2739466710092009 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2673866758528940898129 / 10000000000000000000000 : ℝ)) -
              6 * (1336139156501337456721 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (9605987655299 / 128000000000000 : ℝ) := by
  have hL1 :
    (180910438924111719793 / 2500000000000000000000 : ℝ) ≤
      Real.log (137605987655299 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (137605987655299 / 128000000000000 : ℚ))
        (L := (180910438924111719793 / 2500000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (10325987655299 / 128000000000000 : ℝ) ≤
      (-(6293416179799985485973 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (10325987655299 / 128000000000000 : ℝ) = (10325987655299 / 8000000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (10325987655299 / 8000000000000 : ℚ))
             (U := (638055623200014514027 / 2500000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (10325987655299 / 8000000000000 : ℝ) ≤
            (638055623200014514027 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau186 :
    Real.arctan (684866677523003 / 2500000000000000 : ℝ) ≤
      (2673866758528940898129 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (684866677523003 / 2500000000000000 : ℚ))
        (U := (2673866758528940898129 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2673866758528940898129 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 684866677523003 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 684866677523003 : ℝ) =
              (684866677523003 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau186)
  have hat2 :
    Real.arctan (750000000000000 / 2739466710092009 : ℝ) ≤
      (1336139156501337456721 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 2739466710092009 : ℚ))
        (U := (1336139156501337456721 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (9605987655299 / 128000000000000 : ℚ))
      (lo := (2739466710092009 / 10000000000000000 : ℚ))
      (hi := (684866677523003 / 2500000000000000 : ℚ))
      (s := (2739466710092009 / 10000000000000000 : ℚ))
      (r₁ := (137605987655299 / 128000000000000 : ℚ))
      (r₂ := (10325987655299 / 128000000000000 : ℚ))
      (z₁ := (2500000000000000 / 684866677523003 : ℚ))
      (z₂ := (750000000000000 / 2739466710092009 : ℚ))
      (L := (180910438924111719793 / 2500000000000000000000 : ℚ))
      (U := (-(6293416179799985485973 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_125 :
    ((726085387699705292959 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6285287343943028423973 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((548851573845903 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2678322912471147172359 / 10000000000000000000000 : ℝ)) -
              6 * (1333915620402408418013 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (481980880181 / 6400000000000 : ℝ) := by
  have hL1 :
    (726085387699705292959 / 10000000000000000000000 : ℝ) ≤
      Real.log (6881980880181 / 6400000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (6881980880181 / 6400000000000 : ℚ))
        (L := (726085387699705292959 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (517980880181 / 6400000000000 : ℝ) ≤
      (-(6285287343943028423973 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (517980880181 / 6400000000000 : ℝ) = (517980880181 / 400000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (517980880181 / 400000000000 : ℚ))
             (U := (646184459056971576027 / 2500000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (517980880181 / 400000000000 : ℝ) ≤
            (646184459056971576027 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau187 :
    Real.arctan (1372128934614759 / 5000000000000000 : ℝ) ≤
      (2678322912471147172359 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1372128934614759 / 5000000000000000 : ℚ))
        (U := (2678322912471147172359 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2678322912471147172359 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1372128934614759 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1372128934614759 : ℝ) =
              (1372128934614759 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau187)
  have hat2 :
    Real.arctan (50000000000000 / 182950524615301 : ℝ) ≤
      (1333915620402408418013 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (50000000000000 / 182950524615301 : ℚ))
        (U := (1333915620402408418013 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (481980880181 / 6400000000000 : ℚ))
      (lo := (548851573845903 / 2000000000000000 : ℚ))
      (hi := (1372128934614759 / 5000000000000000 : ℚ))
      (s := (548851573845903 / 2000000000000000 : ℚ))
      (r₁ := (6881980880181 / 6400000000000 : ℚ))
      (r₂ := (517980880181 / 6400000000000 : ℚ))
      (z₁ := (5000000000000000 / 1372128934614759 : ℚ))
      (z₂ := (50000000000000 / 182950524615301 : ℚ))
      (L := (726085387699705292959 / 10000000000000000000000 : ℚ))
      (U := (-(6285287343943028423973 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_126 :
    ((72852842271510586509 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12554369707269414330891 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2749040678119169 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2682770213270387066649 / 10000000000000000000000 : ℝ)) -
              6 * (1331703153507762705967 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (9673247551941 / 128000000000000 : ℝ) := by
  have hL1 :
    (72852842271510586509 / 1000000000000000000000 : ℝ) ≤
      Real.log (137673247551941 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (137673247551941 / 128000000000000 : ℚ))
        (L := (72852842271510586509 / 1000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (10393247551941 / 128000000000000 : ℝ) ≤
      (-(12554369707269414330891 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (10393247551941 / 128000000000000 : ℝ) = (10393247551941 / 8000000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (10393247551941 / 8000000000000 : ℚ))
             (U := (1308573898730585669109 / 5000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (10393247551941 / 8000000000000 : ℝ) ≤
            (1308573898730585669109 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau188 :
    Real.arctan (687260169529793 / 2500000000000000 : ℝ) ≤
      (2682770213270387066649 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (687260169529793 / 2500000000000000 : ℚ))
        (U := (2682770213270387066649 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2682770213270387066649 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 687260169529793 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 687260169529793 : ℝ) =
              (687260169529793 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau188)
  have hat2 :
    Real.arctan (750000000000000 / 2749040678119169 : ℝ) ≤
      (1331703153507762705967 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 2749040678119169 : ℚ))
        (U := (1331703153507762705967 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (9673247551941 / 128000000000000 : ℚ))
      (lo := (2749040678119169 / 10000000000000000 : ℚ))
      (hi := (687260169529793 / 2500000000000000 : ℚ))
      (s := (2749040678119169 / 10000000000000000 : ℚ))
      (r₁ := (137673247551941 / 128000000000000 : ℚ))
      (r₂ := (10393247551941 / 128000000000000 : ℚ))
      (z₁ := (2500000000000000 / 687260169529793 : ℚ))
      (z₂ := (750000000000000 / 2749040678119169 : ℚ))
      (L := (72852842271510586509 / 1000000000000000000000 : ℚ))
      (U := (-(12554369707269414330891 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_127 :
    ((730970861034269802467 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25076434154619059633243 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((172113448766809 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (335901088212172452663 / 1250000000000000000000 : ℝ)) -
              6 * (10636013313898229031 / 40000000000000000000 : ℝ)))) ≤
      Vfield (4853438750131 / 64000000000000 : ℝ) := by
  have hL1 :
    (730970861034269802467 / 10000000000000000000000 : ℝ) ≤
      Real.log (68853438750131 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (68853438750131 / 64000000000000 : ℚ))
        (L := (730970861034269802467 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (5213438750131 / 64000000000000 : ℝ) ≤
      (-(25076434154619059633243 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (5213438750131 / 64000000000000 : ℝ) = (5213438750131 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (5213438750131 / 4000000000000 : ℚ))
             (U := (2649453057380940366757 / 10000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (5213438750131 / 4000000000000 : ℝ) ≤
            (2649453057380940366757 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau189 :
    Real.arctan (2753815180268947 / 10000000000000000 : ℝ) ≤
      (335901088212172452663 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2753815180268947 / 10000000000000000 : ℚ))
        (U := (335901088212172452663 / 1250000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (335901088212172452663 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2753815180268947 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2753815180268947 : ℝ) =
              (2753815180268947 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau189)
  have hat2 :
    Real.arctan (46875000000000 / 172113448766809 : ℝ) ≤
      (10636013313898229031 / 40000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (46875000000000 / 172113448766809 : ℚ))
        (U := (10636013313898229031 / 40000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4853438750131 / 64000000000000 : ℚ))
      (lo := (172113448766809 / 625000000000000 : ℚ))
      (hi := (2753815180268947 / 10000000000000000 : ℚ))
      (s := (172113448766809 / 625000000000000 : ℚ))
      (r₁ := (68853438750131 / 64000000000000 : ℚ))
      (r₂ := (5213438750131 / 64000000000000 : ℚ))
      (z₁ := (10000000000000000 / 2753815180268947 : ℚ))
      (z₂ := (46875000000000 / 172113448766809 : ℚ))
      (L := (730970861034269802467 / 10000000000000000000000 : ℚ))
      (U := (-(25076434154619059633243 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_128 :
    ((735853948749304669843 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5002427009599881711513 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2763339436502733 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (5265741098844656167 / 19531250000000000000 : ℝ)) -
              6 * (2650262515042783265311 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1221767174613 / 16000000000000 : ℝ) := by
  have hL1 :
    (735853948749304669843 / 10000000000000000000000 : ℝ) ≤
      Real.log (17221767174613 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (17221767174613 / 16000000000000 : ℚ))
        (L := (735853948749304669843 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (1311767174613 / 16000000000000 : ℝ) ≤
      (-(5002427009599881711513 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1311767174613 / 16000000000000 : ℝ) = (1311767174613 / 1000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (1311767174613 / 1000000000000 : ℚ))
             (U := (542750432800118288487 / 2000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (1311767174613 / 1000000000000 : ℝ) ≤
            (542750432800118288487 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau190 :
    Real.arctan (172708714781421 / 625000000000000 : ℝ) ≤
      (5265741098844656167 / 19531250000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (172708714781421 / 625000000000000 : ℚ))
        (U := (5265741098844656167 / 19531250000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (5265741098844656167 / 19531250000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 172708714781421 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 172708714781421 : ℝ) =
              (172708714781421 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau190)
  have hat2 :
    Real.arctan (250000000000000 / 921113145500911 : ℝ) ≤
      (2650262515042783265311 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 921113145500911 : ℚ))
        (U := (2650262515042783265311 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1221767174613 / 16000000000000 : ℚ))
      (lo := (2763339436502733 / 10000000000000000 : ℚ))
      (hi := (172708714781421 / 625000000000000 : ℚ))
      (s := (2763339436502733 / 10000000000000000 : ℚ))
      (r₁ := (17221767174613 / 16000000000000 : ℚ))
      (r₂ := (1311767174613 / 16000000000000 : ℚ))
      (z₁ := (625000000000000 / 172708714781421 : ℚ))
      (z₂ := (250000000000000 / 921113145500911 : ℚ))
      (L := (735853948749304669843 / 10000000000000000000000 : ℚ))
      (U := (-(5002427009599881711513 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_129 :
    ((740734653173510746083 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6237061684726463436083 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1386415489272859 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (676218868449462891921 / 2500000000000000000000 : ℝ)) -
              6 * (52832147539552359909 / 200000000000000000000 : ℝ)))) ≤
      Vfield (4920698646773 / 64000000000000 : ℝ) := by
  have hL1 :
    (740734653173510746083 / 10000000000000000000000 : ℝ) ≤
      Real.log (68920698646773 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (68920698646773 / 64000000000000 : ℚ))
        (L := (740734653173510746083 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (5280698646773 / 64000000000000 : ℝ) ≤
      (-(6237061684726463436083 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (5280698646773 / 64000000000000 : ℝ) = (5280698646773 / 4000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (5280698646773 / 4000000000000 : ℚ))
             (U := (694410118273536563917 / 2500000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (5280698646773 / 4000000000000 : ℝ) ≤
            (694410118273536563917 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau191 :
    Real.arctan (2772830978545721 / 10000000000000000 : ℝ) ≤
      (676218868449462891921 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2772830978545721 / 10000000000000000 : ℚ))
        (U := (676218868449462891921 / 2500000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (676218868449462891921 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2772830978545721 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2772830978545721 : ℝ) =
              (2772830978545721 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau191)
  have hat2 :
    Real.arctan (375000000000000 / 1386415489272859 : ℝ) ≤
      (52832147539552359909 / 200000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 1386415489272859 : ℚ))
        (U := (52832147539552359909 / 200000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4920698646773 / 64000000000000 : ℚ))
      (lo := (1386415489272859 / 5000000000000000 : ℚ))
      (hi := (2772830978545721 / 10000000000000000 : ℚ))
      (s := (1386415489272859 / 5000000000000000 : ℚ))
      (r₁ := (68920698646773 / 64000000000000 : ℚ))
      (r₂ := (5280698646773 / 64000000000000 : ℚ))
      (z₁ := (10000000000000000 / 2772830978545721 : ℚ))
      (z₂ := (375000000000000 / 1386415489272859 : ℚ))
      (L := (740734653173510746083 / 10000000000000000000000 : ℚ))
      (U := (-(6237061684726463436083 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_130 :
    ((37280648831609041759 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6221191002898389833279 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2782290141202813 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (542731428790419567221 / 2000000000000000000000 : ℝ)) -
              6 * (658259130780697986243 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (2477164297547 / 32000000000000 : ℝ) := by
  have hL1 :
    (37280648831609041759 / 500000000000000000000 : ℝ) ≤
      Real.log (34477164297547 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (34477164297547 / 32000000000000 : ℚ))
        (L := (37280648831609041759 / 500000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (2657164297547 / 32000000000000 : ℝ) ≤
      (-(6221191002898389833279 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (2657164297547 / 32000000000000 : ℝ) = (2657164297547 / 2000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (2657164297547 / 2000000000000 : ℚ))
             (U := (710280800101610166721 / 2500000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (2657164297547 / 2000000000000 : ℝ) ≤
            (710280800101610166721 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau192 :
    Real.arctan (21736641728147 / 78125000000000 : ℝ) ≤
      (542731428790419567221 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (21736641728147 / 78125000000000 : ℚ))
        (U := (542731428790419567221 / 2000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (542731428790419567221 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (78125000000000 / 21736641728147 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (78125000000000 / 21736641728147 : ℝ) =
              (21736641728147 / 78125000000000 : ℝ)
            by
        norm_num];
        exact hau192)
  have hat2 :
    Real.arctan (750000000000000 / 2782290141202813 : ℝ) ≤
      (658259130780697986243 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 2782290141202813 : ℚ))
        (U := (658259130780697986243 / 2500000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2477164297547 / 32000000000000 : ℚ))
      (lo := (2782290141202813 / 10000000000000000 : ℚ))
      (hi := (21736641728147 / 78125000000000 : ℚ))
      (s := (2782290141202813 / 10000000000000000 : ℚ))
      (r₁ := (34477164297547 / 32000000000000 : ℚ))
      (r₂ := (2657164297547 / 32000000000000 : ℚ))
      (z₁ := (78125000000000 / 21736641728147 : ℚ))
      (z₂ := (750000000000000 / 2782290141202813 : ℚ))
      (L := (37280648831609041759 / 500000000000000000000 : ℚ))
      (U := (-(6221191002898389833279 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_131 :
    ((750488921447206341103 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(24821681749024979579647 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1395858626803403 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2722404791990247254829 / 10000000000000000000000 : ℝ)) -
              6 * (2624548593756629872647 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (997591708683 / 12800000000000 : ℝ) := by
  have hL1 :
    (750488921447206341103 / 10000000000000000000000 : ℝ) ≤
      Real.log (13797591708683 / 12800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (13797591708683 / 12800000000000 : ℚ))
        (L := (750488921447206341103 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (1069591708683 / 12800000000000 : ℝ) ≤
      (-(24821681749024979579647 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (1069591708683 / 12800000000000 : ℝ) = (1069591708683 / 800000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (1069591708683 / 800000000000 : ℚ))
             (U := (2904205462975020420353 / 10000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (1069591708683 / 800000000000 : ℝ) ≤
            (2904205462975020420353 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau193 :
    Real.arctan (2791717253606809 / 10000000000000000 : ℝ) ≤
      (2722404791990247254829 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2791717253606809 / 10000000000000000 : ℚ))
        (U := (2722404791990247254829 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2722404791990247254829 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2791717253606809 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2791717253606809 : ℝ) =
              (2791717253606809 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau193)
  have hat2 :
    Real.arctan (375000000000000 / 1395858626803403 : ℝ) ≤
      (2624548593756629872647 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 1395858626803403 : ℚ))
        (U := (2624548593756629872647 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (997591708683 / 12800000000000 : ℚ))
      (lo := (1395858626803403 / 5000000000000000 : ℚ))
      (hi := (2791717253606809 / 10000000000000000 : ℚ))
      (s := (1395858626803403 / 5000000000000000 : ℚ))
      (r₁ := (13797591708683 / 12800000000000 : ℚ))
      (r₂ := (1069591708683 / 12800000000000 : ℚ))
      (z₁ := (10000000000000000 / 2791717253606809 : ℚ))
      (z₂ := (375000000000000 / 1395858626803403 : ℚ))
      (L := (750488921447206341103 / 10000000000000000000000 : ℚ))
      (U := (-(24821681749024979579647 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_132 :
    ((377681244968541949289 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(24758994930394767520483 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1400556319675997 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2731118751199019664549 / 10000000000000000000000 : ℝ)) -
              6 * (2616142259684255857913 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (627698561467 / 8000000000000 : ℝ) := by
  have hL1 :
    (377681244968541949289 / 5000000000000000000000 : ℝ) ≤
      Real.log (8627698561467 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (8627698561467 / 8000000000000 : ℚ))
        (L := (377681244968541949289 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hU2 :
    Real.log (672698561467 / 8000000000000 : ℝ) ≤
      (-(24758994930394767520483 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (672698561467 / 8000000000000 : ℝ) = (672698561467 / 500000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (672698561467 / 500000000000 : ℚ))
             (U := (2966892281605232479517 / 10000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (672698561467 / 500000000000 : ℝ) ≤
            (2966892281605232479517 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau194 :
    Real.arctan (2801112639351997 / 10000000000000000 : ℝ) ≤
      (2731118751199019664549 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2801112639351997 / 10000000000000000 : ℚ))
        (U := (2731118751199019664549 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2731118751199019664549 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2801112639351997 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2801112639351997 : ℝ) =
              (2801112639351997 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau194)
  have hat2 :
    Real.arctan (375000000000000 / 1400556319675997 : ℝ) ≤
      (2616142259684255857913 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 1400556319675997 : ℚ))
        (U := (2616142259684255857913 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (627698561467 / 8000000000000 : ℚ))
      (lo := (1400556319675997 / 5000000000000000 : ℚ))
      (hi := (2801112639351997 / 10000000000000000 : ℚ))
      (s := (1400556319675997 / 5000000000000000 : ℚ))
      (r₁ := (8627698561467 / 8000000000000 : ℚ))
      (r₂ := (672698561467 / 8000000000000 : ℚ))
      (z₁ := (10000000000000000 / 2801112639351997 : ℚ))
      (z₂ := (375000000000000 / 1400556319675997 : ℚ))
      (L := (377681244968541949289 / 5000000000000000000000 : ℚ))
      (U := (-(24758994930394767520483 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
