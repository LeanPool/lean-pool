/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
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

/-! # V41: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma V_493 :
    ((868295763499205084321 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5991612797366169144041 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1843310758656197 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (198543494771462783499 / 625000000000000000000 : ℝ))) -
              6 * (50685243988281521377 / 500000000000000000000 : ℝ)))) ≤
      Vfield (69586832444983 / 128000000000000 : ℝ) := by
  have hL1 :
    (868295763499205084321 / 2000000000000000000000 : ℝ) ≤
      Real.log (197586832444983 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (197586832444983 / 128000000000000 : ℚ))
        (L := (868295763499205084321 / 2000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (70306832444983 / 128000000000000 : ℝ) ≤
      (-(5991612797366169144041 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (70306832444983 / 128000000000000 : ℚ))
        (r' := (70306832444983 / 64000000000000 : ℚ))
        (U := (-(5991612797366169144041 / 10000000000000000000000 : ℚ)))
        (U' := (939859005633830855959 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by constructor <;> norm_num)
  have hau758 :
    Real.arctan (7373243034624791 / 22424359655436692 : ℝ) ≤
      (198543494771462783499 / 625000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7373243034624791 / 22424359655436692 : ℚ))
        (U := (198543494771462783499 / 625000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau757 :
    Real.arctan (7373243034624791 / 10000000000000000 : ℝ) ≤
      (2 * (198543494771462783499 / 625000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3106089913859173 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (7373243034624791 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7373243034624791 / 10000000000000000 : ℝ) /
                (1 + (3106089913859173 / 2500000000000000 : ℝ)) =
              (7373243034624791 / 22424359655436692 : ℝ)
            by
        norm_num];
        exact hau758)
  have hat1 :
    (Real.pi / 2 - (2 * (198543494771462783499 / 625000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7373243034624791 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7373243034624791 : ℝ) =
              (7373243034624791 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau757)
  have hat2 :
    Real.arctan (187500000000000 / 1843310758656197 : ℝ) ≤
      (50685243988281521377 / 500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 1843310758656197 : ℚ))
        (U := (50685243988281521377 / 500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (69586832444983 / 128000000000000 : ℚ))
      (lo := (1843310758656197 / 2500000000000000 : ℚ))
      (hi := (7373243034624791 / 10000000000000000 : ℚ))
      (s := (1843310758656197 / 2500000000000000 : ℚ))
      (r₁ := (197586832444983 / 128000000000000 : ℚ))
      (r₂ := (70306832444983 / 128000000000000 : ℚ))
      (z₁ := (10000000000000000 / 7373243034624791 : ℚ))
      (z₂ := (187500000000000 / 1843310758656197 : ℚ))
      (L := (868295763499205084321 / 2000000000000000000000 : ℚ))
      (U := (-(5991612797366169144041 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_494 :
    ((2172760564099170449509 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2990128321072975838143 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((295098965024909 / 400000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3178066124563289035779 / 10000000000000000000000 : ℝ))) -
              6 * (506563738093436821663 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (34833359663509 / 64000000000000 : ℝ) := by
  have hL1 :
    (2172760564099170449509 / 5000000000000000000000 : ℝ) ≤
      Real.log (98833359663509 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (98833359663509 / 64000000000000 : ℚ))
        (L := (2172760564099170449509 / 5000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (35193359663509 / 64000000000000 : ℝ) ≤
      (-(2990128321072975838143 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35193359663509 / 64000000000000 : ℚ))
        (r' := (35193359663509 / 32000000000000 : ℚ))
        (U := (-(2990128321072975838143 / 5000000000000000000000 : ℚ)))
        (U' := (475607580427024161857 / 5000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by constructor <;> norm_num)
  have hau760 :
    Real.arctan (7377474125622728 / 22426871065325849 : ℝ) ≤
      (3178066124563289035779 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7377474125622728 / 22426871065325849 : ℚ))
        (U := (3178066124563289035779 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau759 :
    Real.arctan (922184265702841 / 1250000000000000 : ℝ) ≤
      (2 * (3178066124563289035779 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12426871065325849 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (922184265702841 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (922184265702841 / 1250000000000000 : ℝ) /
                (1 + (12426871065325849 / 10000000000000000 : ℝ)) =
              (7377474125622728 / 22426871065325849 : ℝ)
            by
        norm_num];
        exact hau760)
  have hat1 :
    (Real.pi / 2 - (2 * (3178066124563289035779 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 922184265702841 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 922184265702841 : ℝ) =
              (922184265702841 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau759)
  have hat2 :
    Real.arctan (30000000000000 / 295098965024909 : ℝ) ≤
      (506563738093436821663 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (30000000000000 / 295098965024909 : ℚ))
        (U := (506563738093436821663 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (34833359663509 / 64000000000000 : ℚ))
      (lo := (295098965024909 / 400000000000000 : ℚ))
      (hi := (922184265702841 / 1250000000000000 : ℚ))
      (s := (295098965024909 / 400000000000000 : ℚ))
      (r₁ := (98833359663509 / 64000000000000 : ℚ))
      (r₂ := (35193359663509 / 64000000000000 : ℚ))
      (z₁ := (1250000000000000 / 922184265702841 : ℚ))
      (z₂ := (30000000000000 / 295098965024909 : ℚ))
      (L := (2172760564099170449509 / 5000000000000000000000 : ℚ))
      (U := (-(2990128321072975838143 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_495 :
    ((2174780902766655282939 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(298445668426235591233 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7381702791417617 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (397429374257384632401 / 1250000000000000000000 : ℝ))) -
              6 * (1012551058157293370951 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (69746606209053 / 128000000000000 : ℝ) := by
  have hL1 :
    (2174780902766655282939 / 5000000000000000000000 : ℝ) ≤
      Real.log (197746606209053 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (197746606209053 / 128000000000000 : ℚ))
        (L := (2174780902766655282939 / 5000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (70466606209053 / 128000000000000 : ℝ) ≤
      (-(298445668426235591233 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (70466606209053 / 128000000000000 : ℚ))
        (r' := (70466606209053 / 64000000000000 : ℚ))
        (U := (-(298445668426235591233 / 500000000000000000000 : ℚ)))
        (U' := (48127921723764408767 / 500000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by constructor <;> norm_num)
  have hau762 :
    Real.arctan (3690851395708810 / 11214690983886943 : ℝ) ≤
      (397429374257384632401 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3690851395708810 / 11214690983886943 : ℚ))
        (U := (397429374257384632401 / 1250000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau761 :
    Real.arctan (369085139570881 / 500000000000000 : ℝ) ≤
      (2 * (397429374257384632401 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6214690983886943 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (369085139570881 / 500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (369085139570881 / 500000000000000 : ℝ) /
                (1 + (6214690983886943 / 5000000000000000 : ℝ)) =
              (3690851395708810 / 11214690983886943 : ℝ)
            by
        norm_num];
        exact hau762)
  have hat1 :
    (Real.pi / 2 - (2 * (397429374257384632401 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (500000000000000 / 369085139570881 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 369085139570881 : ℝ) =
              (369085139570881 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau761)
  have hat2 :
    Real.arctan (750000000000000 / 7381702791417617 : ℝ) ≤
      (1012551058157293370951 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 7381702791417617 : ℚ))
        (U := (1012551058157293370951 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (69746606209053 / 128000000000000 : ℚ))
      (lo := (7381702791417617 / 10000000000000000 : ℚ))
      (hi := (369085139570881 / 500000000000000 : ℚ))
      (s := (7381702791417617 / 10000000000000000 : ℚ))
      (r₁ := (197746606209053 / 128000000000000 : ℚ))
      (r₂ := (70466606209053 / 128000000000000 : ℚ))
      (z₁ := (500000000000000 / 369085139570881 : ℚ))
      (z₂ := (750000000000000 / 7381702791417617 : ℚ))
      (L := (2174780902766655282939 / 5000000000000000000000 : ℚ))
      (U := (-(298445668426235591233 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_496 :
    ((4353600850820383394063 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5957582947311654869927 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7385929036174967 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (159040126363004019747 / 500000000000000000000 : ℝ))) -
              6 * (25299390571909664953 / 250000000000000000000 : ℝ)))) ≤
      Vfield (4364155818193 / 8000000000000 : ℝ) := by
  have hL1 :
    (4353600850820383394063 / 10000000000000000000000 : ℝ) ≤
      Real.log (12364155818193 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (12364155818193 / 8000000000000 : ℚ))
        (L := (4353600850820383394063 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (4409155818193 / 8000000000000 : ℝ) ≤
      (-(5957582947311654869927 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4409155818193 / 8000000000000 : ℚ))
        (r' := (4409155818193 / 4000000000000 : ℚ))
        (U := (-(5957582947311654869927 / 10000000000000000000000 : ℚ)))
        (U' := (973888855688345130073 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by constructor <;> norm_num)
  have hau764 :
    Real.arctan (7385929036174970 / 22431892363088271 : ℝ) ≤
      (159040126363004019747 / 500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7385929036174970 / 22431892363088271 : ℚ))
        (U := (159040126363004019747 / 500000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau763 :
    Real.arctan (738592903617497 / 1000000000000000 : ℝ) ≤
      (2 * (159040126363004019747 / 500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12431892363088271 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (738592903617497 / 1000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (738592903617497 / 1000000000000000 : ℝ) /
                (1 + (12431892363088271 / 10000000000000000 : ℝ)) =
              (7385929036174970 / 22431892363088271 : ℝ)
            by
        norm_num];
        exact hau764)
  have hat1 :
    (Real.pi / 2 - (2 * (159040126363004019747 / 500000000000000000000 : ℝ))) ≤
      Real.arctan (1000000000000000 / 738592903617497 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 738592903617497 : ℝ) =
              (738592903617497 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau763)
  have hat2 :
    Real.arctan (750000000000000 / 7385929036174967 : ℝ) ≤
      (25299390571909664953 / 250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 7385929036174967 : ℚ))
        (U := (25299390571909664953 / 250000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4364155818193 / 8000000000000 : ℚ))
      (lo := (7385929036174967 / 10000000000000000 : ℚ))
      (hi := (738592903617497 / 1000000000000000 : ℚ))
      (s := (7385929036174967 / 10000000000000000 : ℚ))
      (r₁ := (12364155818193 / 8000000000000 : ℚ))
      (r₂ := (4409155818193 / 8000000000000 : ℚ))
      (z₁ := (1000000000000000 / 738592903617497 : ℚ))
      (z₂ := (750000000000000 / 7385929036174967 : ℚ))
      (L := (4353600850820383394063 / 10000000000000000000000 : ℚ))
      (U := (-(5957582947311654869927 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_497 :
    ((4357638265377410206641 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2973132674707548513867 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((739015286404837 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1591084363294408453171 / 5000000000000000000000 : ℝ))) -
              6 * (1011401167554778336271 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (69906379973123 / 128000000000000 : ℝ) := by
  have hL1 :
    (4357638265377410206641 / 10000000000000000000000 : ℝ) ≤
      Real.log (197906379973123 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (197906379973123 / 128000000000000 : ℚ))
        (L := (4357638265377410206641 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (70626379973123 / 128000000000000 : ℝ) ≤
      (-(2973132674707548513867 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (70626379973123 / 128000000000000 : ℚ))
        (r' := (70626379973123 / 64000000000000 : ℚ))
        (U := (-(2973132674707548513867 / 5000000000000000000000 : ℚ)))
        (U' := (492603226792451486133 / 5000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by constructor <;> norm_num)
  have hau766 :
    Real.arctan (7390152864048373 / 22434402251576162 : ℝ) ≤
      (1591084363294408453171 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7390152864048373 / 22434402251576162 : ℚ))
        (U := (1591084363294408453171 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau765 :
    Real.arctan (7390152864048373 / 10000000000000000 : ℝ) ≤
      (2 * (1591084363294408453171 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6217201125788081 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7390152864048373 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7390152864048373 / 10000000000000000 : ℝ) /
                (1 + (6217201125788081 / 5000000000000000 : ℝ)) =
              (7390152864048373 / 22434402251576162 : ℝ)
            by
        norm_num];
        exact hau766)
  have hat1 :
    (Real.pi / 2 - (2 * (1591084363294408453171 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7390152864048373 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7390152864048373 : ℝ) =
              (7390152864048373 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau765)
  have hat2 :
    Real.arctan (75000000000000 / 739015286404837 : ℝ) ≤
      (1011401167554778336271 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (75000000000000 / 739015286404837 : ℚ))
        (U := (1011401167554778336271 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (69906379973123 / 128000000000000 : ℚ))
      (lo := (739015286404837 / 1000000000000000 : ℚ))
      (hi := (7390152864048373 / 10000000000000000 : ℚ))
      (s := (739015286404837 / 1000000000000000 : ℚ))
      (r₁ := (197906379973123 / 128000000000000 : ℚ))
      (r₂ := (70626379973123 / 128000000000000 : ℚ))
      (z₁ := (10000000000000000 / 7390152864048373 : ℚ))
      (z₂ := (75000000000000 / 739015286404837 : ℚ))
      (L := (4357638265377410206641 / 10000000000000000000000 : ℚ))
      (U := (-(2973132674707548513867 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_498 :
    ((4361674050520646257781 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5934960545842017276557 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1478874855835911 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3183533594461034959257 / 10000000000000000000000 : ℝ))) -
              6 * (252706922353541398699 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (34993133427579 / 64000000000000 : ℝ) := by
  have hL1 :
    (4361674050520646257781 / 10000000000000000000000 : ℝ) ≤
      Real.log (98993133427579 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (98993133427579 / 64000000000000 : ℚ))
        (L := (4361674050520646257781 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (35353133427579 / 64000000000000 : ℝ) ≤
      (-(5934960545842017276557 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35353133427579 / 64000000000000 : ℚ))
        (r' := (35353133427579 / 32000000000000 : ℚ))
        (U := (-(5934960545842017276557 / 10000000000000000000000 : ℚ)))
        (U' := (996511257157982723443 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by constructor <;> norm_num)
  have hau768 :
    Real.arctan (7394374279179558 / 22436911633544405 : ℝ) ≤
      (3183533594461034959257 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7394374279179558 / 22436911633544405 : ℚ))
        (U := (3183533594461034959257 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau767 :
    Real.arctan (3697187139589779 / 5000000000000000 : ℝ) ≤
      (2 * (3183533594461034959257 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2487382326708881 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3697187139589779 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3697187139589779 / 5000000000000000 : ℝ) /
                (1 + (2487382326708881 / 2000000000000000 : ℝ)) =
              (7394374279179558 / 22436911633544405 : ℝ)
            by
        norm_num];
        exact hau768)
  have hat1 :
    (Real.pi / 2 - (2 * (3183533594461034959257 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3697187139589779 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3697187139589779 : ℝ) =
              (3697187139589779 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau767)
  have hat2 :
    Real.arctan (50000000000000 / 492958285278637 : ℝ) ≤
      (252706922353541398699 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (50000000000000 / 492958285278637 : ℚ))
        (U := (252706922353541398699 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (34993133427579 / 64000000000000 : ℚ))
      (lo := (1478874855835911 / 2000000000000000 : ℚ))
      (hi := (3697187139589779 / 5000000000000000 : ℚ))
      (s := (1478874855835911 / 2000000000000000 : ℚ))
      (r₁ := (98993133427579 / 64000000000000 : ℚ))
      (r₂ := (35353133427579 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3697187139589779 : ℚ))
      (z₂ := (50000000000000 / 492958285278637 : ℚ))
      (L := (4361674050520646257781 / 10000000000000000000000 : ℚ))
      (U := (-(5934960545842017276557 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_499 :
    ((2182854103782376903733 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5923668507697611716043 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3699296642849219 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (15924485666428705901 / 50000000000000000000 : ℝ))) -
              6 * (1010255185687260178931 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (70066153737193 / 128000000000000 : ℝ) := by
  have hL1 :
    (2182854103782376903733 / 5000000000000000000000 : ℝ) ≤
      Real.log (198066153737193 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (198066153737193 / 128000000000000 : ℚ))
        (L := (2182854103782376903733 / 5000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (70786153737193 / 128000000000000 : ℝ) ≤
      (-(5923668507697611716043 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (70786153737193 / 128000000000000 : ℚ))
        (r' := (70786153737193 / 64000000000000 : ℚ))
        (U := (-(5923668507697611716043 / 10000000000000000000000 : ℚ)))
        (U' := (1007803295302388283957 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by constructor <;> norm_num)
  have hau770 :
    Real.arctan (7398593285698441 / 22439420509299540 : ℝ) ≤
      (15924485666428705901 / 50000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7398593285698441 / 22439420509299540 : ℚ))
        (U := (15924485666428705901 / 50000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau769 :
    Real.arctan (7398593285698441 / 10000000000000000 : ℝ) ≤
      (2 * (15924485666428705901 / 50000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (621971025464977 / 500000000000000 : ℝ) ≤
          Real.sqrt (1 + (7398593285698441 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7398593285698441 / 10000000000000000 : ℝ) /
                (1 + (621971025464977 / 500000000000000 : ℝ)) =
              (7398593285698441 / 22439420509299540 : ℝ)
            by
        norm_num];
        exact hau770)
  have hat1 :
    (Real.pi / 2 - (2 * (15924485666428705901 / 50000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7398593285698441 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7398593285698441 : ℝ) =
              (7398593285698441 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau769)
  have hat2 :
    Real.arctan (375000000000000 / 3699296642849219 : ℝ) ≤
      (1010255185687260178931 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 3699296642849219 : ℚ))
        (U := (1010255185687260178931 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (70066153737193 / 128000000000000 : ℚ))
      (lo := (3699296642849219 / 5000000000000000 : ℚ))
      (hi := (7398593285698441 / 10000000000000000 : ℚ))
      (s := (3699296642849219 / 5000000000000000 : ℚ))
      (r₁ := (198066153737193 / 128000000000000 : ℚ))
      (r₂ := (70786153737193 / 128000000000000 : ℚ))
      (z₁ := (10000000000000000 / 7398593285698441 : ℚ))
      (z₂ := (375000000000000 / 3699296642849219 : ℚ))
      (L := (2182854103782376903733 / 5000000000000000000000 : ℚ))
      (U := (-(5923668507697611716043 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_500 :
    ((4369740737822804691011 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(739048650773106305367 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1480561977544633 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (159312967273261300701 / 500000000000000000000 : ℝ))) -
              6 * (1009683653617733165789 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (17536510154807 / 32000000000000 : ℝ) := by
  have hL1 :
    (4369740737822804691011 / 10000000000000000000000 : ℝ) ≤
      Real.log (49536510154807 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (49536510154807 / 32000000000000 : ℚ))
        (L := (4369740737822804691011 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (17716510154807 / 32000000000000 : ℝ) ≤
      (-(739048650773106305367 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17716510154807 / 32000000000000 : ℚ))
        (r' := (17716510154807 / 16000000000000 : ℚ))
        (U := (-(739048650773106305367 / 1250000000000000000000 : ℚ)))
        (U' := (127385324601893694633 / 1250000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau772 :
    Real.arctan (7402809887723168 / 22441928879147793 : ℝ) ≤
      (159312967273261300701 / 500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7402809887723168 / 22441928879147793 : ℚ))
        (U := (159312967273261300701 / 500000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau771 :
    Real.arctan (231337808991349 / 312500000000000 : ℝ) ≤
      (2 * (159312967273261300701 / 500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12441928879147793 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (231337808991349 / 312500000000000 : ℝ) ^ 2))
      (by
        rw [show
            (231337808991349 / 312500000000000 : ℝ) /
                (1 + (12441928879147793 / 10000000000000000 : ℝ)) =
              (7402809887723168 / 22441928879147793 : ℝ)
            by
        norm_num];
        exact hau772)
  have hat1 :
    (Real.pi / 2 - (2 * (159312967273261300701 / 500000000000000000000 : ℝ))) ≤
      Real.arctan (312500000000000 / 231337808991349 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (312500000000000 / 231337808991349 : ℝ) =
              (231337808991349 / 312500000000000 : ℝ)
            by
        norm_num];
        exact hau771)
  have hat2 :
    Real.arctan (150000000000000 / 1480561977544633 : ℝ) ≤
      (1009683653617733165789 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 1480561977544633 : ℚ))
        (U := (1009683653617733165789 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (17536510154807 / 32000000000000 : ℚ))
      (lo := (1480561977544633 / 2000000000000000 : ℚ))
      (hi := (231337808991349 / 312500000000000 : ℚ))
      (s := (1480561977544633 / 2000000000000000 : ℚ))
      (r₁ := (49536510154807 / 32000000000000 : ℚ))
      (r₂ := (17716510154807 / 32000000000000 : ℚ))
      (z₁ := (312500000000000 / 231337808991349 : ℚ))
      (z₂ := (150000000000000 / 1480561977544633 : ℚ))
      (L := (4369740737822804691011 / 10000000000000000000000 : ℚ))
      (U := (-(739048650773106305367 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_501 :
    ((4377800923225096597531 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5889868698352369758921 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7411235894704171 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1594489899732132286837 / 5000000000000000000000 : ℝ))) -
              6 * (1008543493479960270289 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (35152907191649 / 64000000000000 : ℝ) := by
  have hL1 :
    (4377800923225096597531 / 10000000000000000000000 : ℝ) ≤
      Real.log (99152907191649 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (99152907191649 / 64000000000000 : ℚ))
        (L := (4377800923225096597531 / 10000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (35512907191649 / 64000000000000 : ℝ) ≤
      (-(5889868698352369758921 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35512907191649 / 64000000000000 : ℚ))
        (r' := (35512907191649 / 32000000000000 : ℚ))
        (U := (-(5889868698352369758921 / 10000000000000000000000 : ℚ)))
        (U' := (1041603104647630241079 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau774 :
    Real.arctan (7411235894704174 / 22446944102347031 : ℝ) ≤
      (1594489899732132286837 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7411235894704174 / 22446944102347031 : ℚ))
        (U := (1594489899732132286837 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau773 :
    Real.arctan (3705617947352087 / 5000000000000000 : ℝ) ≤
      (2 * (1594489899732132286837 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12446944102347031 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3705617947352087 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3705617947352087 / 5000000000000000 : ℝ) /
                (1 + (12446944102347031 / 10000000000000000 : ℝ)) =
              (7411235894704174 / 22446944102347031 : ℝ)
            by
        norm_num];
        exact hau774)
  have hat1 :
    (Real.pi / 2 - (2 * (1594489899732132286837 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3705617947352087 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3705617947352087 : ℝ) =
              (3705617947352087 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau773)
  have hat2 :
    Real.arctan (750000000000000 / 7411235894704171 : ℝ) ≤
      (1008543493479960270289 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 7411235894704171 : ℚ))
        (U := (1008543493479960270289 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (35152907191649 / 64000000000000 : ℚ))
      (lo := (7411235894704171 / 10000000000000000 : ℚ))
      (hi := (3705617947352087 / 5000000000000000 : ℚ))
      (s := (7411235894704171 / 10000000000000000 : ℚ))
      (r₁ := (99152907191649 / 64000000000000 : ℚ))
      (r₂ := (35512907191649 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3705617947352087 : ℚ))
      (z₂ := (750000000000000 / 7411235894704171 : ℚ))
      (L := (4377800923225096597531 / 10000000000000000000000 : ℚ))
      (U := (-(5889868698352369758921 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_502 :
    ((4385854617200366767653 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5867398793907133653737 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7419652332834149 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3191694975543130921949 / 10000000000000000000000 : ℝ))) -
              6 * (503703593583643605337 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (8808198518421 / 16000000000000 : ℝ) := by
  have hL1 :
    (4385854617200366767653 / 10000000000000000000000 : ℝ) ≤
      Real.log (24808198518421 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (24808198518421 / 16000000000000 : ℚ))
        (L := (4385854617200366767653 / 10000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (8898198518421 / 16000000000000 : ℝ) ≤
      (-(5867398793907133653737 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8898198518421 / 16000000000000 : ℚ))
        (r' := (8898198518421 / 8000000000000 : ℚ))
        (U := (-(5867398793907133653737 / 10000000000000000000000 : ℚ)))
        (U' := (1064073009092866346263 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau776 :
    Real.arctan (3709826166417076 / 11225978652792893 : ℝ) ≤
      (3191694975543130921949 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3709826166417076 / 11225978652792893 : ℚ))
        (U := (3191694975543130921949 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau775 :
    Real.arctan (927456541604269 / 1250000000000000 : ℝ) ≤
      (2 * (3191694975543130921949 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6225978652792893 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (927456541604269 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (927456541604269 / 1250000000000000 : ℝ) /
                (1 + (6225978652792893 / 5000000000000000 : ℝ)) =
              (3709826166417076 / 11225978652792893 : ℝ)
            by
        norm_num];
        exact hau776)
  have hat1 :
    (Real.pi / 2 - (2 * (3191694975543130921949 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 927456541604269 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 927456541604269 : ℝ) =
              (927456541604269 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau775)
  have hat2 :
    Real.arctan (750000000000000 / 7419652332834149 : ℝ) ≤
      (503703593583643605337 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 7419652332834149 : ℚ))
        (U := (503703593583643605337 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (8808198518421 / 16000000000000 : ℚ))
      (lo := (7419652332834149 / 10000000000000000 : ℚ))
      (hi := (927456541604269 / 1250000000000000 : ℚ))
      (s := (7419652332834149 / 10000000000000000 : ℚ))
      (r₁ := (24808198518421 / 16000000000000 : ℚ))
      (r₂ := (8898198518421 / 16000000000000 : ℚ))
      (z₁ := (1250000000000000 / 927456541604269 : ℚ))
      (z₂ := (750000000000000 / 7419652332834149 : ℚ))
      (L := (4385854617200366767653 / 10000000000000000000000 : ℚ))
      (U := (-(5867398793907133653737 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_503 :
    ((2196950915098102340867 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(292248963297407018761 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7428059234639349 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3194404892680992092831 / 10000000000000000000000 : ℝ))) -
              6 * (251568678254492200593 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (35312680955719 / 64000000000000 : ℝ) := by
  have hL1 :
    (2196950915098102340867 / 5000000000000000000000 : ℝ) ≤
      Real.log (99312680955719 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (99312680955719 / 64000000000000 : ℚ))
        (L := (2196950915098102340867 / 5000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (35672680955719 / 64000000000000 : ℝ) ≤
      (-(292248963297407018761 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35672680955719 / 64000000000000 : ℚ))
        (r' := (35672680955719 / 32000000000000 : ℚ))
        (U := (-(292248963297407018761 / 500000000000000000000 : ℚ)))
        (U' := (54324626852592981239 / 500000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau778 :
    Real.arctan (1238009872439892 / 3742828081883801 : ℝ) ≤
      (3194404892680992092831 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1238009872439892 / 3742828081883801 : ℚ))
        (U := (3194404892680992092831 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau777 :
    Real.arctan (928507404329919 / 1250000000000000 : ℝ) ≤
      (2 * (3194404892680992092831 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6228484245651403 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (928507404329919 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (928507404329919 / 1250000000000000 : ℝ) /
                (1 + (6228484245651403 / 5000000000000000 : ℝ)) =
              (1238009872439892 / 3742828081883801 : ℝ)
            by
        norm_num];
        exact hau778)
  have hat1 :
    (Real.pi / 2 - (2 * (3194404892680992092831 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 928507404329919 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 928507404329919 : ℝ) =
              (928507404329919 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau777)
  have hat2 :
    Real.arctan (250000000000000 / 2476019744879783 : ℝ) ≤
      (251568678254492200593 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2476019744879783 : ℚ))
        (U := (251568678254492200593 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (35312680955719 / 64000000000000 : ℚ))
      (lo := (7428059234639349 / 10000000000000000 : ℚ))
      (hi := (928507404329919 / 1250000000000000 : ℚ))
      (s := (7428059234639349 / 10000000000000000 : ℚ))
      (r₁ := (99312680955719 / 64000000000000 : ℚ))
      (r₂ := (35672680955719 / 64000000000000 : ℚ))
      (z₁ := (1250000000000000 / 928507404329919 : ℚ))
      (z₂ := (250000000000000 / 2476019744879783 : ℚ))
      (L := (2196950915098102340867 / 5000000000000000000000 : ℚ))
      (U := (-(292248963297407018761 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_504 :
    ((4401942572634988737343 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2911304944548540144719 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((743645663246217 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3197109569752017389649 / 10000000000000000000000 : ℝ))) -
              6 * (1005146049540338767613 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (17696283918877 / 32000000000000 : ℝ) := by
  have hL1 :
    (4401942572634988737343 / 10000000000000000000000 : ℝ) ≤
      Real.log (49696283918877 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (49696283918877 / 32000000000000 : ℚ))
        (L := (4401942572634988737343 / 10000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (17876283918877 / 32000000000000 : ℝ) ≤
      (-(2911304944548540144719 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17876283918877 / 32000000000000 : ℚ))
        (r' := (17876283918877 / 16000000000000 : ℚ))
        (U := (-(2911304944548540144719 / 5000000000000000000000 : ℚ)))
        (U' := (554430956951459855281 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by constructor <;> norm_num)
  have hau780 :
    Real.arctan (2478818877487391 / 7487325887310646 : ℝ) ≤
      (3197109569752017389649 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2478818877487391 / 7487325887310646 : ℚ))
        (U := (3197109569752017389649 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau779 :
    Real.arctan (7436456632462173 / 10000000000000000 : ℝ) ≤
      (2 * (3197109569752017389649 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6230988830965969 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (7436456632462173 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (7436456632462173 / 10000000000000000 : ℝ) /
                (1 + (6230988830965969 / 5000000000000000 : ℝ)) =
              (2478818877487391 / 7487325887310646 : ℝ)
            by
        norm_num];
        exact hau780)
  have hat1 :
    (Real.pi / 2 - (2 * (3197109569752017389649 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 7436456632462173 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 7436456632462173 : ℝ) =
              (7436456632462173 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau779)
  have hat2 :
    Real.arctan (25000000000000 / 247881887748739 : ℝ) ≤
      (1005146049540338767613 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (25000000000000 / 247881887748739 : ℚ))
        (U := (1005146049540338767613 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (17696283918877 / 32000000000000 : ℚ))
      (lo := (743645663246217 / 1000000000000000 : ℚ))
      (hi := (7436456632462173 / 10000000000000000 : ℚ))
      (s := (743645663246217 / 1000000000000000 : ℚ))
      (r₁ := (49696283918877 / 32000000000000 : ℚ))
      (r₂ := (17876283918877 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 7436456632462173 : ℚ))
      (z₂ := (25000000000000 / 247881887748739 : ℚ))
      (L := (4401942572634988737343 / 10000000000000000000000 : ℚ))
      (U := (-(2911304944548540144719 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
