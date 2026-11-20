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

/-! # V35: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma V_421 :
    ((1860131738235363403791 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1569226225604356732877 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3356602458448497 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1478043914574713354633 / 5000000000000000000000 : ℝ))) -
              6 * (222517508356799869161 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (7210739241 / 16000000000 : ℝ) := by
  have hL1 :
    (1860131738235363403791 / 5000000000000000000000 : ℝ) ≤
      Real.log (23210739241 / 16000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (23210739241 / 16000000000 : ℚ))
        (L := (1860131738235363403791 / 5000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (7300739241 / 16000000000 : ℝ) ≤
      (-(1569226225604356732877 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7300739241 / 16000000000 : ℚ))
        (r' := (7300739241 / 4000000000 : ℚ))
        (U := (-(1569226225604356732877 / 2000000000000000000000 : ℚ)))
        (U' := (1203362495595643267123 / 2000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau614 :
    Real.arctan (6713204916896997 / 22044381273284651 : ℝ) ≤
      (1478043914574713354633 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6713204916896997 / 22044381273284651 : ℚ))
        (U := (1478043914574713354633 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau613 :
    Real.arctan (6713204916896997 / 10000000000000000 : ℝ) ≤
      (2 * (1478043914574713354633 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12044381273284651 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6713204916896997 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6713204916896997 / 10000000000000000 : ℝ) /
                (1 + (12044381273284651 / 10000000000000000 : ℝ)) =
              (6713204916896997 / 22044381273284651 : ℝ)
            by
        norm_num];
        exact hau614)
  have hat1 :
    (Real.pi / 2 - (2 * (1478043914574713354633 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6713204916896997 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6713204916896997 : ℝ) =
              (6713204916896997 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau613)
  have hat2 :
    Real.arctan (125000000000000 / 1118867486149499 : ℝ) ≤
      (222517508356799869161 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (125000000000000 / 1118867486149499 : ℚ))
        (U := (222517508356799869161 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (7210739241 / 16000000000 : ℚ))
      (lo := (3356602458448497 / 5000000000000000 : ℚ))
      (hi := (6713204916896997 / 10000000000000000 : ℚ))
      (s := (3356602458448497 / 5000000000000000 : ℚ))
      (r₁ := (23210739241 / 16000000000 : ℚ))
      (r₂ := (7300739241 / 16000000000 : ℚ))
      (z₁ := (10000000000000000 / 6713204916896997 : ℚ))
      (z₂ := (125000000000000 / 1118867486149499 : ℚ))
      (L := (1860131738235363403791 / 5000000000000000000000 : ℚ))
      (U := (-(1569226225604356732877 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_422 :
    ((116400839797190555333 / 312500000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1957907560260822272463 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1679533701099709 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2957786616188343050519 / 10000000000000000000000 : ℝ))) -
              6 * (555888909335956105031 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1805333410003 / 4000000000000 : ℝ) := by
  have hL1 :
    (116400839797190555333 / 312500000000000000000 : ℝ) ≤
      Real.log (5805333410003 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (5805333410003 / 4000000000000 : ℚ))
        (L := (116400839797190555333 / 312500000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (1827833410003 / 4000000000000 : ℝ) ≤
      (-(1957907560260822272463 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1827833410003 / 4000000000000 : ℚ))
        (r' := (1827833410003 / 1000000000000 : ℚ))
        (U := (-(1957907560260822272463 / 2500000000000000000000 : ℚ)))
        (U' := (1507828341239177727537 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau616 :
    Real.arctan (6718134804398839 / 22047129751524842 : ℝ) ≤
      (2957786616188343050519 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6718134804398839 / 22047129751524842 : ℚ))
        (U := (2957786616188343050519 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau615 :
    Real.arctan (6718134804398839 / 10000000000000000 : ℝ) ≤
      (2 * (2957786616188343050519 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6023564875762421 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6718134804398839 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6718134804398839 / 10000000000000000 : ℝ) /
                (1 + (6023564875762421 / 5000000000000000 : ℝ)) =
              (6718134804398839 / 22047129751524842 : ℝ)
            by
        norm_num];
        exact hau616)
  have hat1 :
    (Real.pi / 2 - (2 * (2957786616188343050519 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6718134804398839 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6718134804398839 : ℝ) =
              (6718134804398839 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau615)
  have hat2 :
    Real.arctan (187500000000000 / 1679533701099709 : ℝ) ≤
      (555888909335956105031 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 1679533701099709 : ℚ))
        (U := (555888909335956105031 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1805333410003 / 4000000000000 : ℚ))
      (lo := (1679533701099709 / 2500000000000000 : ℚ))
      (hi := (6718134804398839 / 10000000000000000 : ℚ))
      (s := (1679533701099709 / 2500000000000000 : ℚ))
      (r₁ := (5805333410003 / 4000000000000 : ℚ))
      (r₂ := (1827833410003 / 4000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6718134804398839 : ℚ))
      (z₂ := (187500000000000 / 1679533701099709 : ℚ))
      (L := (116400839797190555333 / 312500000000000000000 : ℚ))
      (U := (-(1957907560260822272463 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_423 :
    ((3729388189040054123869 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7817150351193086393177 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3361530538456403 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2959483383238434001347 / 10000000000000000000000 : ℝ))) -
              6 * (1110969860924394921403 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (451995502439 / 1000000000000 : ℝ) := by
  have hL1 :
    (3729388189040054123869 / 10000000000000000000000 : ℝ) ≤
      Real.log (1451995502439 / 1000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1451995502439 / 1000000000000 : ℚ))
        (L := (3729388189040054123869 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (457620502439 / 1000000000000 : ℝ) ≤
      (-(7817150351193086393177 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (457620502439 / 1000000000000 : ℚ))
        (r' := (457620502439 / 250000000000 : ℚ))
        (U := (-(7817150351193086393177 / 10000000000000000000000 : ℚ)))
        (U' := (6045793254806913606823 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau618 :
    Real.arctan (6723061076912809 / 22049877602859706 : ℝ) ≤
      (2959483383238434001347 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6723061076912809 / 22049877602859706 : ℚ))
        (U := (2959483383238434001347 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau617 :
    Real.arctan (6723061076912809 / 10000000000000000 : ℝ) ≤
      (2 * (2959483383238434001347 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6024938801429853 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6723061076912809 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6723061076912809 / 10000000000000000 : ℝ) /
                (1 + (6024938801429853 / 5000000000000000 : ℝ)) =
              (6723061076912809 / 22049877602859706 : ℝ)
            by
        norm_num];
        exact hau618)
  have hat1 :
    (Real.pi / 2 - (2 * (2959483383238434001347 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6723061076912809 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6723061076912809 : ℝ) =
              (6723061076912809 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau617)
  have hat2 :
    Real.arctan (375000000000000 / 3361530538456403 : ℝ) ≤
      (1110969860924394921403 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 3361530538456403 : ℚ))
        (U := (1110969860924394921403 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (451995502439 / 1000000000000 : ℚ))
      (lo := (3361530538456403 / 5000000000000000 : ℚ))
      (hi := (6723061076912809 / 10000000000000000 : ℚ))
      (s := (3361530538456403 / 5000000000000000 : ℚ))
      (r₁ := (1451995502439 / 1000000000000 : ℚ))
      (r₂ := (457620502439 / 1000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6723061076912809 : ℚ))
      (z₂ := (375000000000000 / 3361530538456403 : ℚ))
      (L := (3729388189040054123869 / 10000000000000000000000 : ℚ))
      (U := (-(7817150351193086393177 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_424 :
    ((3733947424958614430597 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(975336424718981787153 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6727983742379657 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2961178134875425243097 / 10000000000000000000000 : ℝ))) -
              6 * (1110163662135900473617 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1810630609509 / 4000000000000 : ℝ) := by
  have hL1 :
    (3733947424958614430597 / 10000000000000000000000 : ℝ) ≤
      Real.log (5810630609509 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (5810630609509 / 4000000000000 : ℚ))
        (L := (3733947424958614430597 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (1833130609509 / 4000000000000 : ℝ) ≤
      (-(975336424718981787153 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1833130609509 / 4000000000000 : ℚ))
        (r' := (1833130609509 / 1000000000000 : ℚ))
        (U := (-(975336424718981787153 / 1250000000000000000000 : ℚ)))
        (U' := (757531526031018212847 / 1250000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau620 :
    Real.arctan (3363991871189830 / 11026312413859013 : ℝ) ≤
      (2961178134875425243097 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3363991871189830 / 11026312413859013 : ℚ))
        (U := (2961178134875425243097 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau619 :
    Real.arctan (336399187118983 / 500000000000000 : ℝ) ≤
      (2 * (2961178134875425243097 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6026312413859013 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (336399187118983 / 500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (336399187118983 / 500000000000000 : ℝ) /
                (1 + (6026312413859013 / 5000000000000000 : ℝ)) =
              (3363991871189830 / 11026312413859013 : ℝ)
            by
        norm_num];
        exact hau620)
  have hat1 :
    (Real.pi / 2 - (2 * (2961178134875425243097 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (500000000000000 / 336399187118983 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 336399187118983 : ℝ) =
              (336399187118983 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau619)
  have hat2 :
    Real.arctan (750000000000000 / 6727983742379657 : ℝ) ≤
      (1110163662135900473617 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 6727983742379657 : ℚ))
        (U := (1110163662135900473617 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1810630609509 / 4000000000000 : ℚ))
      (lo := (6727983742379657 / 10000000000000000 : ℚ))
      (hi := (336399187118983 / 500000000000000 : ℚ))
      (s := (6727983742379657 / 10000000000000000 : ℚ))
      (r₁ := (5810630609509 / 4000000000000 : ℚ))
      (r₂ := (1833130609509 / 4000000000000 : ℚ))
      (z₁ := (500000000000000 / 336399187118983 : ℚ))
      (z₂ := (750000000000000 / 6727983742379657 : ℚ))
      (L := (3733947424958614430597 / 10000000000000000000000 : ℚ))
      (U := (-(975336424718981787153 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_425 :
    ((3738504583161202382823 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1557650664052654548403 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((841612851088889 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (592574175131759472259 / 2000000000000000000000 : ℝ))) -
              6 * (1109359215933374475979 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (906639604631 / 2000000000000 : ℝ) := by
  have hL1 :
    (3738504583161202382823 / 10000000000000000000000 : ℝ) ≤
      Real.log (2906639604631 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2906639604631 / 2000000000000 : ℚ))
        (L := (3738504583161202382823 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (917889604631 / 2000000000000 : ℝ) ≤
      (-(1557650664052654548403 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (917889604631 / 2000000000000 : ℚ))
        (r' := (917889604631 / 500000000000 : ℚ))
        (U := (-(1557650664052654548403 / 2000000000000000000000 : ℚ)))
        (U' := (1214938057147345451597 / 2000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau622 :
    Real.arctan (6732902808711115 / 22055371426528093 : ℝ) ≤
      (592574175131759472259 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6732902808711115 / 22055371426528093 : ℚ))
        (U := (592574175131759472259 / 2000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau621 :
    Real.arctan (1346580561742223 / 2000000000000000 : ℝ) ≤
      (2 * (592574175131759472259 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12055371426528093 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1346580561742223 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1346580561742223 / 2000000000000000 : ℝ) /
                (1 + (12055371426528093 / 10000000000000000 : ℝ)) =
              (6732902808711115 / 22055371426528093 : ℝ)
            by
        norm_num];
        exact hau622)
  have hat1 :
    (Real.pi / 2 - (2 * (592574175131759472259 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1346580561742223 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1346580561742223 : ℝ) =
              (1346580561742223 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau621)
  have hat2 :
    Real.arctan (93750000000000 / 841612851088889 : ℝ) ≤
      (1109359215933374475979 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (93750000000000 / 841612851088889 : ℚ))
        (U := (1109359215933374475979 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (906639604631 / 2000000000000 : ℚ))
      (lo := (841612851088889 / 1250000000000000 : ℚ))
      (hi := (1346580561742223 / 2000000000000000 : ℚ))
      (s := (841612851088889 / 1250000000000000 : ℚ))
      (r₁ := (2906639604631 / 2000000000000 : ℚ))
      (r₂ := (917889604631 / 2000000000000 : ℚ))
      (z₁ := (2000000000000000 / 1346580561742223 : ℚ))
      (z₂ := (93750000000000 / 841612851088889 : ℚ))
      (L := (3738504583161202382823 / 10000000000000000000000 : ℚ))
      (U := (-(1557650664052654548403 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_426 :
    ((93576491638516288227 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7773836058532506180713 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1684454570947503 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1482280805065932959781 / 5000000000000000000000 : ℝ))) -
              6 * (1108556515976043602471 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (363185561803 / 800000000000 : ℝ) := by
  have hL1 :
    (93576491638516288227 / 250000000000000000000 : ℝ) ≤
      Real.log (1163185561803 / 800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1163185561803 / 800000000000 : ℚ))
        (L := (93576491638516288227 / 250000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (367685561803 / 800000000000 : ℝ) ≤
      (-(7773836058532506180713 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (367685561803 / 800000000000 : ℚ))
        (r' := (367685561803 / 200000000000 : ℚ))
        (U := (-(7773836058532506180713 / 10000000000000000000000 : ℚ)))
        (U' := (6089107547467493819287 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau624 :
    Real.arctan (1347563656758003 / 4411623479943542 : ℝ) ≤
      (1482280805065932959781 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1347563656758003 / 4411623479943542 : ℚ))
        (U := (1482280805065932959781 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau623 :
    Real.arctan (1347563656758003 / 2000000000000000 : ℝ) ≤
      (2 * (1482280805065932959781 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1205811739971771 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1347563656758003 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1347563656758003 / 2000000000000000 : ℝ) /
                (1 + (1205811739971771 / 1000000000000000 : ℝ)) =
              (1347563656758003 / 4411623479943542 : ℝ)
            by
        norm_num];
        exact hau624)
  have hat1 :
    (Real.pi / 2 - (2 * (1482280805065932959781 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1347563656758003 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1347563656758003 : ℝ) =
              (1347563656758003 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau623)
  have hat2 :
    Real.arctan (62500000000000 / 561484856982501 : ℝ) ≤
      (1108556515976043602471 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (62500000000000 / 561484856982501 : ℚ))
        (U := (1108556515976043602471 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (363185561803 / 800000000000 : ℚ))
      (lo := (1684454570947503 / 2500000000000000 : ℚ))
      (hi := (1347563656758003 / 2000000000000000 : ℚ))
      (s := (1684454570947503 / 2500000000000000 : ℚ))
      (r₁ := (1163185561803 / 800000000000 : ℚ))
      (r₂ := (367685561803 / 800000000000 : ℚ))
      (z₁ := (2000000000000000 / 1347563656758003 : ℚ))
      (z₂ := (62500000000000 / 561484856982501 : ℚ))
      (L := (93576491638516288227 / 250000000000000000000 : ℚ))
      (U := (-(7773836058532506180713 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_427 :
    ((1873806336993604995811 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3879719776312348896627 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3371365087735233 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (92695323213183203139 / 312500000000000000000 : ℝ))) -
              6 * (1107755555955205237929 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (28415256387 / 62500000000 : ℝ) := by
  have hL1 :
    (1873806336993604995811 / 5000000000000000000000 : ℝ) ≤
      Real.log (90915256387 / 62500000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (90915256387 / 62500000000 : ℚ))
        (L := (1873806336993604995811 / 5000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (28766818887 / 62500000000 : ℝ) ≤
      (-(3879719776312348896627 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (28766818887 / 62500000000 : ℚ))
        (r' := (28766818887 / 15625000000 : ℚ))
        (U := (-(3879719776312348896627 / 5000000000000000000000 : ℚ)))
        (U' := (3051752026687651103373 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau626 :
    Real.arctan (6742730175470469 / 22060862747714194 : ℝ) ≤
      (92695323213183203139 / 312500000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6742730175470469 / 22060862747714194 : ℚ))
        (U := (92695323213183203139 / 312500000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau625 :
    Real.arctan (6742730175470469 / 10000000000000000 : ℝ) ≤
      (2 * (92695323213183203139 / 312500000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6030431373857097 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6742730175470469 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6742730175470469 / 10000000000000000 : ℝ) /
                (1 + (6030431373857097 / 5000000000000000 : ℝ)) =
              (6742730175470469 / 22060862747714194 : ℝ)
            by
        norm_num];
        exact hau626)
  have hat1 :
    (Real.pi / 2 - (2 * (92695323213183203139 / 312500000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6742730175470469 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6742730175470469 : ℝ) =
              (6742730175470469 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau625)
  have hat2 :
    Real.arctan (125000000000000 / 1123788362578411 : ℝ) ≤
      (1107755555955205237929 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (125000000000000 / 1123788362578411 : ℚ))
        (U := (1107755555955205237929 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (28415256387 / 62500000000 : ℚ))
      (lo := (3371365087735233 / 5000000000000000 : ℚ))
      (hi := (6742730175470469 / 10000000000000000 : ℚ))
      (s := (3371365087735233 / 5000000000000000 : ℚ))
      (r₁ := (90915256387 / 62500000000 : ℚ))
      (r₂ := (28766818887 / 62500000000 : ℚ))
      (z₁ := (10000000000000000 / 6742730175470469 : ℚ))
      (z₂ := (125000000000000 / 1123788362578411 : ℚ))
      (L := (1873806336993604995811 / 5000000000000000000000 : ℚ))
      (U := (-(3879719776312348896627 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_428 :
    ((938040902597136293219 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(968132967857934315427 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1686909622894499 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (593587415648002736951 / 2000000000000000000000 : ℝ))) -
              6 * (2213912659188038901 / 20000000000000000000 : ℝ)))) ≤
      Vfield (1821225008521 / 4000000000000 : ℝ) := by
  have hL1 :
    (938040902597136293219 / 2500000000000000000000 : ℝ) ≤
      Real.log (5821225008521 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (5821225008521 / 4000000000000 : ℚ))
        (L := (938040902597136293219 / 2500000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (1843725008521 / 4000000000000 : ℝ) ≤
      (-(968132967857934315427 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1843725008521 / 4000000000000 : ℚ))
        (r' := (1843725008521 / 1000000000000 : ℚ))
        (U := (-(968132967857934315427 / 1250000000000000000000 : ℚ)))
        (U' := (764734982892065684573 / 1250000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau628 :
    Real.arctan (6747638491577999 / 22063607470944377 : ℝ) ≤
      (593587415648002736951 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6747638491577999 / 22063607470944377 : ℚ))
        (U := (593587415648002736951 / 2000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau627 :
    Real.arctan (6747638491577999 / 10000000000000000 : ℝ) ≤
      (2 * (593587415648002736951 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12063607470944377 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6747638491577999 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6747638491577999 / 10000000000000000 : ℝ) /
                (1 + (12063607470944377 / 10000000000000000 : ℝ)) =
              (6747638491577999 / 22063607470944377 : ℝ)
            by
        norm_num];
        exact hau628)
  have hat1 :
    (Real.pi / 2 - (2 * (593587415648002736951 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6747638491577999 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6747638491577999 : ℝ) =
              (6747638491577999 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau627)
  have hat2 :
    Real.arctan (187500000000000 / 1686909622894499 : ℝ) ≤
      (2213912659188038901 / 20000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 1686909622894499 : ℚ))
        (U := (2213912659188038901 / 20000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1821225008521 / 4000000000000 : ℚ))
      (lo := (1686909622894499 / 2500000000000000 : ℚ))
      (hi := (6747638491577999 / 10000000000000000 : ℚ))
      (s := (1686909622894499 / 2500000000000000 : ℚ))
      (r₁ := (5821225008521 / 4000000000000 : ℚ))
      (r₂ := (1843725008521 / 4000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6747638491577999 : ℚ))
      (z₂ := (187500000000000 / 1686909622894499 : ℚ))
      (L := (938040902597136293219 / 2500000000000000000000 : ℚ))
      (U := (-(968132967857934315427 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_429 :
    ((3756712476629748451179 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(386535428491473142307 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1350508647981937 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1484810910440810834293 / 5000000000000000000000 : ℝ))) -
              6 * (276539707661825492393 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (911936804137 / 2000000000000 : ℝ) := by
  have hL1 :
    (3756712476629748451179 / 10000000000000000000000 : ℝ) ≤
      Real.log (2911936804137 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2911936804137 / 2000000000000 : ℚ))
        (L := (3756712476629748451179 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (923186804137 / 2000000000000 : ℝ) ≤
      (-(386535428491473142307 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (923186804137 / 2000000000000 : ℚ))
        (r' := (923186804137 / 500000000000 : ℚ))
        (U := (-(386535428491473142307 / 500000000000000000000 : ℚ)))
        (U' := (306611751808526857693 / 500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau630 :
    Real.arctan (6752543239909688 / 22066351569834603 : ℝ) ≤
      (1484810910440810834293 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6752543239909688 / 22066351569834603 : ℚ))
        (U := (1484810910440810834293 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau629 :
    Real.arctan (844067904988711 / 1250000000000000 : ℝ) ≤
      (2 * (1484810910440810834293 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12066351569834603 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (844067904988711 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (844067904988711 / 1250000000000000 : ℝ) /
                (1 + (12066351569834603 / 10000000000000000 : ℝ)) =
              (6752543239909688 / 22066351569834603 : ℝ)
            by
        norm_num];
        exact hau630)
  have hat1 :
    (Real.pi / 2 - (2 * (1484810910440810834293 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 844067904988711 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 844067904988711 : ℝ) =
              (844067904988711 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau629)
  have hat2 :
    Real.arctan (150000000000000 / 1350508647981937 : ℝ) ≤
      (276539707661825492393 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 1350508647981937 : ℚ))
        (U := (276539707661825492393 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (911936804137 / 2000000000000 : ℚ))
      (lo := (1350508647981937 / 2000000000000000 : ℚ))
      (hi := (844067904988711 / 1250000000000000 : ℚ))
      (s := (1350508647981937 / 2000000000000000 : ℚ))
      (r₁ := (2911936804137 / 2000000000000 : ℚ))
      (r₂ := (923186804137 / 2000000000000 : ℚ))
      (z₁ := (1250000000000000 / 844067904988711 : ℚ))
      (z₂ := (150000000000000 / 1350508647981937 : ℚ))
      (L := (3756712476629748451179 / 10000000000000000000000 : ℚ))
      (U := (-(386535428491473142307 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_430 :
    ((3761259274593339865841 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1929093493589703793197 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3378722214117157 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2971304575226139195549 / 10000000000000000000000 : ℝ))) -
              6 * (1105363052901320432927 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1826522208027 / 4000000000000 : ℝ) := by
  have hL1 :
    (3761259274593339865841 / 10000000000000000000000 : ℝ) ≤
      Real.log (5826522208027 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (5826522208027 / 4000000000000 : ℚ))
        (L := (3761259274593339865841 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (1849022208027 / 4000000000000 : ℝ) ≤
      (-(1929093493589703793197 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1849022208027 / 4000000000000 : ℚ))
        (r' := (1849022208027 / 1000000000000 : ℚ))
        (U := (-(1929093493589703793197 / 2500000000000000000000 : ℚ)))
        (U' := (1536642407910296206803 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau632 :
    Real.arctan (6757444428234317 / 22069095044810733 : ℝ) ≤
      (2971304575226139195549 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6757444428234317 / 22069095044810733 : ℚ))
        (U := (2971304575226139195549 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau631 :
    Real.arctan (6757444428234317 / 10000000000000000 : ℝ) ≤
      (2 * (2971304575226139195549 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12069095044810733 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6757444428234317 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6757444428234317 / 10000000000000000 : ℝ) /
                (1 + (12069095044810733 / 10000000000000000 : ℝ)) =
              (6757444428234317 / 22069095044810733 : ℝ)
            by
        norm_num];
        exact hau632)
  have hat1 :
    (Real.pi / 2 - (2 * (2971304575226139195549 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6757444428234317 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6757444428234317 : ℝ) =
              (6757444428234317 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau631)
  have hat2 :
    Real.arctan (375000000000000 / 3378722214117157 : ℝ) ≤
      (1105363052901320432927 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 3378722214117157 : ℚ))
        (U := (1105363052901320432927 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1826522208027 / 4000000000000 : ℚ))
      (lo := (3378722214117157 / 5000000000000000 : ℚ))
      (hi := (6757444428234317 / 10000000000000000 : ℚ))
      (s := (3378722214117157 / 5000000000000000 : ℚ))
      (r₁ := (5826522208027 / 4000000000000 : ℚ))
      (r₂ := (1849022208027 / 4000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6757444428234317 : ℚ))
      (z₂ := (375000000000000 / 3378722214117157 : ℚ))
      (L := (3761259274593339865841 / 10000000000000000000000 : ℚ))
      (U := (-(1929093493589703793197 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_431 :
    ((1882902003079636395783 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1925514974385436700747 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6762342064292517 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2972985345737252723841 / 10000000000000000000000 : ℝ))) -
              6 * (1104568990173589174241 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (91458540389 / 200000000000 : ℝ) := by
  have hL1 :
    (1882902003079636395783 / 5000000000000000000000 : ℝ) ≤
      Real.log (291458540389 / 200000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (291458540389 / 200000000000 : ℚ))
        (L := (1882902003079636395783 / 5000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (92583540389 / 200000000000 : ℝ) ≤
      (-(1925514974385436700747 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (92583540389 / 200000000000 : ℚ))
        (r' := (92583540389 / 50000000000 : ℚ))
        (U := (-(1925514974385436700747 / 2500000000000000000000 : ℚ)))
        (U' := (1540220927114563299253 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau634 :
    Real.arctan (6762342064292520 / 22071837896298143 : ℝ) ≤
      (2972985345737252723841 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6762342064292520 / 22071837896298143 : ℚ))
        (U := (2972985345737252723841 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau633 :
    Real.arctan (169058551607313 / 250000000000000 : ℝ) ≤
      (2 * (2972985345737252723841 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12071837896298143 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (169058551607313 / 250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (169058551607313 / 250000000000000 : ℝ) /
                (1 + (12071837896298143 / 10000000000000000 : ℝ)) =
              (6762342064292520 / 22071837896298143 : ℝ)
            by
        norm_num];
        exact hau634)
  have hat1 :
    (Real.pi / 2 - (2 * (2972985345737252723841 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (250000000000000 / 169058551607313 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 169058551607313 : ℝ) =
              (169058551607313 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hau633)
  have hat2 :
    Real.arctan (250000000000000 / 2254114021430839 : ℝ) ≤
      (1104568990173589174241 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2254114021430839 : ℚ))
        (U := (1104568990173589174241 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (91458540389 / 200000000000 : ℚ))
      (lo := (6762342064292517 / 10000000000000000 : ℚ))
      (hi := (169058551607313 / 250000000000000 : ℚ))
      (s := (6762342064292517 / 10000000000000000 : ℚ))
      (r₁ := (291458540389 / 200000000000 : ℚ))
      (r₂ := (92583540389 / 200000000000 : ℚ))
      (z₁ := (250000000000000 / 169058551607313 : ℚ))
      (z₂ := (250000000000000 / 2254114021430839 : ℚ))
      (L := (1882902003079636395783 / 5000000000000000000000 : ℚ))
      (U := (-(1925514974385436700747 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_432 :
    ((1885173336602469301127 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(768776628072108333261 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6767236155796913 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2974664136862955190747 / 10000000000000000000000 : ℝ))) -
              6 * (551888318156334600501 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1831819407533 / 4000000000000 : ℝ) := by
  have hL1 :
    (1885173336602469301127 / 5000000000000000000000 : ℝ) ≤
      Real.log (5831819407533 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (5831819407533 / 4000000000000 : ℚ))
        (L := (1885173336602469301127 / 5000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (1854319407533 / 4000000000000 : ℝ) ≤
      (-(768776628072108333261 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1854319407533 / 4000000000000 : ℚ))
        (r' := (1854319407533 / 1000000000000 : ℚ))
        (U := (-(768776628072108333261 / 1000000000000000000000 : ℚ)))
        (U' := (617517732527891666739 / 1000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau636 :
    Real.arctan (1691809038949229 / 5518645031180432 : ℝ) ≤
      (2974664136862955190747 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1691809038949229 / 5518645031180432 : ℚ))
        (U := (2974664136862955190747 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau635 :
    Real.arctan (1691809038949229 / 2500000000000000 : ℝ) ≤
      (2 * (2974664136862955190747 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (188665314448777 / 156250000000000 : ℝ) ≤
          Real.sqrt (1 + (1691809038949229 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1691809038949229 / 2500000000000000 : ℝ) /
                (1 + (188665314448777 / 156250000000000 : ℝ)) =
              (1691809038949229 / 5518645031180432 : ℝ)
            by
        norm_num];
        exact hau636)
  have hat1 :
    (Real.pi / 2 - (2 * (2974664136862955190747 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1691809038949229 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1691809038949229 : ℝ) =
              (1691809038949229 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau635)
  have hat2 :
    Real.arctan (750000000000000 / 6767236155796913 : ℝ) ≤
      (551888318156334600501 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 6767236155796913 : ℚ))
        (U := (551888318156334600501 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1831819407533 / 4000000000000 : ℚ))
      (lo := (6767236155796913 / 10000000000000000 : ℚ))
      (hi := (1691809038949229 / 2500000000000000 : ℚ))
      (s := (6767236155796913 / 10000000000000000 : ℚ))
      (r₁ := (5831819407533 / 4000000000000 : ℚ))
      (r₂ := (1854319407533 / 4000000000000 : ℚ))
      (z₁ := (2500000000000000 / 1691809038949229 : ℚ))
      (z₂ := (750000000000000 / 6767236155796913 : ℚ))
      (L := (1885173336602469301127 / 5000000000000000000000 : ℚ))
      (U := (-(768776628072108333261 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
