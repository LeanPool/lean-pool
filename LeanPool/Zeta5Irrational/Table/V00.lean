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

/-! # V00: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma V_1 :
    ((8967502915859873 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25870887852728765963031 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((14973028876951 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (11978279880015751031 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (796870528491162609301 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (7174131 / 200000000000 : ℝ) := by
  have hL1 :
    (8967502915859873 / 250000000000000000000 : ℝ) ≤ Real.log (200007174131 / 200000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (200007174131 / 200000000000 : ℚ))
        (L := (8967502915859873 / 250000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (1132174131 / 200000000000 : ℝ) ≤
      (-(25870887852728765963031 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1132174131 / 200000000000 : ℚ))
        (r' := (1132174131 / 781250000 : ℚ))
        (U := (-(25870887852728765963031 / 5000000000000000000000 : ℚ)))
        (U' := (1854999359271234036969 / 5000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau3 :
    Real.arctan (14973028876951 / 2500000000000000 : ℝ) ≤
      (11978279880015751031 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (14973028876951 / 2500000000000000 : ℚ))
        (U := (11978279880015751031 / 2000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (11978279880015751031 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 14973028876951 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 14973028876951 : ℝ) =
              (14973028876951 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau3)
  have hal4 :
    (796870528491162609301 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (59892115507801 / 750000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (59892115507801 / 750000000000000 : ℚ))
        (L := (796870528491162609301 / 10000000000000000000000 : ℚ))
        3 (by decide +kernel))
  have hat2 :
    Real.arctan (750000000000000 / 59892115507801 : ℝ) ≤
      (Real.pi / 2 - (796870528491162609301 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 59892115507801 : ℝ) =
              (59892115507801 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal4)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (7174131 / 200000000000 : ℚ))
      (lo := (59892115507801 / 10000000000000000 : ℚ))
      (hi := (14973028876951 / 2500000000000000 : ℚ))
      (s := (14973028876951 / 2500000000000000 : ℚ))
      (r₁ := (200007174131 / 200000000000 : ℚ))
      (r₂ := (1132174131 / 200000000000 : ℚ))
      (z₁ := (2500000000000000 / 14973028876951 : ℚ))
      (z₂ := (750000000000000 / 59892115507801 : ℚ))
      (L := (8967502915859873 / 250000000000000000000 : ℚ))
      (U := (-(25870887852728765963031 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_2 :
    ((67255668762557231 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25855071403081196359633 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4584535081561 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (73351245745236760791 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (974933462669317096681 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (21522393 / 400000000000 : ℝ) := by
  have hL1 :
    (67255668762557231 / 1250000000000000000000 : ℝ) ≤
      Real.log (400021522393 / 400000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (400021522393 / 400000000000 : ℚ))
        (L := (67255668762557231 / 1250000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (2271522393 / 400000000000 : ℝ) ≤
      (-(25855071403081196359633 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2271522393 / 400000000000 : ℚ))
        (r' := (2271522393 / 1562500000 : ℚ))
        (U := (-(25855071403081196359633 / 5000000000000000000000 : ℚ)))
        (U' := (1870815808918803640367 / 5000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau5 :
    Real.arctan (4584535081561 / 625000000000000 : ℝ) ≤
      (73351245745236760791 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4584535081561 / 625000000000000 : ℚ))
        (U := (73351245745236760791 / 10000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (73351245745236760791 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 4584535081561 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 4584535081561 : ℝ) =
              (4584535081561 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau5)
  have hal6 :
    (974933462669317096681 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (73352561304973 / 750000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (73352561304973 / 750000000000000 : ℚ))
        (L := (974933462669317096681 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hat2 :
    Real.arctan (750000000000000 / 73352561304973 : ℝ) ≤
      (Real.pi / 2 - (974933462669317096681 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 73352561304973 : ℝ) =
              (73352561304973 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal6)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (21522393 / 400000000000 : ℚ))
      (lo := (73352561304973 / 10000000000000000 : ℚ))
      (hi := (4584535081561 / 625000000000000 : ℚ))
      (s := (4584535081561 / 625000000000000 : ℚ))
      (r₁ := (400021522393 / 400000000000 : ℚ))
      (r₂ := (2271522393 / 400000000000 : ℚ))
      (z₁ := (625000000000000 / 4584535081561 : ℚ))
      (z₂ := (750000000000000 / 73352561304973 : ℚ))
      (L := (67255668762557231 / 1250000000000000000000 : ℚ))
      (U := (-(25855071403081196359633 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_3 :
    ((358693683576464417 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25839304827724134032909 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5293765126897 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (16939643323085595789 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (35142868108192574273 / 312500000000000000000 : ℝ))))) ≤
      Vfield (7174131 / 100000000000 : ℝ) := by
  have hL1 :
    (358693683576464417 / 5000000000000000000000 : ℝ) ≤
      Real.log (100007174131 / 100000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (100007174131 / 100000000000 : ℚ))
        (L := (358693683576464417 / 5000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (569674131 / 100000000000 : ℝ) ≤
      (-(25839304827724134032909 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (569674131 / 100000000000 : ℚ))
        (r' := (569674131 / 390625000 : ℚ))
        (U := (-(25839304827724134032909 / 5000000000000000000000 : ℚ)))
        (U' := (1886582384275865967091 / 5000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau7 :
    Real.arctan (5293765126897 / 625000000000000 : ℝ) ≤
      (16939643323085595789 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5293765126897 / 625000000000000 : ℚ))
        (U := (16939643323085595789 / 2000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (16939643323085595789 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 5293765126897 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 5293765126897 : ℝ) =
              (5293765126897 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau7)
  have hal8 :
    (35142868108192574273 / 312500000000000000000 : ℝ) ≤
      Real.arctan (84700242030349 / 750000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (84700242030349 / 750000000000000 : ℚ))
        (L := (35142868108192574273 / 312500000000000000000 : ℚ))
        4 (by decide +kernel))
  have hat2 :
    Real.arctan (750000000000000 / 84700242030349 : ℝ) ≤
      (Real.pi / 2 - (35142868108192574273 / 312500000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 84700242030349 : ℝ) =
              (84700242030349 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal8)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (7174131 / 100000000000 : ℚ))
      (lo := (84700242030349 / 10000000000000000 : ℚ))
      (hi := (5293765126897 / 625000000000000 : ℚ))
      (s := (5293765126897 / 625000000000000 : ℚ))
      (r₁ := (100007174131 / 100000000000 : ℚ))
      (r₂ := (569674131 / 100000000000 : ℚ))
      (z₁ := (625000000000000 / 5293765126897 : ℚ))
      (z₂ := (750000000000000 / 84700242030349 : ℚ))
      (L := (358693683576464417 / 5000000000000000000000 : ℚ))
      (U := (-(25839304827724134032909 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_4 :
    ((37063408769787157 / 500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51674418216178446788859 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((86098527861981 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (17219280094892480421 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1142976954465331252621 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (14825913 / 200000000000 : ℝ) := by
  have hL1 :
    (37063408769787157 / 500000000000000000000 : ℝ) ≤
      Real.log (200014825913 / 200000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (200014825913 / 200000000000 : ℚ))
        (L := (37063408769787157 / 500000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (1139825913 / 200000000000 : ℝ) ≤
      (-(51674418216178446788859 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1139825913 / 200000000000 : ℚ))
        (r' := (1139825913 / 781250000 : ℚ))
        (U := (-(51674418216178446788859 / 10000000000000000000000 : ℚ)))
        (U' := (3777356207821553211141 / 10000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau9 :
    Real.arctan (86098527861981 / 10000000000000000 : ℝ) ≤
      (17219280094892480421 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (86098527861981 / 10000000000000000 : ℚ))
        (U := (17219280094892480421 / 2000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (17219280094892480421 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 86098527861981 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 86098527861981 : ℝ) =
              (86098527861981 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau9)
  have hal10 :
    (1142976954465331252621 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (14349754643663 / 125000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (14349754643663 / 125000000000000 : ℚ))
        (L := (1142976954465331252621 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hat2 :
    Real.arctan (125000000000000 / 14349754643663 : ℝ) ≤
      (Real.pi / 2 - (1142976954465331252621 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (125000000000000 / 14349754643663 : ℝ) =
              (14349754643663 / 125000000000000 : ℝ)
            by
        norm_num];
        exact hal10)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (14825913 / 200000000000 : ℚ))
      (lo := (43049263930989 / 5000000000000000 : ℚ))
      (hi := (86098527861981 / 10000000000000000 : ℚ))
      (s := (86098527861981 / 10000000000000000 : ℚ))
      (r₁ := (200014825913 / 200000000000 : ℚ))
      (r₂ := (1139825913 / 200000000000 : ℚ))
      (z₁ := (10000000000000000 / 86098527861981 : ℚ))
      (z₂ := (125000000000000 / 14349754643663 : ℚ))
      (L := (37063408769787157 / 500000000000000000000 : ℚ))
      (U := (-(51674418216178446788859 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_5 :
    ((196661542144736661 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51666458509222761164599 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((88694820029133 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (44346247166374961649 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (117713038222569168397 / 1000000000000000000000 : ℝ))))) ≤
      Vfield (78667711 / 1000000000000 : ℝ) := by
  have hL1 :
    (196661542144736661 / 2500000000000000000000 : ℝ) ≤
      Real.log (1000078667711 / 1000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1000078667711 / 1000000000000 : ℚ))
        (L := (196661542144736661 / 2500000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (5703667711 / 1000000000000 : ℝ) ≤
      (-(51666458509222761164599 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5703667711 / 1000000000000 : ℚ))
        (r' := (5703667711 / 3906250000 : ℚ))
        (U := (-(51666458509222761164599 / 10000000000000000000000 : ℚ)))
        (U' := (3785315914777238835401 / 10000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau11 :
    Real.arctan (88694820029133 / 10000000000000000 : ℝ) ≤
      (44346247166374961649 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (88694820029133 / 10000000000000000 : ℚ))
        (U := (44346247166374961649 / 5000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (44346247166374961649 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 88694820029133 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 88694820029133 : ℝ) =
              (88694820029133 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau11)
  have hal12 :
    (117713038222569168397 / 1000000000000000000000 : ℝ) ≤
      Real.arctan (2956494000971 / 25000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (2956494000971 / 25000000000000 : ℚ))
        (L := (117713038222569168397 / 1000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hat2 :
    Real.arctan (25000000000000 / 2956494000971 : ℝ) ≤
      (Real.pi / 2 - (117713038222569168397 / 1000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (25000000000000 / 2956494000971 : ℝ) = (2956494000971 / 25000000000000 : ℝ)
            by
        norm_num];
        exact hal12)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (78667711 / 1000000000000 : ℚ))
      (lo := (8869482002913 / 1000000000000000 : ℚ))
      (hi := (88694820029133 / 10000000000000000 : ℚ))
      (s := (88694820029133 / 10000000000000000 : ℚ))
      (r₁ := (1000078667711 / 1000000000000 : ℚ))
      (r₂ := (5703667711 / 1000000000000 : ℚ))
      (z₁ := (10000000000000000 / 88694820029133 : ℚ))
      (z₂ := (25000000000000 / 2956494000971 : ℚ))
      (L := (196661542144736661 / 2500000000000000000000 : ℚ))
      (U := (-(51666458509222761164599 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_6 :
    ((85811957048696007 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51653934194779139713727 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((92636730836101 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (92634081079116824847 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (614466029692359913717 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (85815639 / 1000000000000 : ℝ) := by
  have hL1 :
    (85811957048696007 / 1000000000000000000000 : ℝ) ≤
      Real.log (1000085815639 / 1000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1000085815639 / 1000000000000 : ℚ))
        (L := (85811957048696007 / 1000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (5710815639 / 1000000000000 : ℝ) ≤
      (-(51653934194779139713727 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5710815639 / 1000000000000 : ℚ))
        (r' := (5710815639 / 3906250000 : ℚ))
        (U := (-(51653934194779139713727 / 10000000000000000000000 : ℚ)))
        (U' := (3797840229220860286273 / 10000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau13 :
    Real.arctan (92636730836101 / 10000000000000000 : ℝ) ≤
      (92634081079116824847 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (92636730836101 / 10000000000000000 : ℚ))
        (U := (92634081079116824847 / 10000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (92634081079116824847 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 92636730836101 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 92636730836101 : ℝ) =
              (92636730836101 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau13)
  have hal14 :
    (614466029692359913717 / 5000000000000000000000 : ℝ) ≤
      Real.arctan (46318365418049 / 375000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (46318365418049 / 375000000000000 : ℚ))
        (L := (614466029692359913717 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hat2 :
    Real.arctan (375000000000000 / 46318365418049 : ℝ) ≤
      (Real.pi / 2 - (614466029692359913717 / 5000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (375000000000000 / 46318365418049 : ℝ) =
              (46318365418049 / 375000000000000 : ℝ)
            by
        norm_num];
        exact hal14)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (85815639 / 1000000000000 : ℚ))
      (lo := (46318365418049 / 5000000000000000 : ℚ))
      (hi := (92636730836101 / 10000000000000000 : ℚ))
      (s := (92636730836101 / 10000000000000000 : ℚ))
      (r₁ := (1000085815639 / 1000000000000 : ℚ))
      (r₂ := (5710815639 / 1000000000000 : ℚ))
      (z₁ := (10000000000000000 / 92636730836101 : ℚ))
      (z₂ := (375000000000000 / 46318365418049 : ℚ))
      (L := (85811957048696007 / 1000000000000000000000 : ℚ))
      (U := (-(51653934194779139713727 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_7 :
    ((30107723030942933 / 312500000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25817752990537051829671 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((19631541457563 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (49077277496392064609 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1301372761809135071741 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (19269871 / 200000000000 : ℝ) := by
  have hL1 :
    (30107723030942933 / 312500000000000000000 : ℝ) ≤
      Real.log (200019269871 / 200000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (200019269871 / 200000000000 : ℚ))
        (L := (30107723030942933 / 312500000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (1144269871 / 200000000000 : ℝ) ≤
      (-(25817752990537051829671 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1144269871 / 200000000000 : ℚ))
        (r' := (1144269871 / 781250000 : ℚ))
        (U := (-(25817752990537051829671 / 5000000000000000000000 : ℚ)))
        (U' := (1908134221462948170329 / 5000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau15 :
    Real.arctan (19631541457563 / 2000000000000000 : ℝ) ≤
      (49077277496392064609 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (19631541457563 / 2000000000000000 : ℚ))
        (U := (49077277496392064609 / 5000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (49077277496392064609 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 19631541457563 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 19631541457563 : ℝ) =
              (19631541457563 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau15)
  have hal16 :
    (1301372761809135071741 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (8179808940651 / 62500000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (8179808940651 / 62500000000000 : ℚ))
        (L := (1301372761809135071741 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hat2 :
    Real.arctan (62500000000000 / 8179808940651 : ℝ) ≤
      (Real.pi / 2 - (1301372761809135071741 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (62500000000000 / 8179808940651 : ℝ) = (8179808940651 / 62500000000000 : ℝ)
            by
        norm_num];
        exact hal16)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (19269871 / 200000000000 : ℚ))
      (lo := (24539426821953 / 2500000000000000 : ℚ))
      (hi := (19631541457563 / 2000000000000000 : ℚ))
      (s := (19631541457563 / 2000000000000000 : ℚ))
      (r₁ := (200019269871 / 200000000000 : ℚ))
      (r₂ := (1144269871 / 200000000000 : ℚ))
      (z₁ := (2000000000000000 / 19631541457563 : ℚ))
      (z₂ := (62500000000000 / 8179808940651 : ℚ))
      (L := (30107723030942933 / 312500000000000000000 : ℚ))
      (U := (-(25817752990537051829671 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_8 :
    ((278789739678365227 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51609021536891161835761 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((105604031173059 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (52800052853726802719 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1398857469718843080699 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (55761057 / 500000000000 : ℝ) := by
  have hL1 :
    (278789739678365227 / 2500000000000000000000 : ℝ) ≤
      Real.log (500055761057 / 500000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (500055761057 / 500000000000 : ℚ))
        (L := (278789739678365227 / 2500000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (2868261057 / 500000000000 : ℝ) ≤
      (-(51609021536891161835761 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2868261057 / 500000000000 : ℚ))
        (r' := (2868261057 / 1953125000 : ℚ))
        (U := (-(51609021536891161835761 / 10000000000000000000000 : ℚ)))
        (U' := (3842752887108838164239 / 10000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau17 :
    Real.arctan (105604031173059 / 10000000000000000 : ℝ) ≤
      (52800052853726802719 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (105604031173059 / 10000000000000000 : ℚ))
        (U := (52800052853726802719 / 5000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (52800052853726802719 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 105604031173059 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 105604031173059 : ℝ) =
              (105604031173059 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau17)
  have hal18 :
    (1398857469718843080699 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (550020995693 / 3906250000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (550020995693 / 3906250000000 : ℚ))
        (L := (1398857469718843080699 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hat2 :
    Real.arctan (3906250000000 / 550020995693 : ℝ) ≤
      (Real.pi / 2 - (1398857469718843080699 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show (1 : ℝ) / (3906250000000 / 550020995693 : ℝ) = (550020995693 / 3906250000000 : ℝ)
            by
        norm_num];
        exact hal18)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (55761057 / 500000000000 : ℚ))
      (lo := (1650062987079 / 156250000000000 : ℚ))
      (hi := (105604031173059 / 10000000000000000 : ℚ))
      (s := (105604031173059 / 10000000000000000 : ℚ))
      (r₁ := (500055761057 / 500000000000 : ℚ))
      (r₂ := (2868261057 / 500000000000 : ℚ))
      (z₁ := (10000000000000000 / 105604031173059 : ℚ))
      (z₂ := (3906250000000 / 550020995693 : ℚ))
      (L := (278789739678365227 / 2500000000000000000000 : ℚ))
      (U := (-(51609021536891161835761 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_9 :
    ((1333382420614834419 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51571047996245974723013 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((57738014340641 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (115470896292829511109 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (763841962364687947279 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (33336783 / 250000000000 : ℝ) := by
  have hL1 :
    (1333382420614834419 / 10000000000000000000000 : ℝ) ≤
      Real.log (250033336783 / 250000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (250033336783 / 250000000000 : ℚ))
        (L := (1333382420614834419 / 10000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (1439586783 / 250000000000 : ℝ) ≤
      (-(51571047996245974723013 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1439586783 / 250000000000 : ℚ))
        (r' := (1439586783 / 976562500 : ℚ))
        (U := (-(51571047996245974723013 / 10000000000000000000000 : ℚ)))
        (U' := (3880726427754025276987 / 10000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau19 :
    Real.arctan (57738014340641 / 5000000000000000 : ℝ) ≤
      (115470896292829511109 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (57738014340641 / 5000000000000000 : ℚ))
        (U := (115470896292829511109 / 10000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (115470896292829511109 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 57738014340641 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 57738014340641 : ℝ) =
              (57738014340641 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau19)
  have hal20 :
    (763841962364687947279 / 5000000000000000000000 : ℝ) ≤
      Real.arctan (115476028681279 / 750000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (115476028681279 / 750000000000000 : ℚ))
        (L := (763841962364687947279 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hat2 :
    Real.arctan (750000000000000 / 115476028681279 : ℝ) ≤
      (Real.pi / 2 - (763841962364687947279 / 5000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 115476028681279 : ℝ) =
              (115476028681279 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal20)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (33336783 / 250000000000 : ℚ))
      (lo := (115476028681279 / 10000000000000000 : ℚ))
      (hi := (57738014340641 / 5000000000000000 : ℚ))
      (s := (57738014340641 / 5000000000000000 : ℚ))
      (r₁ := (250033336783 / 250000000000 : ℚ))
      (r₂ := (1439586783 / 250000000000 : ℚ))
      (z₁ := (5000000000000000 / 57738014340641 : ℚ))
      (z₂ := (750000000000000 / 115476028681279 : ℚ))
      (L := (1333382420614834419 / 10000000000000000000000 : ℚ))
      (U := (-(51571047996245974723013 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_10 :
    ((66033623550755633 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51516061139574022265869 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((128490344384317 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (25696654786369851871 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1696732463001094446147 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (82548843 / 500000000000 : ℝ) := by
  have hL1 :
    (66033623550755633 / 400000000000000000000 : ℝ) ≤
      Real.log (500082548843 / 500000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (500082548843 / 500000000000 : ℚ))
        (L := (66033623550755633 / 400000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (2895048843 / 500000000000 : ℝ) ≤
      (-(51516061139574022265869 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2895048843 / 500000000000 : ℚ))
        (r' := (2895048843 / 1953125000 : ℚ))
        (U := (-(51516061139574022265869 / 10000000000000000000000 : ℚ)))
        (U' := (3935713284425977734131 / 10000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau21 :
    Real.arctan (128490344384317 / 10000000000000000 : ℝ) ≤
      (25696654786369851871 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (128490344384317 / 10000000000000000 : ℚ))
        (U := (25696654786369851871 / 2000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (25696654786369851871 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 128490344384317 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 128490344384317 : ℝ) =
              (128490344384317 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau21)
  have hal22 :
    (1696732463001094446147 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (64245172192157 / 375000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (64245172192157 / 375000000000000 : ℚ))
        (L := (1696732463001094446147 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat2 :
    Real.arctan (375000000000000 / 64245172192157 : ℝ) ≤
      (Real.pi / 2 - (1696732463001094446147 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (375000000000000 / 64245172192157 : ℝ) =
              (64245172192157 / 375000000000000 : ℝ)
            by
        norm_num];
        exact hal22)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (82548843 / 500000000000 : ℚ))
      (lo := (64245172192157 / 5000000000000000 : ℚ))
      (hi := (128490344384317 / 10000000000000000 : ℚ))
      (s := (128490344384317 / 10000000000000000 : ℚ))
      (r₁ := (500082548843 / 500000000000 : ℚ))
      (r₂ := (2895048843 / 500000000000 : ℚ))
      (z₁ := (10000000000000000 / 128490344384317 : ℚ))
      (z₂ := (375000000000000 / 64245172192157 : ℚ))
      (L := (66033623550755633 / 400000000000000000000 : ℚ))
      (U := (-(51516061139574022265869 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_11 :
    ((1060918377258494863 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51435029869943759185693 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((18209123228481 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (145662682903283762149 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (1918420011923721109387 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (53051547 / 250000000000 : ℝ) := by
  have hL1 :
    (1060918377258494863 / 5000000000000000000000 : ℝ) ≤
      Real.log (250053051547 / 250000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (250053051547 / 250000000000 : ℚ))
        (L := (1060918377258494863 / 5000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (1459301547 / 250000000000 : ℝ) ≤
      (-(51435029869943759185693 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1459301547 / 250000000000 : ℚ))
        (r' := (1459301547 / 976562500 : ℚ))
        (U := (-(51435029869943759185693 / 10000000000000000000000 : ℚ)))
        (U' := (4016744554056240814307 / 10000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau23 :
    Real.arctan (18209123228481 / 1250000000000000 : ℝ) ≤
      (145662682903283762149 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (18209123228481 / 1250000000000000 : ℚ))
        (U := (145662682903283762149 / 10000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (145662682903283762149 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 18209123228481 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 18209123228481 : ℝ) =
              (18209123228481 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau23)
  have hal24 :
    (1918420011923721109387 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (9711532388523 / 50000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (9711532388523 / 50000000000000 : ℚ))
        (L := (1918420011923721109387 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat2 :
    Real.arctan (50000000000000 / 9711532388523 : ℝ) ≤
      (Real.pi / 2 - (1918420011923721109387 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (50000000000000 / 9711532388523 : ℝ) = (9711532388523 / 50000000000000 : ℝ)
            by
        norm_num];
        exact hal24)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (53051547 / 250000000000 : ℚ))
      (lo := (29134597165569 / 2000000000000000 : ℚ))
      (hi := (18209123228481 / 1250000000000000 : ℚ))
      (s := (18209123228481 / 1250000000000000 : ℚ))
      (r₁ := (250053051547 / 250000000000 : ℚ))
      (r₂ := (1459301547 / 250000000000 : ℚ))
      (z₁ := (1250000000000000 / 18209123228481 : ℚ))
      (z₂ := (50000000000000 / 9711532388523 : ℚ))
      (L := (1060918377258494863 / 5000000000000000000000 : ℚ))
      (U := (-(51435029869943759185693 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_12 :
    ((2480279280302765263 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12843449268270218651961 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((9843674394551 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (39371442317394135319 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2069906494283519593871 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (496117379 / 2000000000000 : ℝ) := by
  have hL1 :
    (2480279280302765263 / 10000000000000000000000 : ℝ) ≤
      Real.log (2000496117379 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2000496117379 / 2000000000000 : ℚ))
        (L := (2480279280302765263 / 10000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (11746117379 / 2000000000000 : ℝ) ≤
      (-(12843449268270218651961 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11746117379 / 2000000000000 : ℚ))
        (r' := (11746117379 / 7812500000 : ℚ))
        (U := (-(12843449268270218651961 / 2500000000000000000000 : ℚ)))
        (U' := (1019494337729781348039 / 2500000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau25 :
    Real.arctan (9843674394551 / 625000000000000 : ℝ) ≤
      (39371442317394135319 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (9843674394551 / 625000000000000 : ℚ))
        (U := (39371442317394135319 / 2500000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (39371442317394135319 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (625000000000000 / 9843674394551 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 9843674394551 : ℝ) =
              (9843674394551 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau25)
  have hal26 :
    (2069906494283519593871 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (157498790312813 / 750000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (157498790312813 / 750000000000000 : ℚ))
        (L := (2069906494283519593871 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat2 :
    Real.arctan (750000000000000 / 157498790312813 : ℝ) ≤
      (Real.pi / 2 - (2069906494283519593871 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 157498790312813 : ℝ) =
              (157498790312813 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal26)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (496117379 / 2000000000000 : ℚ))
      (lo := (157498790312813 / 10000000000000000 : ℚ))
      (hi := (9843674394551 / 625000000000000 : ℚ))
      (s := (9843674394551 / 625000000000000 : ℚ))
      (r₁ := (2000496117379 / 2000000000000 : ℚ))
      (r₂ := (11746117379 / 2000000000000 : ℚ))
      (z₁ := (625000000000000 / 9843674394551 : ℚ))
      (z₂ := (750000000000000 / 157498790312813 : ℚ))
      (L := (2480279280302765263 / 10000000000000000000000 : ℚ))
      (U := (-(12843449268270218651961 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
