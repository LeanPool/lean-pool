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

/-! # V15: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

lemma V_181 :
    ((565756240004760742753 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(20760370400176964455387 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1730616131954301 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3332169574449736592719 / 10000000000000000000000 : ℝ)) -
              6 * (213386950021971650621 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (3833641211111 / 32000000000000 : ℝ) := by
  have hL1 :
    (565756240004760742753 / 5000000000000000000000 : ℝ) ≤
      Real.log (35833641211111 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (35833641211111 / 32000000000000 : ℚ))
        (L := (565756240004760742753 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (4013641211111 / 32000000000000 : ℝ) ≤
      (-(20760370400176964455387 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (4013641211111 / 32000000000000 : ℝ) = (4013641211111 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (4013641211111 / 4000000000000 : ℚ))
             (U := (34045008823035544613 / 10000000000000000000000 : ℚ))
             3 (by decide +kernel)) :
          Real.log (4013641211111 / 4000000000000 : ℝ) ≤
            (34045008823035544613 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau243 :
    Real.arctan (692246452781721 / 2000000000000000 : ℝ) ≤
      (3332169574449736592719 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (692246452781721 / 2000000000000000 : ℚ))
        (U := (3332169574449736592719 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3332169574449736592719 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 692246452781721 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 692246452781721 : ℝ) =
              (692246452781721 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau243)
  have hat2 :
    Real.arctan (125000000000000 / 576872043984767 : ℝ) ≤
      (213386950021971650621 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (125000000000000 / 576872043984767 : ℚ))
        (U := (213386950021971650621 / 1000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (3833641211111 / 32000000000000 : ℚ))
      (lo := (1730616131954301 / 5000000000000000 : ℚ))
      (hi := (692246452781721 / 2000000000000000 : ℚ))
      (s := (1730616131954301 / 5000000000000000 : ℚ))
      (r₁ := (35833641211111 / 32000000000000 : ℚ))
      (r₂ := (4013641211111 / 32000000000000 : ℚ))
      (z₁ := (2000000000000000 / 692246452781721 : ℚ))
      (z₂ := (125000000000000 / 576872043984767 : ℚ))
      (L := (565756240004760742753 / 5000000000000000000000 : ℚ))
      (U := (-(20760370400176964455387 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_182 :
    ((227553573578023514173 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4140932104806516067421 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3471339599085811 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (668238552174649568123 / 2000000000000000000000 : ℝ)) -
              6 * (265980315177075916949 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (1928031777949 / 16000000000000 : ℝ) := by
  have hL1 :
    (227553573578023514173 / 2000000000000000000000 : ℝ) ≤
      Real.log (17928031777949 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (17928031777949 / 16000000000000 : ℚ))
        (L := (227553573578023514173 / 2000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (2018031777949 / 16000000000000 : ℝ) ≤
      (-(4140932104806516067421 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2018031777949 / 16000000000000 : ℝ) = (2018031777949 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (2018031777949 / 2000000000000 : ℚ))
             (U := (17950976993483932579 / 2000000000000000000000 : ℚ))
             3 (by decide +kernel)) :
          Real.log (2018031777949 / 2000000000000 : ℝ) ≤
            (17950976993483932579 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau244 :
    Real.arctan (1735669799542907 / 5000000000000000 : ℝ) ≤
      (668238552174649568123 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1735669799542907 / 5000000000000000 : ℚ))
        (U := (668238552174649568123 / 2000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (668238552174649568123 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1735669799542907 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1735669799542907 : ℝ) =
              (1735669799542907 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau244)
  have hat2 :
    Real.arctan (750000000000000 / 3471339599085811 : ℝ) ≤
      (265980315177075916949 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 3471339599085811 : ℚ))
        (U := (265980315177075916949 / 1250000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1928031777949 / 16000000000000 : ℚ))
      (lo := (3471339599085811 / 10000000000000000 : ℚ))
      (hi := (1735669799542907 / 5000000000000000 : ℚ))
      (s := (3471339599085811 / 10000000000000000 : ℚ))
      (r₁ := (17928031777949 / 16000000000000 : ℚ))
      (r₂ := (2018031777949 / 16000000000000 : ℚ))
      (z₁ := (5000000000000000 / 1735669799542907 : ℚ))
      (z₂ := (750000000000000 / 3471339599085811 : ℚ))
      (L := (227553573578023514173 / 2000000000000000000000 : ℚ))
      (U := (-(4140932104806516067421 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_183 :
    ((115026691691253115783 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10297081645966272621029 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((139658659693411 / 400000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3359143938006206998433 / 10000000000000000000000 : ℝ)) -
              6 * (1057970113702477507409 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (121903382671 / 1000000000000 : ℝ) := by
  have hL1 :
    (115026691691253115783 / 1000000000000000000000 : ℝ) ≤
      Real.log (1121903382671 / 1000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1121903382671 / 1000000000000 : ℚ))
        (L := (115026691691253115783 / 1000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (127528382671 / 1000000000000 : ℝ) ≤
      (-(10297081645966272621029 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (127528382671 / 1000000000000 : ℝ) = (127528382671 / 125000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (127528382671 / 125000000000 : ℚ))
             (U := (100126058533727378971 / 5000000000000000000000 : ℚ))
             4 (by decide +kernel)) :
          Real.log (127528382671 / 125000000000 : ℝ) ≤
            (100126058533727378971 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau245 :
    Real.arctan (1745733246167639 / 5000000000000000 : ℝ) ≤
      (3359143938006206998433 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1745733246167639 / 5000000000000000 : ℚ))
        (U := (3359143938006206998433 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3359143938006206998433 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1745733246167639 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1745733246167639 : ℝ) =
              (1745733246167639 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau245)
  have hat2 :
    Real.arctan (30000000000000 / 139658659693411 : ℝ) ≤
      (1057970113702477507409 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (30000000000000 / 139658659693411 : ℚ))
        (U := (1057970113702477507409 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (121903382671 / 1000000000000 : ℚ))
      (lo := (139658659693411 / 400000000000000 : ℚ))
      (hi := (1745733246167639 / 5000000000000000 : ℚ))
      (s := (139658659693411 / 400000000000000 : ℚ))
      (r₁ := (1121903382671 / 1000000000000 : ℚ))
      (r₂ := (127528382671 / 1000000000000 : ℚ))
      (z₁ := (5000000000000000 / 1745733246167639 : ℚ))
      (z₂ := (30000000000000 / 139658659693411 : ℚ))
      (L := (115026691691253115783 / 1000000000000000000000 : ℚ))
      (U := (-(10297081645966272621029 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_184 :
    ((72671897675793028739 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10242436845908227152729 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((877869506319801 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1688484972162490177399 / 5000000000000000000000 : ℝ)) -
              6 * (263029436248314576797 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (1972876467523 / 16000000000000 : ℝ) := by
  have hL1 :
    (72671897675793028739 / 625000000000000000000 : ℝ) ≤
      Real.log (17972876467523 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (17972876467523 / 16000000000000 : ℚ))
        (L := (72671897675793028739 / 625000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (2062876467523 / 16000000000000 : ℝ) ≤
      (-(10242436845908227152729 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2062876467523 / 16000000000000 : ℝ) = (2062876467523 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (2062876467523 / 2000000000000 : ℚ))
             (U := (154770858591772847271 / 5000000000000000000000 : ℚ))
             4 (by decide +kernel)) :
          Real.log (2062876467523 / 2000000000000 : ℝ) ≤
            (154770858591772847271 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau246 :
    Real.arctan (3511478025279207 / 10000000000000000 : ℝ) ≤
      (1688484972162490177399 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3511478025279207 / 10000000000000000 : ℚ))
        (U := (1688484972162490177399 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1688484972162490177399 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3511478025279207 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3511478025279207 : ℝ) =
              (3511478025279207 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau246)
  have hat2 :
    Real.arctan (62500000000000 / 292623168773267 : ℝ) ≤
      (263029436248314576797 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (62500000000000 / 292623168773267 : ℚ))
        (U := (263029436248314576797 / 1250000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1972876467523 / 16000000000000 : ℚ))
      (lo := (877869506319801 / 2500000000000000 : ℚ))
      (hi := (3511478025279207 / 10000000000000000 : ℚ))
      (s := (877869506319801 / 2500000000000000 : ℚ))
      (r₁ := (17972876467523 / 16000000000000 : ℚ))
      (r₂ := (2062876467523 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3511478025279207 : ℚ))
      (z₂ := (62500000000000 / 292623168773267 : ℚ))
      (L := (72671897675793028739 / 625000000000000000000 : ℚ))
      (U := (-(10242436845908227152729 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_185 :
    ((293804561124544004693 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(101883828061061805467 / 50000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3531376159082673 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (424334104594847274703 / 1250000000000000000000 : ℝ)) -
              6 * (1046361451427109468381 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (199529881231 / 1600000000000 : ℝ) := by
  have hL1 :
    (293804561124544004693 / 2500000000000000000000 : ℝ) ≤
      Real.log (1799529881231 / 1600000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1799529881231 / 1600000000000 : ℚ))
        (L := (293804561124544004693 / 2500000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (208529881231 / 1600000000000 : ℝ) ≤
      (-(101883828061061805467 / 50000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (208529881231 / 1600000000000 : ℝ) = (208529881231 / 200000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (208529881231 / 200000000000 : ℚ))
             (U := (2088248983938194533 / 50000000000000000000 : ℚ))
             4 (by decide +kernel)) :
          Real.log (208529881231 / 200000000000 : ℝ) ≤
            (2088248983938194533 / 50000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau247 :
    Real.arctan (882844039770669 / 2500000000000000 : ℝ) ≤
      (424334104594847274703 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (882844039770669 / 2500000000000000 : ℚ))
        (U := (424334104594847274703 / 1250000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (424334104594847274703 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 882844039770669 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 882844039770669 : ℝ) =
              (882844039770669 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau247)
  have hat2 :
    Real.arctan (250000000000000 / 1177125386360891 : ℝ) ≤
      (1046361451427109468381 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1177125386360891 : ℚ))
        (U := (1046361451427109468381 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (199529881231 / 1600000000000 : ℚ))
      (lo := (3531376159082673 / 10000000000000000 : ℚ))
      (hi := (882844039770669 / 2500000000000000 : ℚ))
      (s := (3531376159082673 / 10000000000000000 : ℚ))
      (r₁ := (1799529881231 / 1600000000000 : ℚ))
      (r₂ := (208529881231 / 1600000000000 : ℚ))
      (z₁ := (2500000000000000 / 882844039770669 : ℚ))
      (z₂ := (250000000000000 / 1177125386360891 : ℚ))
      (L := (293804561124544004693 / 2500000000000000000000 : ℚ))
      (U := (-(101883828061061805467 / 50000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_186 :
    ((74229412545702061359 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(158357920152138572839 / 78125000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1775581399982569 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (106632956741550105427 / 312500000000000000000 : ℝ)) -
              6 * (2081397264622508967207 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2017721157097 / 16000000000000 : ℝ) := by
  have hL1 :
    (74229412545702061359 / 625000000000000000000 : ℝ) ≤
      Real.log (18017721157097 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (18017721157097 / 16000000000000 : ℚ))
        (L := (74229412545702061359 / 625000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (2107721157097 / 16000000000000 : ℝ) ≤
      (-(158357920152138572839 / 78125000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2107721157097 / 16000000000000 : ℝ) = (2107721157097 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (2107721157097 / 2000000000000 : ℚ))
             (U := (4098450230673927161 / 78125000000000000000 : ℚ))
             5 (by decide +kernel)) :
          Real.log (2107721157097 / 2000000000000 : ℝ) ≤
            (4098450230673927161 / 78125000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau248 :
    Real.arctan (3551162799965141 / 10000000000000000 : ℝ) ≤
      (106632956741550105427 / 312500000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3551162799965141 / 10000000000000000 : ℚ))
        (U := (106632956741550105427 / 312500000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (106632956741550105427 / 312500000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3551162799965141 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3551162799965141 : ℝ) =
              (3551162799965141 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau248)
  have hat2 :
    Real.arctan (375000000000000 / 1775581399982569 : ℝ) ≤
      (2081397264622508967207 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 1775581399982569 : ℚ))
        (U := (2081397264622508967207 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2017721157097 / 16000000000000 : ℚ))
      (lo := (1775581399982569 / 5000000000000000 : ℚ))
      (hi := (3551162799965141 / 10000000000000000 : ℚ))
      (s := (1775581399982569 / 5000000000000000 : ℚ))
      (r₁ := (18017721157097 / 16000000000000 : ℚ))
      (r₂ := (2107721157097 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3551162799965141 : ℚ))
      (z₂ := (375000000000000 / 1775581399982569 : ℚ))
      (L := (74229412545702061359 / 625000000000000000000 : ℚ))
      (U := (-(158357920152138572839 / 78125000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_187 :
    ((1200107470129474167961 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5040998430578654879721 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((446354975166469 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (342971722732483462099 / 1000000000000000000000 : ℝ)) -
              6 * (82810142757838897227 / 400000000000000000000 : ℝ)))) ≤
      Vfield (510035875471 / 4000000000000 : ℝ) := by
  have hL1 :
    (1200107470129474167961 / 10000000000000000000000 : ℝ) ≤
      Real.log (4510035875471 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (4510035875471 / 4000000000000 : ℚ))
        (L := (1200107470129474167961 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (532535875471 / 4000000000000 : ℝ) ≤
      (-(5040998430578654879721 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (532535875471 / 4000000000000 : ℝ) = (532535875471 / 500000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (532535875471 / 500000000000 : ℚ))
             (U := (157605421671345120279 / 2500000000000000000000 : ℚ))
             5 (by decide +kernel)) :
          Real.log (532535875471 / 500000000000 : ℝ) ≤
            (157605421671345120279 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau249 :
    Real.arctan (714167960266351 / 2000000000000000 : ℝ) ≤
      (342971722732483462099 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (714167960266351 / 2000000000000000 : ℚ))
        (U := (342971722732483462099 / 1000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (342971722732483462099 / 1000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 714167960266351 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 714167960266351 : ℝ) =
              (714167960266351 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau249)
  have hat2 :
    Real.arctan (93750000000000 / 446354975166469 : ℝ) ≤
      (82810142757838897227 / 400000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (93750000000000 / 446354975166469 : ℚ))
        (U := (82810142757838897227 / 400000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (510035875471 / 4000000000000 : ℚ))
      (lo := (446354975166469 / 1250000000000000 : ℚ))
      (hi := (714167960266351 / 2000000000000000 : ℚ))
      (s := (446354975166469 / 1250000000000000 : ℚ))
      (r₁ := (4510035875471 / 4000000000000 : ℚ))
      (r₂ := (532535875471 / 4000000000000 : ℚ))
      (z₁ := (2000000000000000 / 714167960266351 : ℚ))
      (z₂ := (93750000000000 / 446354975166469 : ℚ))
      (L := (1200107470129474167961 / 10000000000000000000000 : ℚ))
      (U := (-(5040998430578654879721 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_188 :
    ((612467451086576923913 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(9977827430743743884387 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((360987204712473 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1732146236679985576439 / 5000000000000000000000 : ℝ)) -
              6 * (128030806236496645127 / 625000000000000000000 : ℝ)))) ≤
      Vfield (1042494095729 / 8000000000000 : ℝ) := by
  have hL1 :
    (612467451086576923913 / 5000000000000000000000 : ℝ) ≤
      Real.log (9042494095729 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (9042494095729 / 8000000000000 : ℚ))
        (L := (612467451086576923913 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (1087494095729 / 8000000000000 : ℝ) ≤
      (-(9977827430743743884387 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1087494095729 / 8000000000000 : ℝ) = (1087494095729 / 1000000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (1087494095729 / 1000000000000 : ℚ))
             (U := (419380273756256115613 / 5000000000000000000000 : ℚ))
             5 (by decide +kernel)) :
          Real.log (1087494095729 / 1000000000000 : ℝ) ≤
            (419380273756256115613 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau250 :
    Real.arctan (3609872047124733 / 10000000000000000 : ℝ) ≤
      (1732146236679985576439 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3609872047124733 / 10000000000000000 : ℚ))
        (U := (1732146236679985576439 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1732146236679985576439 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3609872047124733 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3609872047124733 : ℝ) =
              (3609872047124733 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau250)
  have hat2 :
    Real.arctan (25000000000000 / 120329068237491 : ℝ) ≤
      (128030806236496645127 / 625000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (25000000000000 / 120329068237491 : ℚ))
        (U := (128030806236496645127 / 625000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1042494095729 / 8000000000000 : ℚ))
      (lo := (360987204712473 / 1000000000000000 : ℚ))
      (hi := (3609872047124733 / 10000000000000000 : ℚ))
      (s := (360987204712473 / 1000000000000000 : ℚ))
      (r₁ := (9042494095729 / 8000000000000 : ℚ))
      (r₂ := (1087494095729 / 8000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3609872047124733 : ℚ))
      (z₂ := (25000000000000 / 120329068237491 : ℚ))
      (L := (612467451086576923913 / 5000000000000000000000 : ℚ))
      (U := (-(9977827430743743884387 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_189 :
    ((24994016934096835669 / 200000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(19751568072237638037033 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((145939469679453 / 400000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1749206566456722486477 / 5000000000000000000000 : ℝ)) -
              6 * (1013702202475916540091 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (266229110129 / 2000000000000 : ℝ) := by
  have hL1 :
    (24994016934096835669 / 200000000000000000000 : ℝ) ≤
      Real.log (2266229110129 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2266229110129 / 2000000000000 : ℚ))
        (L := (24994016934096835669 / 200000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (277479110129 / 2000000000000 : ℝ) ≤
      (-(19751568072237638037033 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (277479110129 / 2000000000000 : ℝ) = (277479110129 / 250000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (277479110129 / 250000000000 : ℚ))
             (U := (1042847336762361962967 / 10000000000000000000000 : ℚ))
             6 (by decide +kernel)) :
          Real.log (277479110129 / 250000000000 : ℝ) ≤
            (1042847336762361962967 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau251 :
    Real.arctan (456060842748291 / 1250000000000000 : ℝ) ≤
      (1749206566456722486477 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (456060842748291 / 1250000000000000 : ℚ))
        (U := (1749206566456722486477 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1749206566456722486477 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 456060842748291 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 456060842748291 : ℝ) =
              (456060842748291 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau251)
  have hat2 :
    Real.arctan (10000000000000 / 48646489893151 : ℝ) ≤
      (1013702202475916540091 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (10000000000000 / 48646489893151 : ℚ))
        (U := (1013702202475916540091 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (266229110129 / 2000000000000 : ℚ))
      (lo := (145939469679453 / 400000000000000 : ℚ))
      (hi := (456060842748291 / 1250000000000000 : ℚ))
      (s := (145939469679453 / 400000000000000 : ℚ))
      (r₁ := (2266229110129 / 2000000000000 : ℚ))
      (r₂ := (277479110129 / 2000000000000 : ℚ))
      (z₁ := (1250000000000000 / 456060842748291 : ℚ))
      (z₂ := (10000000000000 / 48646489893151 : ℚ))
      (L := (24994016934096835669 / 200000000000000000000 : ℚ))
      (U := (-(19751568072237638037033 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_190 :
    ((259809897242961142701 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1935548032090052720183 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((465564410925817 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3565345242591427109191 / 10000000000000000000000 : ℝ)) -
              6 * (397422127297066665873 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (110976113009 / 800000000000 : ℝ) := by
  have hL1 :
    (259809897242961142701 / 2000000000000000000000 : ℝ) ≤
      Real.log (910976113009 / 800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (910976113009 / 800000000000 : ℚ))
        (L := (259809897242961142701 / 2000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (115476113009 / 800000000000 : ℝ) ≤
      (-(1935548032090052720183 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (115476113009 / 800000000000 : ℝ) = (115476113009 / 100000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (115476113009 / 100000000000 : ℚ))
             (U := (143893508809947279817 / 1000000000000000000000 : ℚ))
             6 (by decide +kernel)) :
          Real.log (115476113009 / 100000000000 : ℝ) ≤
            (143893508809947279817 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau252 :
    Real.arctan (3724515287406539 / 10000000000000000 : ℝ) ≤
      (3565345242591427109191 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3724515287406539 / 10000000000000000 : ℚ))
        (U := (3565345242591427109191 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3565345242591427109191 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3724515287406539 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3724515287406539 : ℝ) =
              (3724515287406539 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau252)
  have hat2 :
    Real.arctan (93750000000000 / 465564410925817 : ℝ) ≤
      (397422127297066665873 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (93750000000000 / 465564410925817 : ℚ))
        (U := (397422127297066665873 / 2000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (110976113009 / 800000000000 : ℚ))
      (lo := (465564410925817 / 1250000000000000 : ℚ))
      (hi := (3724515287406539 / 10000000000000000 : ℚ))
      (s := (465564410925817 / 1250000000000000 : ℚ))
      (r₁ := (910976113009 / 800000000000 : ℚ))
      (r₂ := (115476113009 / 800000000000 : ℚ))
      (z₁ := (10000000000000000 / 3724515287406539 : ℚ))
      (z₂ := (93750000000000 / 465564410925817 : ℚ))
      (L := (259809897242961142701 / 2000000000000000000000 : ℚ))
      (U := (-(1935548032090052720183 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_191 :
    ((13481557922957465779 / 100000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4743621304204845889853 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3799022604012773 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3630616003248135794793 / 10000000000000000000000 : ℝ)) -
              6 * (1949127934440516860467 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (72162863729 / 500000000000 : ℝ) := by
  have hL1 :
    (13481557922957465779 / 100000000000000000000 : ℝ) ≤
      Real.log (572162863729 / 500000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (572162863729 / 500000000000 : ℚ))
        (L := (13481557922957465779 / 100000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (74975363729 / 500000000000 : ℝ) ≤
      (-(4743621304204845889853 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (74975363729 / 500000000000 : ℝ) = (74975363729 / 62500000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (74975363729 / 62500000000 : ℚ))
             (U := (454982548045154110147 / 2500000000000000000000 : ℚ))
             7 (by decide +kernel)) :
          Real.log (74975363729 / 62500000000 : ℝ) ≤
            (454982548045154110147 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau253 :
    Real.arctan (474877825501597 / 1250000000000000 : ℝ) ≤
      (3630616003248135794793 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (474877825501597 / 1250000000000000 : ℚ))
        (U := (3630616003248135794793 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3630616003248135794793 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 474877825501597 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 474877825501597 : ℝ) =
              (474877825501597 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau253)
  have hat2 :
    Real.arctan (750000000000000 / 3799022604012773 : ℝ) ≤
      (1949127934440516860467 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 3799022604012773 : ℚ))
        (U := (1949127934440516860467 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (72162863729 / 500000000000 : ℚ))
      (lo := (3799022604012773 / 10000000000000000 : ℚ))
      (hi := (474877825501597 / 1250000000000000 : ℚ))
      (s := (3799022604012773 / 10000000000000000 : ℚ))
      (r₁ := (572162863729 / 500000000000 : ℚ))
      (r₂ := (74975363729 / 500000000000 : ℚ))
      (z₁ := (1250000000000000 / 474877825501597 : ℚ))
      (z₂ := (750000000000000 / 3799022604012773 : ℚ))
      (L := (13481557922957465779 / 100000000000000000000 : ℚ))
      (U := (-(4743621304204845889853 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_192 :
    ((1363649648793105799231 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18856849239285061292259 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1911152162703291 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1825472812071868163633 / 5000000000000000000000 : ℝ)) -
              6 * (968775768368206191403 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (4675203313927 / 32000000000000 : ℝ) := by
  have hL1 :
    (1363649648793105799231 / 10000000000000000000000 : ℝ) ≤
      Real.log (36675203313927 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (36675203313927 / 32000000000000 : ℚ))
        (L := (1363649648793105799231 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (4855203313927 / 32000000000000 : ℝ) ≤
      (-(18856849239285061292259 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (4855203313927 / 32000000000000 : ℝ) = (4855203313927 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (4855203313927 / 4000000000000 : ℚ))
             (U := (1937566169714938707741 / 10000000000000000000000 : ℚ))
             7 (by decide +kernel)) :
          Real.log (4855203313927 / 4000000000000 : ℝ) ≤
            (1937566169714938707741 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau254 :
    Real.arctan (764460865081317 / 2000000000000000 : ℝ) ≤
      (1825472812071868163633 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (764460865081317 / 2000000000000000 : ℚ))
        (U := (1825472812071868163633 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1825472812071868163633 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 764460865081317 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 764460865081317 : ℝ) =
              (764460865081317 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau254)
  have hat2 :
    Real.arctan (125000000000000 / 637050720901097 : ℝ) ≤
      (968775768368206191403 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (125000000000000 / 637050720901097 : ℚ))
        (U := (968775768368206191403 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4675203313927 / 32000000000000 : ℚ))
      (lo := (1911152162703291 / 5000000000000000 : ℚ))
      (hi := (764460865081317 / 2000000000000000 : ℚ))
      (s := (1911152162703291 / 5000000000000000 : ℚ))
      (r₁ := (36675203313927 / 32000000000000 : ℚ))
      (r₂ := (4855203313927 / 32000000000000 : ℚ))
      (z₁ := (2000000000000000 / 764460865081317 : ℚ))
      (z₂ := (125000000000000 / 637050720901097 : ℚ))
      (L := (1363649648793105799231 / 10000000000000000000000 : ℚ))
      (U := (-(18856849239285061292259 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
