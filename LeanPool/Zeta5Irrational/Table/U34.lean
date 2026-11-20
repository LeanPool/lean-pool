/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U34) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_412_1 :
    Uω (aρ 1) (bρ 1) (441401103427 / 1000000000000 : ℝ) ≤
      (-(8325295657190344060219 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8698953293364661 / 20000000000000000 : ℝ) ≤
      (-(8325295657190344060219 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8698953293364661 / 20000000000000000 : ℚ))
        (r' := (8698953293364661 / 5000000000000000 : ℚ))
        (U := (-(8325295657190344060219 / 10000000000000000000000 : ℚ)))
        (U' := (5537647948809655939781 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (441401103427 / 1000000000000 : ℚ))
      (s := (4349439477179661 / 10000000000000000 : ℚ))
      (q := (8698953293364661 / 20000000000000000 : ℚ))
      (U := (-(8325295657190344060219 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_412_2 :
    Uω (aρ 2) (bρ 2) (441401103427 / 1000000000000 : ℝ) ≤
      (-(335222984107915235267 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4325499530969083 / 10000000000000000 : ℝ) ≤
      (-(335222984107915235267 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4325499530969083 / 10000000000000000 : ℚ))
        (r' := (4325499530969083 / 2500000000000000 : ℚ))
        (U := (-(335222984107915235267 / 400000000000000000000 : ℚ)))
        (U' := (219294760132084764733 / 400000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (441401103427 / 1000000000000 : ℚ))
      (s := (2162627129131583 / 5000000000000000 : ℚ))
      (q := (4325499530969083 / 10000000000000000 : ℚ))
      (U := (-(335222984107915235267 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_412_3 :
    Uω (aρ 3) (bρ 3) (441401103427 / 1000000000000 : ℝ) ≤
      (-(8492201232119775677881 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8554967854459393 / 20000000000000000 : ℝ) ≤
      (-(8492201232119775677881 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8554967854459393 / 20000000000000000 : ℚ))
        (r' := (8554967854459393 / 5000000000000000 : ℚ))
        (U := (-(8492201232119775677881 / 10000000000000000000000 : ℚ)))
        (U' := (5370742373880224322119 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (441401103427 / 1000000000000 : ℚ))
      (s := (4276619157134393 / 10000000000000000 : ℚ))
      (q := (8554967854459393 / 20000000000000000 : ℚ))
      (U := (-(8492201232119775677881 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_412_4 :
    Uω (aρ 4) (bρ 4) (441401103427 / 1000000000000 : ℝ) ≤
      (-(4340422539223208551097 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2098774082580749 / 5000000000000000 : ℝ) ≤
      (-(4340422539223208551097 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2098774082580749 / 5000000000000000 : ℚ))
        (r' := (2098774082580749 / 1250000000000000 : ℚ))
        (U := (-(4340422539223208551097 / 5000000000000000000000 : ℚ)))
        (U' := (2591049263776791448903 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (441401103427 / 1000000000000 : ℚ))
      (s := (1048760453515749 / 2500000000000000 : ℚ))
      (q := (2098774082580749 / 5000000000000000 : ℚ))
      (U := (-(4340422539223208551097 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_412_5 :
    Uω (aρ 5) (bρ 5) (441401103427 / 1000000000000 : ℝ) ≤
      (-(4488166174250952639887 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (407533054044943 / 1000000000000000 : ℝ) ≤
      (-(4488166174250952639887 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (407533054044943 / 1000000000000000 : ℚ))
        (r' := (407533054044943 / 250000000000000 : ℚ))
        (U := (-(4488166174250952639887 / 5000000000000000000000 : ℚ)))
        (U' := (2443305628749047360113 / 5000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (441401103427 / 1000000000000 : ℚ))
      (s := (203439824198693 / 500000000000000 : ℚ))
      (q := (407533054044943 / 1000000000000000 : ℚ))
      (U := (-(4488166174250952639887 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_412_6 :
    Uω (aρ 6) (bρ 6) (441401103427 / 1000000000000 : ℝ) ≤
      (-(470947097206575796623 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3898886104311623 / 10000000000000000 : ℝ) ≤
      (-(470947097206575796623 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3898886104311623 / 10000000000000000 : ℚ))
        (r' := (3898886104311623 / 2500000000000000 : ℚ))
        (U := (-(470947097206575796623 / 500000000000000000000 : ℚ)))
        (U' := (222200083093424203377 / 500000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (441401103427 / 1000000000000 : ℚ))
      (s := (1941573993419123 / 5000000000000000 : ℚ))
      (q := (3898886104311623 / 10000000000000000 : ℚ))
      (U := (-(470947097206575796623 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_412_7 :
    Uω (aρ 7) (bρ 7) (441401103427 / 1000000000000 : ℝ) ≤
      (-(10063552978277690335471 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (45693608893127 / 125000000000000 : ℝ) ≤
      (-(10063552978277690335471 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (45693608893127 / 125000000000000 : ℚ))
        (r' := (45693608893127 / 31250000000000 : ℚ))
        (U := (-(10063552978277690335471 / 10000000000000000000000 : ℚ)))
        (U' := (3799390627722309664529 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (441401103427 / 1000000000000 : ℚ))
      (s := (90500364546883 / 250000000000000 : ℚ))
      (q := (45693608893127 / 125000000000000 : ℚ))
      (U := (-(10063552978277690335471 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_412_8 :
    Uω (aρ 8) (bρ 8) (441401103427 / 1000000000000 : ℝ) ≤
      (-(274774647827680332549 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3331712716879051 / 10000000000000000 : ℝ) ≤
      (-(274774647827680332549 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3331712716879051 / 10000000000000000 : ℚ))
        (r' := (3331712716879051 / 2500000000000000 : ℚ))
        (U := (-(274774647827680332549 / 250000000000000000000 : ℚ)))
        (U' := (71798942322319667451 / 250000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (441401103427 / 1000000000000 : ℚ))
      (s := (1628002122036551 / 5000000000000000 : ℚ))
      (q := (3331712716879051 / 10000000000000000 : ℚ))
      (U := (-(274774647827680332549 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_412_9 :
    Uω (aρ 9) (bρ 9) (441401103427 / 1000000000000 : ℝ) ≤
      (-(1234130017850107135807 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5821757867243393 / 20000000000000000 : ℝ) ≤
      (-(1234130017850107135807 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5821757867243393 / 20000000000000000 : ℚ))
        (r' := (5821757867243393 / 5000000000000000 : ℚ))
        (U := (-(1234130017850107135807 / 1000000000000000000000 : ℚ)))
        (U' := (152164342749892864193 / 1000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (441401103427 / 1000000000000 : ℚ))
      (s := (2755302305918393 / 10000000000000000 : ℚ))
      (q := (5821757867243393 / 20000000000000000 : ℚ))
      (U := (-(1234130017850107135807 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_412_10 :
    Uω (aρ 10) (bρ 10) (441401103427 / 1000000000000 : ℝ) ≤
      (-(14443658687485022068619 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2358956177358807 / 10000000000000000 : ℝ) ≤
      (-(14443658687485022068619 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2358956177358807 / 10000000000000000 : ℚ))
        (r' := (2358956177358807 / 1250000000000000 : ℚ))
        (U := (-(14443658687485022068619 / 10000000000000000000000 : ℚ)))
        (U' := (6350756721514977931381 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (441401103427 / 1000000000000 : ℚ))
      (s := (1020007913443807 / 5000000000000000 : ℚ))
      (q := (2358956177358807 / 10000000000000000 : ℚ))
      (U := (-(14443658687485022068619 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_412_11 :
    Uω (aρ 11) (bρ 11) (441401103427 / 1000000000000 : ℝ) ≤
      (-(19162436512716292548947 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (735793522556029 / 5000000000000000 : ℝ) ≤
      (-(19162436512716292548947 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (735793522556029 / 5000000000000000 : ℚ))
        (r' := (735793522556029 / 625000000000000 : ℚ))
        (U := (-(19162436512716292548947 / 10000000000000000000000 : ℚ)))
        (U' := (1631978896283707451053 / 10000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (441401103427 / 1000000000000 : ℚ))
      (s := (170938547149779 / 2500000000000000 : ℚ))
      (q := (735793522556029 / 5000000000000000 : ℚ))
      (U := (-(19162436512716292548947 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_412_12 :
    Uω (aρ 12) (bρ 12) (441401103427 / 1000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_412_13 :
    Uω (aρ 13) (bρ 13) (441401103427 / 1000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_412_14 :
    Uω (aρ 14) (bρ 14) (441401103427 / 1000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_412_15 :
    Uω (aρ 15) (bρ 15) (441401103427 / 1000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_412_16 :
    Uω (aρ 16) (bρ 16) (441401103427 / 1000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_412 :
    Uρ (441401103427 / 1000000000000 : ℝ) ≤
      (-(6106371938425516455039 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_412_1 U_412_2 U_412_3 U_412_4 U_412_5 U_412_6 U_412_7 U_412_8 U_412_9 U_412_10
    U_412_11 U_412_12 U_412_13 U_412_14 U_412_15 U_412_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_413_1 :
    Uω (aρ 1) (bρ 1) (885450806607 / 2000000000000 : ℝ) ≤
      (-(829489431824442098373 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8725439516552003 / 20000000000000000 : ℝ) ≤
      (-(829489431824442098373 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8725439516552003 / 20000000000000000 : ℚ))
        (r' := (8725439516552003 / 5000000000000000 : ℚ))
        (U := (-(829489431824442098373 / 1000000000000000000000 : ℚ)))
        (U' := (556804928775557901627 / 1000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (885450806607 / 2000000000000 : ℚ))
      (s := (4362682701602003 / 10000000000000000 : ℚ))
      (q := (8725439516552003 / 20000000000000000 : ℚ))
      (U := (-(829489431824442098373 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_413_2 :
    Uω (aρ 2) (bρ 2) (885450806607 / 2000000000000 : ℝ) ≤
      (-(417500176740119125927 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1735497311365583 / 4000000000000000 : ℝ) ≤
      (-(417500176740119125927 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1735497311365583 / 4000000000000000 : ℚ))
        (r' := (1735497311365583 / 1000000000000000 : ℚ))
        (U := (-(417500176740119125927 / 500000000000000000000 : ℚ)))
        (U' := (275647003559880874073 / 500000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (885450806607 / 2000000000000 : ℚ))
      (s := (867699750877583 / 2000000000000000 : ℚ))
      (q := (1735497311365583 / 4000000000000000 : ℚ))
      (U := (-(417500176740119125927 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_413_3 :
    Uω (aρ 3) (bρ 3) (885450806607 / 2000000000000 : ℝ) ≤
      (-(1692256610190248951243 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8581459191154971 / 20000000000000000 : ℝ) ≤
      (-(1692256610190248951243 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8581459191154971 / 20000000000000000 : ℚ))
        (r' := (8581459191154971 / 5000000000000000 : ℚ))
        (U := (-(1692256610190248951243 / 2000000000000000000000 : ℚ)))
        (U' := (1080332111009751048757 / 2000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (885450806607 / 2000000000000 : ℚ))
      (s := (4289867495064971 / 10000000000000000 : ℚ))
      (q := (8581459191154971 / 20000000000000000 : ℚ))
      (U := (-(1692256610190248951243 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_413_4 :
    Uω (aρ 4) (bρ 4) (885450806607 / 2000000000000 : ℝ) ≤
      (-(1729865328848618984599 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4210799051116593 / 10000000000000000 : ℝ) ≤
      (-(1729865328848618984599 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4210799051116593 / 10000000000000000 : ℚ))
        (r' := (4210799051116593 / 2500000000000000 : ℚ))
        (U := (-(1729865328848618984599 / 2000000000000000000000 : ℚ)))
        (U' := (1042723392351381015401 / 2000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (885450806607 / 2000000000000 : ℚ))
      (s := (2104150293604093 / 5000000000000000 : ℚ))
      (q := (4210799051116593 / 10000000000000000 : ℚ))
      (U := (-(1729865328848618984599 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_413_5 :
    Uω (aρ 5) (bρ 5) (885450806607 / 2000000000000 : ℝ) ≤
      (-(8943837665525954089233 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8177189473928883 / 20000000000000000 : ℝ) ≤
      (-(8943837665525954089233 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8177189473928883 / 20000000000000000 : ℚ))
        (r' := (8177189473928883 / 5000000000000000 : ℚ))
        (U := (-(8943837665525954089233 / 10000000000000000000000 : ℚ)))
        (U' := (4919105940474045910767 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (885450806607 / 2000000000000 : ℚ))
      (s := (4082081878238883 / 10000000000000000 : ℚ))
      (q := (8177189473928883 / 20000000000000000 : ℚ))
      (U := (-(8943837665525954089233 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_413_6 :
    Uω (aρ 6) (bρ 6) (885450806607 / 2000000000000 : ℝ) ≤
      (-(9384896663309727471479 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (782436518566833 / 2000000000000000 : ℝ) ≤
      (-(9384896663309727471479 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (782436518566833 / 2000000000000000 : ℚ))
        (r' := (782436518566833 / 500000000000000 : ℚ))
        (U := (-(9384896663309727471479 / 10000000000000000000000 : ℚ)))
        (U' := (4478046942690272528521 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (885450806607 / 2000000000000 : ℚ))
      (s := (389649796511833 / 1000000000000000 : ℚ))
      (q := (782436518566833 / 2000000000000000 : ℚ))
      (U := (-(9384896663309727471479 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_413_7 :
    Uω (aρ 7) (bρ 7) (885450806607 / 2000000000000 : ℝ) ≤
      (-(10027038309970569596151 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1834430503309113 / 5000000000000000 : ℝ) ≤
      (-(10027038309970569596151 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1834430503309113 / 5000000000000000 : ℚ))
        (r' := (1834430503309113 / 1250000000000000 : ℚ))
        (U := (-(10027038309970569596151 / 10000000000000000000000 : ℚ)))
        (U' := (3835905296029430403849 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (885450806607 / 2000000000000 : ℚ))
      (s := (908379043361613 / 2500000000000000 : ℚ))
      (q := (1834430503309113 / 5000000000000000 : ℚ))
      (U := (-(10027038309970569596151 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_413_8 :
    Uω (aρ 8) (bρ 8) (885450806607 / 2000000000000 : ℝ) ≤
      (-(10950399669358784600239 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3345262365188567 / 10000000000000000 : ℝ) ≤
      (-(10950399669358784600239 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3345262365188567 / 10000000000000000 : ℚ))
        (r' := (3345262365188567 / 2500000000000000 : ℚ))
        (U := (-(10950399669358784600239 / 10000000000000000000000 : ℚ)))
        (U' := (2912543936641215399761 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (885450806607 / 2000000000000 : ℚ))
      (s := (1634930270963567 / 5000000000000000 : ℚ))
      (q := (3345262365188567 / 10000000000000000 : ℚ))
      (U := (-(10950399669358784600239 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_413_9 :
    Uω (aρ 9) (bρ 9) (885450806607 / 2000000000000 : ℝ) ≤
      (-(6146682270563129851507 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5849731828561447 / 20000000000000000 : ℝ) ≤
      (-(6146682270563129851507 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5849731828561447 / 20000000000000000 : ℚ))
        (r' := (5849731828561447 / 5000000000000000 : ℚ))
        (U := (-(6146682270563129851507 / 5000000000000000000000 : ℚ)))
        (U' := (784789532436870148493 / 5000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (885450806607 / 2000000000000 : ℚ))
      (s := (2770033268471447 / 10000000000000000 : ℚ))
      (q := (5849731828561447 / 20000000000000000 : ℚ))
      (U := (-(6146682270563129851507 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_413_10 :
    Uω (aρ 10) (bρ 10) (885450806607 / 2000000000000 : ℝ) ≤
      (-(3594754308831076809627 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4748508407420689 / 20000000000000000 : ℝ) ≤
      (-(3594754308831076809627 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4748508407420689 / 20000000000000000 : ℚ))
        (r' := (4748508407420689 / 2500000000000000 : ℚ))
        (U := (-(3594754308831076809627 / 2500000000000000000000 : ℚ)))
        (U' := (1603849543418923190373 / 2500000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (885450806607 / 2000000000000 : ℚ))
      (s := (2057368880825689 / 10000000000000000 : ℚ))
      (q := (4748508407420689 / 20000000000000000 : ℚ))
      (U := (-(3594754308831076809627 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_413_11 :
    Uω (aρ 11) (bρ 11) (885450806607 / 2000000000000 : ℝ) ≤
      (-(18974596681744203262247 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2998981120853179 / 20000000000000000 : ℝ) ≤
      (-(18974596681744203262247 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2998981120853179 / 20000000000000000 : ℚ))
        (r' := (2998981120853179 / 2500000000000000 : ℚ))
        (U := (-(18974596681744203262247 / 10000000000000000000000 : ℚ)))
        (U' := (1819818727255796737753 / 10000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (885450806607 / 2000000000000 : ℚ))
      (s := (726318220463179 / 10000000000000000 : ℚ))
      (q := (2998981120853179 / 20000000000000000 : ℚ))
      (U := (-(18974596681744203262247 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_413_12 :
    Uω (aρ 12) (bρ 12) (885450806607 / 2000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_413_13 :
    Uω (aρ 13) (bρ 13) (885450806607 / 2000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_413_14 :
    Uω (aρ 14) (bρ 14) (885450806607 / 2000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_413_15 :
    Uω (aρ 15) (bρ 15) (885450806607 / 2000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_413_16 :
    Uω (aρ 16) (bρ 16) (885450806607 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_413 :
    Uρ (885450806607 / 2000000000000 : ℝ) ≤
      (-(1217216813364887052379 / 1000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_413_1 U_413_2 U_413_3 U_413_4 U_413_5 U_413_6 U_413_7 U_413_8 U_413_9 U_413_10
    U_413_11 U_413_12 U_413_13 U_413_14 U_413_15 U_413_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_414_1 :
    Uω (aρ 1) (bρ 1) (22202485159 / 50000000000 : ℝ) ≤
      (-(8264585124940494284273 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1750385147674701 / 4000000000000000 : ℝ) ≤
      (-(8264585124940494284273 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1750385147674701 / 4000000000000000 : ℚ))
        (r' := (1750385147674701 / 1000000000000000 : ℚ))
        (U := (-(8264585124940494284273 / 10000000000000000000000 : ℚ)))
        (U' := (5598358481059505715727 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (22202485159 / 50000000000 : ℚ))
      (s := (875185184931701 / 2000000000000000 : ℚ))
      (q := (1750385147674701 / 4000000000000000 : ℚ))
      (U := (-(8264585124940494284273 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_414_2 :
    Uω (aρ 2) (bρ 2) (22202485159 / 50000000000 : ℝ) ≤
      (-(8319525651625783148213 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4351987021301887 / 10000000000000000 : ℝ) ≤
      (-(8319525651625783148213 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4351987021301887 / 10000000000000000 : ℚ))
        (r' := (4351987021301887 / 2500000000000000 : ℚ))
        (U := (-(8319525651625783148213 / 10000000000000000000000 : ℚ)))
        (U' := (5543417954374216851787 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (22202485159 / 50000000000 : ℚ))
      (s := (2175871620699387 / 5000000000000000 : ℚ))
      (q := (4351987021301887 / 10000000000000000 : ℚ))
      (U := (-(8319525651625783148213 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_414_3 :
    Uω (aρ 3) (bρ 3) (22202485159 / 50000000000 : ℝ) ≤
      (-(4215230103394798454407 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8607950494980963 / 20000000000000000 : ℝ) ≤
      (-(4215230103394798454407 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8607950494980963 / 20000000000000000 : ℚ))
        (r' := (8607950494980963 / 5000000000000000 : ℚ))
        (U := (-(4215230103394798454407 / 5000000000000000000000 : ℚ)))
        (U' := (2716241699605201545593 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (22202485159 / 50000000000 : ℚ))
      (s := (4303115800125963 / 10000000000000000 : ℚ))
      (q := (8607950494980963 / 20000000000000000 : ℚ))
      (U := (-(4215230103394798454407 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_414_4 :
    Uω (aρ 4) (bρ 4) (22202485159 / 50000000000 : ℝ) ≤
      (-(8617907356384918787213 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4224049887558109 / 10000000000000000 : ℝ) ≤
      (-(8617907356384918787213 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4224049887558109 / 10000000000000000 : ℚ))
        (r' := (4224049887558109 / 2500000000000000 : ℚ))
        (U := (-(8617907356384918787213 / 10000000000000000000000 : ℚ)))
        (U' := (5245036249615081212787 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (22202485159 / 50000000000 : ℚ))
      (s := (2110779630663109 / 5000000000000000 : ℚ))
      (q := (4224049887558109 / 10000000000000000 : ℚ))
      (U := (-(8617907356384918787213 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_414_5 :
    Uω (aρ 5) (bρ 5) (22202485159 / 50000000000 : ℝ) ≤
      (-(8911448565837778337919 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (82037175923353 / 200000000000000 : ℝ) ≤
      (-(8911448565837778337919 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (82037175923353 / 200000000000000 : ℚ))
        (r' := (82037175923353 / 50000000000000 : ℚ))
        (U := (-(8911448565837778337919 / 10000000000000000000000 : ℚ)))
        (U' := (4951495040162221662081 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (22202485159 / 50000000000 : ℚ))
      (s := (40953669978803 / 100000000000000 : ℚ))
      (q := (82037175923353 / 200000000000000 : ℚ))
      (U := (-(8911448565837778337919 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_414_6 :
    Uω (aρ 6) (bρ 6) (22202485159 / 50000000000 : ℝ) ≤
      (-(9350967824237916076221 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7850957435088173 / 20000000000000000 : ℝ) ≤
      (-(9350967824237916076221 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7850957435088173 / 20000000000000000 : ℚ))
        (r' := (7850957435088173 / 5000000000000000 : ℚ))
        (U := (-(9350967824237916076221 / 10000000000000000000000 : ℚ)))
        (U' := (4511975781762083923779 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (22202485159 / 50000000000 : ℚ))
      (s := (3909847215773173 / 10000000000000000 : ℚ))
      (q := (7850957435088173 / 20000000000000000 : ℚ))
      (U := (-(9350967824237916076221 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_414_7 :
    Uω (aρ 7) (bρ 7) (22202485159 / 50000000000 : ℝ) ≤
      (-(4995329531900420707149 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1472892941447899 / 4000000000000000 : ℝ) ≤
      (-(4995329531900420707149 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1472892941447899 / 4000000000000000 : ℚ))
        (r' := (1472892941447899 / 1000000000000000 : ℚ))
        (U := (-(4995329531900420707149 / 5000000000000000000000 : ℚ)))
        (U' := (1936142271099579292851 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (22202485159 / 50000000000 : ℚ))
      (s := (729403173736899 / 2000000000000000 : ℚ))
      (q := (1472892941447899 / 4000000000000000 : ℚ))
      (U := (-(4995329531900420707149 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_414_8 :
    Uω (aρ 8) (bρ 8) (22202485159 / 50000000000 : ℝ) ≤
      (-(10909985018713567947419 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3358809482831227 / 10000000000000000 : ℝ) ≤
      (-(10909985018713567947419 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3358809482831227 / 10000000000000000 : ℚ))
        (r' := (3358809482831227 / 2500000000000000 : ℚ))
        (U := (-(10909985018713567947419 / 10000000000000000000000 : ℚ)))
        (U' := (2952958587286432052581 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (22202485159 / 50000000000 : ℚ))
      (s := (1641855889223727 / 5000000000000000 : ℚ))
      (q := (3358809482831227 / 10000000000000000 : ℚ))
      (U := (-(10909985018713567947419 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_414_9 :
    Uω (aρ 9) (bρ 9) (22202485159 / 50000000000 : ℝ) ≤
      (-(191338797200200775319 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5877690842706347 / 20000000000000000 : ℝ) ≤
      (-(191338797200200775319 / 156250000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5877690842706347 / 20000000000000000 : ℚ))
        (r' := (5877690842706347 / 5000000000000000 : ℚ))
        (U := (-(191338797200200775319 / 156250000000000000000 : ℚ)))
        (U' := (25269696643549224681 / 156250000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (22202485159 / 50000000000 : ℚ))
      (s := (2784749283851347 / 10000000000000000 : ℚ))
      (q := (5877690842706347 / 20000000000000000 : ℚ))
      (U := (-(191338797200200775319 / 156250000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_414_10 :
    Uω (aρ 10) (bρ 10) (22202485159 / 50000000000 : ℝ) ≤
      (-(286298355615774617203 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2389521924000261 / 10000000000000000 : ℝ) ≤
      (-(286298355615774617203 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2389521924000261 / 10000000000000000 : ℚ))
        (r' := (2389521924000261 / 1250000000000000 : ℚ))
        (U := (-(286298355615774617203 / 200000000000000000000 : ℚ)))
        (U' := (129589952564225382797 / 200000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (22202485159 / 50000000000 : ℚ))
      (s := (1037330661320261 / 5000000000000000 : ℚ))
      (q := (2389521924000261 / 10000000000000000 : ℚ))
      (U := (-(286298355615774617203 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_414_11 :
    Uω (aρ 11) (bρ 11) (22202485159 / 50000000000 : ℝ) ≤
      (-(3759439815845592521937 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3052657018071263 / 20000000000000000 : ℝ) ≤
      (-(3759439815845592521937 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3052657018071263 / 20000000000000000 : ℚ))
        (r' := (3052657018071263 / 2500000000000000 : ℚ))
        (U := (-(3759439815845592521937 / 2000000000000000000000 : ℚ)))
        (U' := (399443265954407478063 / 2000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (22202485159 / 50000000000 : ℚ))
      (s := (766751118916263 / 10000000000000000 : ℚ))
      (q := (3052657018071263 / 20000000000000000 : ℚ))
      (U := (-(3759439815845592521937 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_414_12 :
    Uω (aρ 12) (bρ 12) (22202485159 / 50000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_414_13 :
    Uω (aρ 13) (bρ 13) (22202485159 / 50000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_414_14 :
    Uω (aρ 14) (bρ 14) (22202485159 / 50000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_414_15 :
    Uω (aρ 15) (bρ 15) (22202485159 / 50000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_414_16 :
    Uω (aρ 16) (bρ 16) (22202485159 / 50000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_414 :
    Uρ (22202485159 / 50000000000 : ℝ) ≤ (-(485301670043732980539 / 400000000000000000000 : ℝ)) :=
  by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (22202485159 / 50000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(8264585124940494284273 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (22202485159 / 50000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(8319525651625783148213 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (22202485159 / 50000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(4215230103394798454407 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (22202485159 / 50000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(8617907356384918787213 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (22202485159 / 50000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(8911448565837778337919 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (22202485159 / 50000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(9350967824237916076221 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (22202485159 / 50000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(4995329531900420707149 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (22202485159 / 50000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(10909985018713567947419 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (22202485159 / 50000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(191338797200200775319 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (22202485159 / 50000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) * (-(286298355615774617203 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (22202485159 / 50000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(3759439815845592521937 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (22202485159 / 50000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (22202485159 / 50000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (22202485159 / 50000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (22202485159 / 50000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (22202485159 / 50000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_414_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_415_1 :
    Uω (aρ 1) (bρ 1) (890748006113 / 2000000000000 : ℝ) ≤
      (-(2058591880093690254427 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2194602989710383 / 5000000000000000 : ℝ) ≤
      (-(2058591880093690254427 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2194602989710383 / 5000000000000000 : ℚ))
        (r' := (2194602989710383 / 1250000000000000 : ℚ))
        (U := (-(2058591880093690254427 / 2500000000000000000000 : ℚ)))
        (U' := (1407144021406309745573 / 2500000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (890748006113 / 2000000000000 : ℚ))
      (s := (1097292286590383 / 2500000000000000 : ℚ))
      (q := (2194602989710383 / 5000000000000000 : ℚ))
      (U := (-(2058591880093690254427 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_415_2 :
    Uω (aρ 2) (bρ 2) (890748006113 / 2000000000000 : ℝ) ≤
      (-(4144570193375825698037 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (272826922479647 / 625000000000000 : ℝ) ≤
      (-(4144570193375825698037 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (272826922479647 / 625000000000000 : ℚ))
        (r' := (272826922479647 / 156250000000000 : ℚ))
        (U := (-(4144570193375825698037 / 5000000000000000000000 : ℚ)))
        (U' := (2786901609624174301963 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (890748006113 / 2000000000000 : ℚ))
      (s := (272811732461169 / 625000000000000 : ℚ))
      (q := (272826922479647 / 625000000000000 : ℚ))
      (U := (-(4144570193375825698037 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_415_3 :
    Uω (aρ 3) (bρ 3) (890748006113 / 2000000000000 : ℝ) ≤
      (-(4199866056630123266719 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8634441766240031 / 20000000000000000 : ℝ) ≤
      (-(4199866056630123266719 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8634441766240031 / 20000000000000000 : ℚ))
        (r' := (8634441766240031 / 5000000000000000 : ℚ))
        (U := (-(4199866056630123266719 / 5000000000000000000000 : ℚ)))
        (U' := (2731605746369876733281 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (890748006113 / 2000000000000 : ℚ))
      (s := (4316364072620031 / 10000000000000000 : ℚ))
      (q := (8634441766240031 / 20000000000000000 : ℚ))
      (U := (-(4199866056630123266719 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_415_4 :
    Uω (aρ 4) (bρ 4) (890748006113 / 2000000000000 : ℝ) ≤
      (-(8586586592335453971777 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1694920269980443 / 4000000000000000 : ℝ) ≤
      (-(8586586592335453971777 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1694920269980443 / 4000000000000000 : ℚ))
        (r' := (1694920269980443 / 1000000000000000 : ℚ))
        (U := (-(8586586592335453971777 / 10000000000000000000000 : ℚ)))
        (U' := (5276357013664546028223 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (890748006113 / 2000000000000 : ℚ))
      (s := (846963567469443 / 2000000000000000 : ℚ))
      (q := (1694920269980443 / 4000000000000000 : ℚ))
      (U := (-(8586586592335453971777 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_415_5 :
    Uω (aρ 5) (bρ 5) (890748006113 / 2000000000000 : ℝ) ≤
      (-(34684235794435448991 / 39062500000000000000 : ℝ)) := by
  have hlg :
    Real.log (4115122719391029 / 10000000000000000 : ℝ) ≤
      (-(34684235794435448991 / 39062500000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4115122719391029 / 10000000000000000 : ℚ))
        (r' := (4115122719391029 / 2500000000000000 : ℚ))
        (U := (-(34684235794435448991 / 39062500000000000000 : ℚ)))
        (U' := (19467887666502051009 / 39062500000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (890748006113 / 2000000000000 : ℚ))
      (s := (2054325922781029 / 5000000000000000 : ℚ))
      (q := (4115122719391029 / 10000000000000000 : ℚ))
      (U := (-(34684235794435448991 / 39062500000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_415_6 :
    Uω (aρ 6) (bρ 6) (890748006113 / 2000000000000 : ℝ) ≤
      (-(4658577313435840435391 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (787754896431033 / 2000000000000000 : ℝ) ≤
      (-(4658577313435840435391 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (787754896431033 / 2000000000000000 : ℚ))
        (r' := (787754896431033 / 500000000000000 : ℚ))
        (U := (-(4658577313435840435391 / 5000000000000000000000 : ℚ)))
        (U' := (2272894489564159564609 / 5000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (890748006113 / 2000000000000 : ℚ))
      (s := (392319574623033 / 1000000000000000 : ℚ))
      (q := (787754896431033 / 2000000000000000 : ℚ))
      (U := (-(4658577313435840435391 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_415_7 :
    Uω (aρ 7) (bρ 7) (890748006113 / 2000000000000 : ℝ) ≤
      (-(9954414220290087389677 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3695602762945023 / 10000000000000000 : ℝ) ≤
      (-(9954414220290087389677 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3695602762945023 / 10000000000000000 : ℚ))
        (r' := (3695602762945023 / 2500000000000000 : ℚ))
        (U := (-(9954414220290087389677 / 10000000000000000000000 : ℚ)))
        (U' := (3908529385709912610323 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (890748006113 / 2000000000000 : ℚ))
      (s := (1830256844285023 / 5000000000000000 : ℚ))
      (q := (3695602762945023 / 10000000000000000 : ℚ))
      (U := (-(9954414220290087389677 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_415_8 :
    Uω (aρ 8) (bρ 8) (890748006113 / 2000000000000 : ℝ) ≤
      (-(5434870227411690620931 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (421544262712109 / 1250000000000000 : ℝ) ≤
      (-(5434870227411690620931 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (421544262712109 / 1250000000000000 : ℚ))
        (r' := (421544262712109 / 312500000000000 : ℚ))
        (U := (-(5434870227411690620931 / 5000000000000000000000 : ℚ)))
        (U' := (1496601575588309379069 / 5000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (890748006113 / 2000000000000 : ℚ))
      (s := (206097376088359 / 625000000000000 : ℚ))
      (q := (421544262712109 / 1250000000000000 : ℚ))
      (U := (-(5434870227411690620931 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_415_9 :
    Uω (aρ 9) (bρ 9) (890748006113 / 2000000000000 : ℝ) ≤
      (-(12198252685595503436989 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2952817572699407 / 10000000000000000 : ℝ) ≤
      (-(12198252685595503436989 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2952817572699407 / 10000000000000000 : ℚ))
        (r' := (2952817572699407 / 2500000000000000 : ℚ))
        (U := (-(12198252685595503436989 / 10000000000000000000000 : ℚ)))
        (U' := (1664690920404496563011 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (890748006113 / 2000000000000 : ℚ))
      (s := (1399725293889407 / 5000000000000000 : ℚ))
      (q := (2952817572699407 / 10000000000000000 : ℚ))
      (U := (-(12198252685595503436989 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_415_10 :
    Uω (aρ 10) (bρ 10) (890748006113 / 2000000000000 : ℝ) ≤
      (-(1781418685494105864799 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (601190022448769 / 2500000000000000 : ℝ) ≤
      (-(1781418685494105864799 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (601190022448769 / 2500000000000000 : ℚ))
        (r' := (601190022448769 / 312500000000000 : ℚ))
        (U := (-(1781418685494105864799 / 1250000000000000000000 : ℚ)))
        (U' := (817883240630894135201 / 1250000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (890748006113 / 2000000000000 : ℚ))
      (s := (32685853991643 / 156250000000000 : ℚ))
      (q := (601190022448769 / 2500000000000000 : ℚ))
      (U := (-(1781418685494105864799 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_415_11 :
    Uω (aρ 11) (bρ 11) (890748006113 / 2000000000000 : ℝ) ≤
      (-(9314361252783403192807 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (31045228193841 / 200000000000000 : ℝ) ≤
      (-(9314361252783403192807 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (31045228193841 / 200000000000000 : ℚ))
        (r' := (31045228193841 / 25000000000000 : ℚ))
        (U := (-(9314361252783403192807 / 5000000000000000000000 : ℚ)))
        (U' := (1082846451716596807193 / 5000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (890748006113 / 2000000000000 : ℚ))
      (s := (8053739214641 / 100000000000000 : ℚ))
      (q := (31045228193841 / 200000000000000 : ℚ))
      (U := (-(9314361252783403192807 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_415_12 :
    Uω (aρ 12) (bρ 12) (890748006113 / 2000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_415_13 :
    Uω (aρ 13) (bρ 13) (890748006113 / 2000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_415_14 :
    Uω (aρ 14) (bρ 14) (890748006113 / 2000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_415_15 :
    Uω (aρ 15) (bρ 15) (890748006113 / 2000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_415_16 :
    Uω (aρ 16) (bρ 16) (890748006113 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_415 :
    Uρ (890748006113 / 2000000000000 : ℝ) ≤
      (-(12093743108271133476063 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_415_1 U_415_2 U_415_3 U_415_4 U_415_5 U_415_6 U_415_7 U_415_8 U_415_9 U_415_10
    U_415_11 U_415_12 U_415_13 U_415_14 U_415_15 U_415_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_416_1 :
    Uω (aρ 1) (bρ 1) (446698302933 / 1000000000000 : ℝ) ≤
      (-(8204240952676966510493 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4402449088984149 / 10000000000000000 : ℝ) ≤
      (-(8204240952676966510493 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4402449088984149 / 10000000000000000 : ℚ))
        (r' := (4402449088984149 / 2500000000000000 : ℚ))
        (U := (-(8204240952676966510493 / 10000000000000000000000 : ℚ)))
        (U' := (5658702653323033489507 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (446698302933 / 1000000000000 : ℚ))
      (s := (2201206183361649 / 5000000000000000 : ℚ))
      (q := (4402449088984149 / 10000000000000000 : ℚ))
      (U := (-(8204240952676966510493 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_416_2 :
    Uω (aρ 2) (bρ 2) (446698302933 / 1000000000000 : ℝ) ≤
      (-(1032355897364107694117 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1094618623393083 / 2500000000000000 : ℝ) ≤
      (-(1032355897364107694117 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1094618623393083 / 2500000000000000 : ℚ))
        (r' := (1094618623393083 / 625000000000000 : ℚ))
        (U := (-(1032355897364107694117 / 1250000000000000000000 : ℚ)))
        (U' := (700512053385892305883 / 1250000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (446698302933 / 1000000000000 : ℚ))
      (s := (68409877943901 / 156250000000000 : ℚ))
      (q := (1094618623393083 / 2500000000000000 : ℚ))
      (U := (-(1032355897364107694117 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_416_3 :
    Uω (aρ 3) (bρ 3) (446698302933 / 1000000000000 : ℝ) ≤
      (-(8369098189383941263791 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8660933005231133 / 20000000000000000 : ℝ) ≤
      (-(8369098189383941263791 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8660933005231133 / 20000000000000000 : ℚ))
        (r' := (8660933005231133 / 5000000000000000 : ℚ))
        (U := (-(8369098189383941263791 / 10000000000000000000000 : ℚ)))
        (U' := (5493845416616058736209 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (446698302933 / 1000000000000 : ℚ))
      (s := (4329612312846133 / 10000000000000000 : ℚ))
      (q := (8660933005231133 / 20000000000000000 : ℚ))
      (U := (-(8369098189383941263791 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_416_4 :
    Uω (aρ 4) (bρ 4) (446698302933 / 1000000000000 : ℝ) ≤
      (-(8555363735410042263653 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4250551413754841 / 10000000000000000 : ℝ) ≤
      (-(8555363735410042263653 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4250551413754841 / 10000000000000000 : ℚ))
        (r' := (4250551413754841 / 2500000000000000 : ℚ))
        (U := (-(8555363735410042263653 / 10000000000000000000000 : ℚ)))
        (U' := (5307579870589957736347 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (446698302933 / 1000000000000 : ℚ))
      (s := (2124038158094841 / 5000000000000000 : ℚ))
      (q := (4250551413754841 / 10000000000000000 : ℚ))
      (U := (-(8555363735410042263653 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_416_5 :
    Uω (aρ 5) (bρ 5) (446698302933 / 1000000000000 : ℝ) ≤
      (-(884698437876299503827 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4128386507949351 / 10000000000000000 : ℝ) ≤
      (-(884698437876299503827 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4128386507949351 / 10000000000000000 : ℚ))
        (r' := (4128386507949351 / 2500000000000000 : ℚ))
        (U := (-(884698437876299503827 / 1000000000000000000000 : ℚ)))
        (U' := (501595922723700496173 / 1000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (446698302933 / 1000000000000 : ℚ))
      (s := (2060968211956851 / 5000000000000000 : ℚ))
      (q := (4128386507949351 / 10000000000000000 : ℚ))
      (U := (-(884698437876299503827 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_416_6 :
    Uω (aρ 6) (bρ 6) (446698302933 / 1000000000000 : ℝ) ≤
      (-(9283456279446531117199 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3952069890330607 / 10000000000000000 : ℝ) ≤
      (-(9283456279446531117199 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3952069890330607 / 10000000000000000 : ℚ))
        (r' := (3952069890330607 / 2500000000000000 : ℚ))
        (U := (-(9283456279446531117199 / 10000000000000000000000 : ℚ)))
        (U' := (4579487326553468882801 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (446698302933 / 1000000000000 : ℚ))
      (s := (1968271781908107 / 5000000000000000 : ℚ))
      (q := (3952069890330607 / 10000000000000000 : ℚ))
      (U := (-(9283456279446531117199 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_416_7 :
    Uω (aρ 7) (bρ 7) (446698302933 / 1000000000000 : ℝ) ≤
      (-(2479575692907522664859 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3708972244928743 / 10000000000000000 : ℝ) ≤
      (-(2479575692907522664859 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3708972244928743 / 10000000000000000 : ℚ))
        (r' := (3708972244928743 / 2500000000000000 : ℚ))
        (U := (-(2479575692907522664859 / 2500000000000000000000 : ℚ)))
        (U' := (986160208592477335141 / 2500000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (446698302933 / 1000000000000 : ℚ))
      (s := (1837004826886243 / 5000000000000000 : ℚ))
      (q := (3708972244928743 / 10000000000000000 : ℚ))
      (U := (-(2479575692907522664859 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_416_8 :
    Uω (aρ 8) (bρ 8) (446698302933 / 1000000000000 : ℝ) ≤
      (-(2165932898364507387119 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (677179250626111 / 2000000000000000 : ℝ) ≤
      (-(2165932898364507387119 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (677179250626111 / 2000000000000000 : ℚ))
        (r' := (677179250626111 / 500000000000000 : ℚ))
        (U := (-(2165932898364507387119 / 2000000000000000000000 : ℚ)))
        (U' := (606655822835492612881 / 2000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (446698302933 / 1000000000000 : ℚ))
      (s := (331139932151611 / 1000000000000000 : ℚ))
      (q := (677179250626111 / 2000000000000000 : ℚ))
      (U := (-(2165932898364507387119 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_416_9 :
    Uω (aρ 9) (bρ 9) (446698302933 / 1000000000000 : ℝ) ≤
      (-(12151070657503466858303 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5933564967200663 / 20000000000000000 : ℝ) ≤
      (-(12151070657503466858303 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5933564967200663 / 20000000000000000 : ℚ))
        (r' := (5933564967200663 / 5000000000000000 : ℚ))
        (U := (-(12151070657503466858303 / 10000000000000000000000 : ℚ)))
        (U' := (1711872948496533141697 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (446698302933 / 1000000000000 : ℚ))
      (s := (2814137410815663 / 10000000000000000 : ℚ))
      (q := (5933564967200663 / 20000000000000000 : ℚ))
      (U := (-(12151070657503466858303 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_416_10 :
    Uω (aρ 10) (bρ 10) (446698302933 / 1000000000000 : ℝ) ≤
      (-(3547075465469153810511 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (604992356392347 / 2500000000000000 : ℝ) ≤
      (-(3547075465469153810511 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (604992356392347 / 2500000000000000 : ℚ))
        (r' := (604992356392347 / 312500000000000 : ℚ))
        (U := (-(3547075465469153810511 / 2500000000000000000000 : ℚ)))
        (U' := (1651528386780846189489 / 2500000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (446698302933 / 1000000000000 : ℚ))
      (s := (263633791031097 / 1250000000000000 : ℚ))
      (q := (604992356392347 / 2500000000000000 : ℚ))
      (U := (-(3547075465469153810511 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_416_11 :
    Uω (aρ 11) (bρ 11) (446698302933 / 1000000000000 : ℝ) ≤
      (-(738719378596878066367 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1577413760887911 / 10000000000000000 : ℝ) ≤
      (-(738719378596878066367 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1577413760887911 / 10000000000000000 : ℚ))
        (r' := (1577413760887911 / 1250000000000000 : ℚ))
        (U := (-(738719378596878066367 / 400000000000000000000 : ℚ)))
        (U' := (93057237763121933633 / 400000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (446698302933 / 1000000000000 : ℚ))
      (s := (421217812545411 / 5000000000000000 : ℚ))
      (q := (1577413760887911 / 10000000000000000 : ℚ))
      (U := (-(738719378596878066367 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_416_12 :
    Uω (aρ 12) (bρ 12) (446698302933 / 1000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_416_13 :
    Uω (aρ 13) (bρ 13) (446698302933 / 1000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_416_14 :
    Uω (aρ 14) (bρ 14) (446698302933 / 1000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_416_15 :
    Uω (aρ 15) (bρ 15) (446698302933 / 1000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_416_16 :
    Uω (aρ 16) (bρ 16) (446698302933 / 1000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_416 :
    Uρ (446698302933 / 1000000000000 : ℝ) ≤
      (-(1506959668461532668943 / 1250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_416_1 U_416_2 U_416_3 U_416_4 U_416_5 U_416_6 U_416_7 U_416_8 U_416_9 U_416_10
    U_416_11 U_416_12 U_416_13 U_416_14 U_416_15 U_416_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_417_1 :
    Uω (aρ 1) (bρ 1) (896045205619 / 2000000000000 : ℝ) ≤
      (-(2043551218737480737427 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (883138439576587 / 2000000000000000 : ℝ) ≤
      (-(2043551218737480737427 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (883138439576587 / 2000000000000000 : ℚ))
        (r' := (883138439576587 / 500000000000000 : ℚ))
        (U := (-(2043551218737480737427 / 2500000000000000000000 : ℚ)))
        (U' := (1422184682762519262573 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (896045205619 / 2000000000000 : ℚ))
      (s := (441565558575587 / 1000000000000000 : ℚ))
      (q := (883138439576587 / 2000000000000000 : ℚ))
      (U := (-(2043551218737480737427 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_417_2 :
    Uω (aρ 2) (bρ 2) (896045205619 / 2000000000000 : ℝ) ≤
      (-(2057161367982340828791 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4391718223036311 / 10000000000000000 : ℝ) ≤
      (-(2057161367982340828791 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4391718223036311 / 10000000000000000 : ℚ))
        (r' := (4391718223036311 / 2500000000000000 : ℚ))
        (U := (-(2057161367982340828791 / 2500000000000000000000 : ℚ)))
        (U' := (1408574533517659171209 / 2500000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (896045205619 / 2000000000000 : ℚ))
      (s := (2195738324286311 / 5000000000000000 : ℚ))
      (q := (4391718223036311 / 10000000000000000 : ℚ))
      (U := (-(2057161367982340828791 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_417_3 :
    Uω (aρ 3) (bρ 3) (896045205619 / 2000000000000 : ℝ) ≤
      (-(833855785951075132007 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1085928026531197 / 2500000000000000 : ℝ) ≤
      (-(833855785951075132007 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1085928026531197 / 2500000000000000 : ℚ))
        (r' := (1085928026531197 / 625000000000000 : ℚ))
        (U := (-(833855785951075132007 / 1000000000000000000000 : ℚ)))
        (U' := (552438574648924867993 / 1000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (896045205619 / 2000000000000 : ℚ))
      (s := (542857565137447 / 1250000000000000 : ℚ))
      (q := (1085928026531197 / 2500000000000000 : ℚ))
      (U := (-(833855785951075132007 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_417_4 :
    Uω (aρ 4) (bρ 4) (896045205619 / 2000000000000 : ℝ) ≤
      (-(1704847634940521090967 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8527604208845687 / 20000000000000000 : ℝ) ≤
      (-(1704847634940521090967 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8527604208845687 / 20000000000000000 : ℚ))
        (r' := (8527604208845687 / 5000000000000000 : ℚ))
        (U := (-(1704847634940521090967 / 2000000000000000000000 : ℚ)))
        (U' := (1067741086259478909033 / 2000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (896045205619 / 2000000000000 : ℚ))
      (s := (4261334698760687 / 10000000000000000 : ℚ))
      (q := (8527604208845687 / 20000000000000000 : ℚ))
      (U := (-(1704847634940521090967 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_417_5 :
    Uω (aρ 5) (bρ 5) (896045205619 / 2000000000000 : ℝ) ≤
      (-(1101863492402909633239 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8283300326280939 / 20000000000000000 : ℝ) ≤
      (-(1101863492402909633239 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8283300326280939 / 20000000000000000 : ℚ))
        (r' := (8283300326280939 / 5000000000000000 : ℚ))
        (U := (-(1101863492402909633239 / 1250000000000000000000 : ℚ)))
        (U' := (631004458347090366761 / 1250000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (896045205619 / 2000000000000 : ℚ))
      (s := (4135220735530939 / 10000000000000000 : ℚ))
      (q := (8283300326280939 / 20000000000000000 : ℚ))
      (U := (-(1101863492402909633239 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_417_6 :
    Uω (aρ 6) (bρ 6) (896045205619 / 2000000000000 : ℝ) ≤
      (-(9249871998363191376847 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7930729891367817 / 20000000000000000 : ℝ) ≤
      (-(9249871998363191376847 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7930729891367817 / 20000000000000000 : ℚ))
        (r' := (7930729891367817 / 5000000000000000 : ℚ))
        (U := (-(9249871998363191376847 / 10000000000000000000000 : ℚ)))
        (U' := (4613071607636808623153 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (896045205619 / 2000000000000 : ℚ))
      (s := (3949890675757817 / 10000000000000000 : ℚ))
      (q := (7930729891367817 / 20000000000000000 : ℚ))
      (U := (-(9249871998363191376847 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_417_7 :
    Uω (aρ 7) (bρ 7) (896045205619 / 2000000000000 : ℝ) ≤
      (-(494116186075126798691 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1488936323901157 / 4000000000000000 : ℝ) ≤
      (-(494116186075126798691 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1488936323901157 / 4000000000000000 : ℚ))
        (r' := (1488936323901157 / 1000000000000000 : ℚ))
        (U := (-(494116186075126798691 / 500000000000000000000 : ℚ)))
        (U' := (199030994224873201309 / 500000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (896045205619 / 2000000000000 : ℚ))
      (s := (737500756931157 / 2000000000000000 : ℚ))
      (q := (1488936323901157 / 4000000000000000 : ℚ))
      (U := (-(494116186075126798691 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_417_8 :
    Uω (aρ 8) (bρ 8) (896045205619 / 2000000000000 : ℝ) ≤
      (-(10789755663946743181419 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3399435967944357 / 10000000000000000 : ℝ) ≤
      (-(10789755663946743181419 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3399435967944357 / 10000000000000000 : ℚ))
        (r' := (3399435967944357 / 2500000000000000 : ℚ))
        (U := (-(10789755663946743181419 / 10000000000000000000000 : ℚ)))
        (U' := (3073187942053256818581 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (896045205619 / 2000000000000 : ℚ))
      (s := (1662617876189357 / 5000000000000000 : ℚ))
      (q := (3399435967944357 / 10000000000000000 : ℚ))
      (U := (-(10789755663946743181419 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_417_9 :
    Uω (aρ 9) (bρ 9) (896045205619 / 2000000000000 : ℝ) ≤
      (-(756508381948669364161 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (372592533353797 / 1250000000000000 : ℝ) ≤
      (-(756508381948669364161 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (372592533353797 / 1250000000000000 : ℚ))
        (r' := (372592533353797 / 312500000000000 : ℚ))
        (U := (-(756508381948669364161 / 625000000000000000000 : ℚ)))
        (U' := (109925593426330635839 / 625000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (896045205619 / 2000000000000 : ℚ))
      (s := (88400311828461 / 312500000000000 : ℚ))
      (q := (372592533353797 / 1250000000000000 : ℚ))
      (U := (-(756508381948669364161 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_417_10 :
    Uω (aρ 10) (bρ 10) (896045205619 / 2000000000000 : ℝ) ≤
      (-(2825152954444311047283 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2435150630002837 / 10000000000000000 : ℝ) ≤
      (-(2825152954444311047283 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2435150630002837 / 10000000000000000 : ℚ))
        (r' := (2435150630002837 / 1250000000000000 : ℚ))
        (U := (-(2825152954444311047283 / 2000000000000000000000 : ℚ)))
        (U' := (1333730127355688952717 / 2000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (896045205619 / 2000000000000 : ℚ))
      (s := (1063094869175337 / 5000000000000000 : ℚ))
      (q := (2435150630002837 / 10000000000000000 : ℚ))
      (U := (-(2825152954444311047283 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_417_11 :
    Uω (aρ 11) (bρ 11) (896045205619 / 2000000000000 : ℝ) ≤
      (-(3662808807969156807193 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3203768806367033 / 20000000000000000 : ℝ) ≤
      (-(3662808807969156807193 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3203768806367033 / 20000000000000000 : ℚ))
        (r' := (3203768806367033 / 2500000000000000 : ℚ))
        (U := (-(3662808807969156807193 / 2000000000000000000000 : ℚ)))
        (U' := (496074273830843192807 / 2000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (896045205619 / 2000000000000 : ℚ))
      (s := (878133910917033 / 10000000000000000 : ℚ))
      (q := (3203768806367033 / 20000000000000000 : ℚ))
      (U := (-(3662808807969156807193 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_417_12 :
    Uω (aρ 12) (bρ 12) (896045205619 / 2000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_417_13 :
    Uω (aρ 13) (bρ 13) (896045205619 / 2000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_417_14 :
    Uω (aρ 14) (bρ 14) (896045205619 / 2000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_417_15 :
    Uω (aρ 15) (bρ 15) (896045205619 / 2000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_417_16 :
    Uω (aρ 16) (bρ 16) (896045205619 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_417 :
    Uρ (896045205619 / 2000000000000 : ℝ) ≤
      (-(2403653742116277630583 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_417_1 U_417_2 U_417_3 U_417_4 U_417_5 U_417_6 U_417_7 U_417_8 U_417_9 U_417_10
    U_417_11 U_417_12 U_417_13 U_417_14 U_417_15 U_417_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_418_1 :
    Uω (aρ 1) (bρ 1) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(326368824010608195853 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (442231375208497 / 1000000000000000 : ℝ) ≤
      (-(326368824010608195853 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (442231375208497 / 1000000000000000 : ℚ))
        (r' := (442231375208497 / 250000000000000 : ℚ))
        (U := (-(326368824010608195853 / 400000000000000000000 : ℚ)))
        (U' := (228148920229391804147 / 400000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1794739010991 / 4000000000000 : ℚ))
      (s := (27639232467359 / 62500000000000 : ℚ))
      (q := (442231375208497 / 1000000000000000 : ℚ))
      (U := (-(326368824010608195853 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_418_2 :
    Uω (aρ 2) (bρ 2) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(4106789379413987168301 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8796680172236137 / 20000000000000000 : ℝ) ≤
      (-(4106789379413987168301 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8796680172236137 / 20000000000000000 : ℚ))
        (r' := (8796680172236137 / 5000000000000000 : ℚ))
        (U := (-(4106789379413987168301 / 5000000000000000000000 : ℚ)))
        (U' := (2824682423586012831699 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1794739010991 / 4000000000000 : ℚ))
      (s := (4398098875353637 / 10000000000000000 : ℚ))
      (q := (8796680172236137 / 20000000000000000 : ℚ))
      (U := (-(4106789379413987168301 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_418_3 :
    Uω (aρ 3) (bρ 3) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(8323322613875938862681 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (174013396077207 / 400000000000000 : ℝ) ≤
      (-(8323322613875938862681 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (174013396077207 / 400000000000000 : ℚ))
        (r' := (174013396077207 / 100000000000000 : ℚ))
        (U := (-(8323322613875938862681 / 10000000000000000000000 : ℚ)))
        (U' := (5539620992124061137319 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1794739010991 / 4000000000000 : ℚ))
      (s := (86989692266557 / 200000000000000 : ℚ))
      (q := (174013396077207 / 400000000000000 : ℚ))
      (U := (-(8323322613875938862681 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_418_4 :
    Uω (aρ 4) (bρ 4) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(8508711691084804030819 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4270427431846133 / 10000000000000000 : ℝ) ≤
      (-(8508711691084804030819 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4270427431846133 / 10000000000000000 : ℚ))
        (r' := (4270427431846133 / 2500000000000000 : ℚ))
        (U := (-(8508711691084804030819 / 10000000000000000000000 : ℚ)))
        (U' := (5354231914915195969181 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1794739010991 / 4000000000000 : ℚ))
      (s := (2133981927112383 / 5000000000000000 : ℚ))
      (q := (4270427431846133 / 10000000000000000 : ℚ))
      (U := (-(8508711691084804030819 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_418_5 :
    Uω (aρ 5) (bρ 5) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(2199727085099057476111 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2074140970562173 / 5000000000000000 : ℝ) ≤
      (-(2199727085099057476111 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2074140970562173 / 5000000000000000 : ℚ))
        (r' := (2074140970562173 / 1250000000000000 : ℚ))
        (U := (-(2199727085099057476111 / 2500000000000000000000 : ℚ)))
        (U' := (1266008816400942523889 / 2500000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1794739010991 / 4000000000000 : ℚ))
      (s := (129433212253631 / 312500000000000 : ℚ))
      (q := (2074140970562173 / 5000000000000000 : ℚ))
      (U := (-(2199727085099057476111 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_418_6 :
    Uω (aρ 6) (bρ 6) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(4616561195014913821701 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3972012342168089 / 10000000000000000 : ℝ) ≤
      (-(4616561195014913821701 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3972012342168089 / 10000000000000000 : ℚ))
        (r' := (3972012342168089 / 2500000000000000 : ℚ))
        (U := (-(4616561195014913821701 / 5000000000000000000000 : ℚ)))
        (U' := (2314910607985086178299 / 5000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1794739010991 / 4000000000000 : ℚ))
      (s := (1978281984671839 / 5000000000000000 : ℚ))
      (q := (3972012342168089 / 10000000000000000 : ℚ))
      (U := (-(4616561195014913821701 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_418_7 :
    Uω (aρ 7) (bρ 7) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(4932191768818572964023 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1491609900548377 / 4000000000000000 : ℝ) ≤
      (-(4932191768818572964023 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1491609900548377 / 4000000000000000 : ℚ))
        (r' := (1491609900548377 / 1000000000000000 : ℚ))
        (U := (-(4932191768818572964023 / 5000000000000000000000 : ℚ)))
        (U' := (1999280034181427035977 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (1794739010991 / 4000000000000 : ℚ))
      (s := (738850033701877 / 2000000000000000 : ℚ))
      (q := (1491609900548377 / 4000000000000000 : ℚ))
      (U := (-(4932191768818572964023 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_418_8 :
    Uω (aρ 8) (bρ 8) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(2153972694606828066529 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1703102460552339 / 5000000000000000 : ℝ) ≤
      (-(2153972694606828066529 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1703102460552339 / 5000000000000000 : ℚ))
        (r' := (1703102460552339 / 1250000000000000 : ℚ))
        (U := (-(2153972694606828066529 / 2000000000000000000000 : ℚ)))
        (U' := (618616026593171933471 / 2000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (1794739010991 / 4000000000000 : ℚ))
      (s := (416519019914607 / 1250000000000000 : ℚ))
      (q := (1703102460552339 / 5000000000000000 : ℚ))
      (U := (-(2153972694606828066529 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_418_9 :
    Uω (aρ 9) (bρ 9) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(12080757024811163845657 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (597543304028569 / 2000000000000000 : ℝ) ≤
      (-(12080757024811163845657 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (597543304028569 / 2000000000000000 : ℚ))
        (r' := (597543304028569 / 500000000000000 : ℚ))
        (U := (-(12080757024811163845657 / 10000000000000000000000 : ℚ)))
        (U' := (1782186581188836154343 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (1794739010991 / 4000000000000 : ℚ))
      (s := (283614098575319 / 1000000000000000 : ℚ))
      (q := (597543304028569 / 2000000000000000 : ℚ))
      (U := (-(12080757024811163845657 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_418_10 :
    Uω (aρ 10) (bρ 10) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(14094684596889839880361 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1221365447276197 / 5000000000000000 : ℝ) ≤
      (-(14094684596889839880361 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1221365447276197 / 5000000000000000 : ℚ))
        (r' := (1221365447276197 / 625000000000000 : ℚ))
        (U := (-(14094684596889839880361 / 10000000000000000000000 : ℚ)))
        (U' := (6699730812110160119639 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (1794739010991 / 4000000000000 : ℚ))
      (s := (266841096008411 / 1250000000000000 : ℚ))
      (q := (1221365447276197 / 5000000000000000 : ℚ))
      (U := (-(14094684596889839880361 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_418_11 :
    Uω (aρ 11) (bρ 11) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(18239378751248439378963 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (322777936483651 / 2000000000000000 : ℝ) ≤
      (-(18239378751248439378963 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (322777936483651 / 2000000000000000 : ℚ))
        (r' := (322777936483651 / 250000000000000 : ℚ))
        (U := (-(18239378751248439378963 / 10000000000000000000000 : ℚ)))
        (U' := (2555036657751560621037 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (1794739010991 / 4000000000000 : ℚ))
      (s := (89552297000401 / 1000000000000000 : ℚ))
      (q := (322777936483651 / 2000000000000000 : ℚ))
      (U := (-(18239378751248439378963 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_418_12 :
    Uω (aρ 12) (bρ 12) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_418_13 :
    Uω (aρ 13) (bρ 13) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_418_14 :
    Uω (aρ 14) (bρ 14) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_418_15 :
    Uω (aρ 15) (bρ 15) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_418_16 :
    Uω (aρ 16) (bρ 16) (1794739010991 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_418 :
    Uρ (1794739010991 / 4000000000000 : ℝ) ≤
      (-(599989554116664840691 / 500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_418_1 U_418_2 U_418_3 U_418_4 U_418_5 U_418_6 U_418_7 U_418_8 U_418_9 U_418_10
    U_418_11 U_418_12 U_418_13 U_418_14 U_418_15 U_418_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_419_1 :
    Uω (aρ 1) (bρ 1) (224673451343 / 500000000000 : ℝ) ≤
      (-(2036064686302483332461 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2214467653061543 / 5000000000000000 : ℝ) ≤
      (-(2036064686302483332461 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2214467653061543 / 5000000000000000 : ℚ))
        (r' := (2214467653061543 / 1250000000000000 : ℚ))
        (U := (-(2036064686302483332461 / 2500000000000000000000 : ℚ)))
        (U' := (1429671215197516667539 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (224673451343 / 500000000000 : ℚ))
      (s := (1107224700867793 / 2500000000000000 : ℚ))
      (q := (2214467653061543 / 5000000000000000 : ℚ))
      (U := (-(2036064686302483332461 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_419_2 :
    Uω (aρ 2) (bρ 2) (224673451343 / 500000000000 : ℝ) ≤
      (-(8198534714646879541903 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4404961948106287 / 10000000000000000 : ℝ) ≤
      (-(8198534714646879541903 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4404961948106287 / 10000000000000000 : ℚ))
        (r' := (4404961948106287 / 2500000000000000 : ℚ))
        (U := (-(8198534714646879541903 / 10000000000000000000000 : ℚ)))
        (U' := (5664408891353120458097 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (224673451343 / 500000000000 : ℚ))
      (s := (2202360549973787 / 5000000000000000 : ℚ))
      (q := (4404961948106287 / 10000000000000000 : ℚ))
      (U := (-(8198534714646879541903 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_419_3 :
    Uω (aρ 3) (bρ 3) (224673451343 / 500000000000 : ℝ) ≤
      (-(4154055276627529415703 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4356957693793537 / 10000000000000000 : ℝ) ≤
      (-(4154055276627529415703 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4356957693793537 / 10000000000000000 : ℚ))
        (r' := (4356957693793537 / 2500000000000000 : ℚ))
        (U := (-(4154055276627529415703 / 5000000000000000000000 : ℚ)))
        (U' := (2777416526372470584297 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (224673451343 / 500000000000 : ℚ))
      (s := (2178054348836037 / 5000000000000000 : ℚ))
      (q := (4356957693793537 / 10000000000000000 : ℚ))
      (U := (-(4154055276627529415703 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_419_4 :
    Uω (aρ 4) (bρ 4) (224673451343 / 500000000000 : ℝ) ≤
      (-(53082558156334955823 / 62500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8554105494806037 / 20000000000000000 : ℝ) ≤
      (-(53082558156334955823 / 62500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8554105494806037 / 20000000000000000 : ℚ))
        (r' := (8554105494806037 / 5000000000000000 : ℚ))
        (U := (-(53082558156334955823 / 62500000000000000000 : ℚ)))
        (U' := (33560839381165044177 / 62500000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (224673451343 / 500000000000 : ℚ))
      (s := (4274592985956037 / 10000000000000000 : ℚ))
      (q := (8554105494806037 / 20000000000000000 : ℚ))
      (U := (-(53082558156334955823 / 62500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_419_5 :
    Uω (aρ 5) (bρ 5) (224673451343 / 500000000000 : ℝ) ≤
      (-(2195733594623203264179 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2077456843122793 / 5000000000000000 : ℝ) ≤
      (-(2195733594623203264179 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2077456843122793 / 5000000000000000 : ℚ))
        (r' := (2077456843122793 / 1250000000000000 : ℚ))
        (U := (-(2195733594623203264179 / 2500000000000000000000 : ℚ)))
        (U' := (1270002306876796735821 / 2500000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (224673451343 / 500000000000 : ℚ))
      (s := (1037126195744043 / 2500000000000000 : ℚ))
      (q := (2077456843122793 / 5000000000000000 : ℚ))
      (U := (-(2195733594623203264179 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_419_6 :
    Uω (aρ 6) (bρ 6) (224673451343 / 500000000000 : ℝ) ≤
      (-(92164010080748980551 / 100000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7957319303559397 / 20000000000000000 : ℝ) ≤
      (-(92164010080748980551 / 100000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7957319303559397 / 20000000000000000 : ℚ))
        (r' := (7957319303559397 / 5000000000000000 : ℚ))
        (U := (-(92164010080748980551 / 100000000000000000000 : ℚ)))
        (U' := (46465425979251019449 / 100000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (224673451343 / 500000000000 : ℚ))
      (s := (3963237089184397 / 10000000000000000 : ℚ))
      (q := (7957319303559397 / 20000000000000000 : ℚ))
      (U := (-(92164010080748980551 / 100000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_419_7 :
    Uω (aρ 7) (bρ 7) (224673451343 / 500000000000 : ℝ) ≤
      (-(9846476084902234316057 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1867854233724793 / 5000000000000000 : ℝ) ≤
      (-(9846476084902234316057 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1867854233724793 / 5000000000000000 : ℚ))
        (r' := (1867854233724793 / 1250000000000000 : ℚ))
        (U := (-(9846476084902234316057 / 10000000000000000000000 : ℚ)))
        (U' := (4016467521097765683943 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (224673451343 / 500000000000 : ℚ))
      (s := (925249025321043 / 2500000000000000 : ℚ))
      (q := (1867854233724793 / 5000000000000000 : ℚ))
      (U := (-(9846476084902234316057 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_419_8 :
    Uω (aρ 8) (bρ 8) (224673451343 / 500000000000 : ℝ) ≤
      (-(2687503131290268703811 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6825946552857763 / 20000000000000000 : ℝ) ≤
      (-(2687503131290268703811 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6825946552857763 / 20000000000000000 : ℚ))
        (r' := (6825946552857763 / 5000000000000000 : ℚ))
        (U := (-(2687503131290268703811 / 2500000000000000000000 : ℚ)))
        (U' := (778232770209731296189 / 2500000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (224673451343 / 500000000000 : ℚ))
      (s := (3339067370582763 / 10000000000000000 : ℚ))
      (q := (6825946552857763 / 20000000000000000 : ℚ))
      (U := (-(2687503131290268703811 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_419_9 :
    Uω (aρ 9) (bρ 9) (224673451343 / 500000000000 : ℝ) ≤
      (-(1507180034067428396347 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5989382065455843 / 20000000000000000 : ℝ) ≤
      (-(1507180034067428396347 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5989382065455843 / 20000000000000000 : ℚ))
        (r' := (5989382065455843 / 5000000000000000 : ℚ))
        (U := (-(1507180034067428396347 / 1250000000000000000000 : ℚ)))
        (U' := (225687916682571603653 / 1250000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (224673451343 / 500000000000 : ℚ))
      (s := (2843468511540843 / 10000000000000000 : ℚ))
      (q := (5989382065455843 / 20000000000000000 : ℚ))
      (U := (-(1507180034067428396347 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_419_10 :
    Uω (aρ 10) (bρ 10) (224673451343 / 500000000000 : ℝ) ≤
      (-(7031864198912791906271 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4900608754398927 / 20000000000000000 : ℝ) ≤
      (-(7031864198912791906271 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4900608754398927 / 20000000000000000 : ℚ))
        (r' := (4900608754398927 / 2500000000000000 : ℚ))
        (U := (-(7031864198912791906271 / 5000000000000000000000 : ℚ)))
        (U' := (3365343505587208093729 / 5000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (224673451343 / 500000000000 : ℚ))
      (s := (2143254233978927 / 10000000000000000 : ℚ))
      (q := (4900608754398927 / 20000000000000000 : ℚ))
      (U := (-(7031864198912791906271 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_419_11 :
    Uω (aρ 11) (bρ 11) (224673451343 / 500000000000 : ℝ) ≤
      (-(9083068948402617052851 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3251506681080341 / 20000000000000000 : ℝ) ≤
      (-(9083068948402617052851 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3251506681080341 / 20000000000000000 : ℚ))
        (r' := (3251506681080341 / 2500000000000000 : ℚ))
        (U := (-(9083068948402617052851 / 5000000000000000000000 : ℚ)))
        (U' := (1314138756097382947149 / 5000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (224673451343 / 500000000000 : ℚ))
      (s := (912628786865341 / 10000000000000000 : ℚ))
      (q := (3251506681080341 / 20000000000000000 : ℚ))
      (U := (-(9083068948402617052851 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_419_12 :
    Uω (aρ 12) (bρ 12) (224673451343 / 500000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_419_13 :
    Uω (aρ 13) (bρ 13) (224673451343 / 500000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_419_14 :
    Uω (aρ 14) (bρ 14) (224673451343 / 500000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_419_15 :
    Uω (aρ 15) (bρ 15) (224673451343 / 500000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_419_16 :
    Uω (aρ 16) (bρ 16) (224673451343 / 500000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_419 :
    Uρ (224673451343 / 500000000000 : ℝ) ≤
      (-(2396291097251474981877 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_419_1 U_419_2 U_419_3 U_419_4 U_419_5 U_419_6 U_419_7 U_419_8 U_419_9 U_419_10
    U_419_11 U_419_12 U_419_13 U_419_14 U_419_15 U_419_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_420_1 :
    Uω (aρ 1) (bρ 1) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(4064659621397125910963 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4435556859998017 / 10000000000000000 : ℝ) ≤
      (-(4064659621397125910963 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4435556859998017 / 10000000000000000 : ℚ))
        (r' := (4435556859998017 / 2500000000000000 : ℚ))
        (U := (-(4064659621397125910963 / 5000000000000000000000 : ℚ)))
        (U' := (2866812181602874089037 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1800036210497 / 4000000000000 : ℚ))
      (s := (2217760205919267 / 5000000000000000 : ℚ))
      (q := (4435556859998017 / 10000000000000000 : ℚ))
      (U := (-(4064659621397125910963 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_420_2 :
    Uω (aρ 2) (bρ 2) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(4091756635633582914549 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8823167618011783 / 20000000000000000 : ℝ) ≤
      (-(4091756635633582914549 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8823167618011783 / 20000000000000000 : ℚ))
        (r' := (8823167618011783 / 5000000000000000 : ℚ))
        (U := (-(4091756635633582914549 / 5000000000000000000000 : ℚ)))
        (U' := (2839715167366417085451 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1800036210497 / 4000000000000 : ℚ))
      (s := (4411343322364283 / 10000000000000000 : ℚ))
      (q := (8823167618011783 / 20000000000000000 : ℚ))
      (U := (-(4091756635633582914549 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_420_3 :
    Uω (aρ 3) (bρ 3) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(8292921607161953238429 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8727160963465661 / 20000000000000000 : ℝ) ≤
      (-(8292921607161953238429 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8727160963465661 / 20000000000000000 : ℚ))
        (r' := (8727160963465661 / 5000000000000000 : ℚ))
        (U := (-(8292921607161953238429 / 10000000000000000000000 : ℚ)))
        (U' := (5570021998838046761571 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1800036210497 / 4000000000000 : ℚ))
      (s := (4362732774168161 / 10000000000000000 : ℚ))
      (q := (8727160963465661 / 20000000000000000 : ℚ))
      (U := (-(8292921607161953238429 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_420_4 :
    Uω (aρ 4) (bρ 4) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(1059716367714879467071 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1713471220459449 / 4000000000000000 : ℝ) ≤
      (-(1059716367714879467071 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1713471220459449 / 4000000000000000 : ℚ))
        (r' := (1713471220459449 / 1000000000000000 : ℚ))
        (U := (-(1059716367714879467071 / 1250000000000000000000 : ℚ)))
        (U' := (673151583035120532929 / 1250000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1800036210497 / 4000000000000 : ℚ))
      (s := (856244418812949 / 2000000000000000 : ℚ))
      (q := (1713471220459449 / 4000000000000000 : ℚ))
      (U := (-(1059716367714879467071 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_420_5 :
    Uω (aρ 5) (bρ 5) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(1753397194246807411647 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1664618159464713 / 4000000000000000 : ℝ) ≤
      (-(1753397194246807411647 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1664618159464713 / 4000000000000000 : ℚ))
        (r' := (1664618159464713 / 1000000000000000 : ℚ))
        (U := (-(1753397194246807411647 / 2000000000000000000000 : ℚ)))
        (U' := (1019191526953192588353 / 2000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1800036210497 / 4000000000000 : ℚ))
      (s := (831029341685213 / 2000000000000000 : ℚ))
      (q := (1664618159464713 / 4000000000000000 : ℚ))
      (U := (-(1753397194246807411647 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_420_6 :
    Uω (aρ 6) (bρ 6) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(183994155135901900949 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7970613749913629 / 20000000000000000 : ℝ) ≤
      (-(183994155135901900949 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7970613749913629 / 20000000000000000 : ℚ))
        (r' := (7970613749913629 / 5000000000000000 : ℚ))
        (U := (-(183994155135901900949 / 200000000000000000000 : ℚ)))
        (U' := (93264716984098099051 / 200000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1800036210497 / 4000000000000 : ℚ))
      (s := (3969910036156129 / 10000000000000000 : ℚ))
      (q := (7970613749913629 / 20000000000000000 : ℚ))
      (U := (-(183994155135901900949 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_420_7 :
    Uω (aρ 7) (bρ 7) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(9828601241911390730523 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7484783918439749 / 20000000000000000 : ℝ) ≤
      (-(9828601241911390730523 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7484783918439749 / 20000000000000000 : ℚ))
        (r' := (7484783918439749 / 5000000000000000 : ℚ))
        (U := (-(9828601241911390730523 / 10000000000000000000000 : ℚ)))
        (U' := (4034342364088609269477 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (1800036210497 / 4000000000000 : ℚ))
      (s := (3707741585442249 / 10000000000000000 : ℚ))
      (q := (7484783918439749 / 20000000000000000 : ℚ))
      (U := (-(9828601241911390730523 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_420_8 :
    Uω (aρ 8) (bρ 8) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(1073020264259629767199 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3419741037623649 / 10000000000000000 : ℝ) ≤
      (-(1073020264259629767199 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3419741037623649 / 10000000000000000 : ℚ))
        (r' := (3419741037623649 / 2500000000000000 : ℚ))
        (U := (-(1073020264259629767199 / 1000000000000000000000 : ℚ)))
        (U' := (313274096340370232801 / 1000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (1800036210497 / 4000000000000 : ℚ))
      (s := (1672990696794899 / 5000000000000000 : ℚ))
      (q := (3419741037623649 / 10000000000000000 : ℚ))
      (U := (-(1073020264259629767199 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_420_9 :
    Uω (aρ 9) (bρ 9) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(12034183515403065078679 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (120066552720337 / 400000000000000 : ℝ) ≤
      (-(12034183515403065078679 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (120066552720337 / 400000000000000 : ℚ))
        (r' := (120066552720337 / 100000000000000 : ℚ))
        (U := (-(12034183515403065078679 / 10000000000000000000000 : ℚ)))
        (U' := (1828760090596934921321 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (1800036210497 / 4000000000000 : ℚ))
      (s := (57015851654387 / 200000000000000 : ℚ))
      (q := (120066552720337 / 400000000000000 : ℚ))
      (U := (-(12034183515403065078679 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_420_10 :
    Uω (aρ 10) (bρ 10) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(561315799852319578607 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4915742317110657 / 20000000000000000 : ℝ) ≤
      (-(561315799852319578607 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4915742317110657 / 20000000000000000 : ℚ))
        (r' := (4915742317110657 / 2500000000000000 : ℚ))
        (U := (-(561315799852319578607 / 400000000000000000000 : ℚ)))
        (U' := (270460816507680421393 / 400000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (1800036210497 / 4000000000000 : ℚ))
      (s := (2151766297308157 / 10000000000000000 : ℚ))
      (q := (4915742317110657 / 20000000000000000 : ℚ))
      (U := (-(561315799852319578607 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_420_11 :
    Uω (aρ 11) (bρ 11) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(18094246652620039559979 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3274966393514093 / 20000000000000000 : ℝ) ≤
      (-(18094246652620039559979 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3274966393514093 / 20000000000000000 : ℚ))
        (r' := (3274966393514093 / 2500000000000000 : ℚ))
        (U := (-(18094246652620039559979 / 10000000000000000000000 : ℚ)))
        (U' := (2700168756379960440021 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (1800036210497 / 4000000000000 : ℚ))
      (s := (929466999916593 / 10000000000000000 : ℚ))
      (q := (3274966393514093 / 20000000000000000 : ℚ))
      (U := (-(18094246652620039559979 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_420_12 :
    Uω (aρ 12) (bρ 12) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_420_13 :
    Uω (aρ 13) (bρ 13) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_420_14 :
    Uω (aρ 14) (bρ 14) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_420_15 :
    Uω (aρ 15) (bρ 15) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_420_16 :
    Uω (aρ 16) (bρ 16) (1800036210497 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_420 :
    Uρ (1800036210497 / 4000000000000 : ℝ) ≤
      (-(5981627919399893279119 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_420_1 U_420_2 U_420_3 U_420_4 U_420_5 U_420_6 U_420_7 U_420_8 U_420_9 U_420_10
    U_420_11 U_420_12 U_420_13 U_420_14 U_420_15 U_420_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_421_1 :
    Uω (aρ 1) (bρ 1) (7210739241 / 16000000000 : ℝ) ≤
      (-(8114402026328109846991 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1776871365484197 / 4000000000000000 : ℝ) ≤
      (-(8114402026328109846991 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1776871365484197 / 4000000000000000 : ℚ))
        (r' := (1776871365484197 / 1000000000000000 : ℚ))
        (U := (-(8114402026328109846991 / 10000000000000000000000 : ℚ)))
        (U' := (5748541579671890153009 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (7210739241 / 16000000000 : ℚ))
      (s := (888428403976197 / 2000000000000000 : ℚ))
      (q := (1776871365484197 / 4000000000000000 : ℚ))
      (U := (-(8114402026328109846991 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_421_2 :
    Uω (aρ 2) (bρ 2) (7210739241 / 16000000000 : ℝ) ≤
      (-(4084257180438267317039 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4418205668821777 / 10000000000000000 : ℝ) ≤
      (-(4084257180438267317039 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4418205668821777 / 10000000000000000 : ℚ))
        (r' := (4418205668821777 / 2500000000000000 : ℚ))
        (U := (-(4084257180438267317039 / 5000000000000000000000 : ℚ)))
        (U' := (2847214622561732682961 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (7210739241 / 16000000000 : ℚ))
      (s := (2208982771306777 / 5000000000000000 : ℚ))
      (q := (4418205668821777 / 10000000000000000 : ℚ))
      (U := (-(4084257180438267317039 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_421_3 :
    Uω (aρ 3) (bρ 3) (7210739241 / 16000000000 : ℝ) ≤
      (-(8277755705431535785367 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1748081306306361 / 4000000000000000 : ℝ) ≤
      (-(8277755705431535785367 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1748081306306361 / 4000000000000000 : ℚ))
        (r' := (1748081306306361 / 1000000000000000 : ℚ))
        (U := (-(8277755705431535785367 / 10000000000000000000000 : ℚ)))
        (U' := (5585187900568464214633 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (7210739241 / 16000000000 : ℚ))
      (s := (873871368570361 / 2000000000000000 : ℚ))
      (q := (1748081306306361 / 4000000000000000 : ℚ))
      (U := (-(8277755705431535785367 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_421_4 :
    Uω (aρ 4) (bρ 4) (7210739241 / 16000000000 : ℝ) ≤
      (-(67698212214232369843 / 80000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4290303343137727 / 10000000000000000 : ℝ) ≤
      (-(67698212214232369843 / 80000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4290303343137727 / 10000000000000000 : ℚ))
        (r' := (4290303343137727 / 2500000000000000 : ℚ))
        (U := (-(67698212214232369843 / 80000000000000000000 : ℚ)))
        (U' := (43205336633767630157 / 80000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (7210739241 / 16000000000 : ℚ))
      (s := (2143925589330227 / 5000000000000000 : ℚ))
      (q := (4290303343137727 / 10000000000000000 : ℚ))
      (U := (-(67698212214232369843 / 80000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_421_5 :
    Uω (aρ 5) (bρ 5) (7210739241 / 16000000000 : ℝ) ≤
      (-(8751063036737577972069 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (52102213481619 / 125000000000000 : ℝ) ≤
      (-(8751063036737577972069 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (52102213481619 / 125000000000000 : ℚ))
        (r' := (52102213481619 / 31250000000000 : ℚ))
        (U := (-(8751063036737577972069 / 10000000000000000000000 : ℚ)))
        (U' := (5111880569262422027931 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (7210739241 / 16000000000 : ℚ))
      (s := (26011178554869 / 62500000000000 : ℚ))
      (q := (52102213481619 / 125000000000000 : ℚ))
      (U := (-(8751063036737577972069 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_421_6 :
    Uω (aρ 6) (bρ 6) (7210739241 / 16000000000 : ℝ) ≤
      (-(2295760635244161997167 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (798390802426913 / 2000000000000000 : ℝ) ≤
      (-(2295760635244161997167 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (798390802426913 / 2000000000000000 : ℚ))
        (r' := (798390802426913 / 500000000000000 : ℚ))
        (U := (-(2295760635244161997167 / 2500000000000000000000 : ℚ)))
        (U' := (1169975266255838002833 / 2500000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (7210739241 / 16000000000 : ℚ))
      (s := (397658281112913 / 1000000000000000 : ℚ))
      (q := (798390802426913 / 2000000000000000 : ℚ))
      (U := (-(2295760635244161997167 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_421_7 :
    Uω (aρ 7) (bρ 7) (7210739241 / 16000000000 : ℝ) ≤
      (-(306586215248868418239 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7498150455807673 / 20000000000000000 : ℝ) ≤
      (-(306586215248868418239 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7498150455807673 / 20000000000000000 : ℚ))
        (r' := (7498150455807673 / 5000000000000000 : ℚ))
        (U := (-(306586215248868418239 / 312500000000000000000 : ℚ)))
        (U' := (126630772438631581761 / 312500000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (7210739241 / 16000000000 : ℚ))
      (s := (3714486623427673 / 10000000000000000 : ℚ))
      (q := (7498150455807673 / 20000000000000000 : ℚ))
      (U := (-(306586215248868418239 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_421_8 :
    Uω (aρ 8) (bρ 8) (7210739241 / 16000000000 : ℝ) ≤
      (-(1338804206099587571027 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (685301641672891 / 2000000000000000 : ℝ) ≤
      (-(1338804206099587571027 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (685301641672891 / 2000000000000000 : ℚ))
        (r' := (685301641672891 / 500000000000000 : ℚ))
        (U := (-(1338804206099587571027 / 1250000000000000000000 : ℚ)))
        (U' := (394063744650412428973 / 1250000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (7210739241 / 16000000000 : ℚ))
      (s := (335289423568891 / 1000000000000000 : ℚ))
      (q := (685301641672891 / 2000000000000000 : ℚ))
      (U := (-(1338804206099587571027 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_421_9 :
    Uω (aρ 9) (bρ 9) (7210739241 / 16000000000 : ℝ) ≤
      (-(12010986417487087268443 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1203453955705317 / 4000000000000000 : ℝ) ≤
      (-(12010986417487087268443 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1203453955705317 / 4000000000000000 : ℚ))
        (r' := (1203453955705317 / 1000000000000000 : ℚ))
        (U := (-(12010986417487087268443 / 10000000000000000000000 : ℚ)))
        (U' := (1851957188512912731557 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (7210739241 / 16000000000 : ℚ))
      (s := (571622645169317 / 2000000000000000 : ℚ))
      (q := (1203453955705317 / 4000000000000000 : ℚ))
      (U := (-(12010986417487087268443 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_421_10 :
    Uω (aρ 10) (bρ 10) (7210739241 / 16000000000 : ℝ) ≤
      (-(350054580804219201741 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2465431317835013 / 10000000000000000 : ℝ) ≤
      (-(350054580804219201741 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2465431317835013 / 10000000000000000 : ℚ))
        (r' := (2465431317835013 / 1250000000000000 : ℚ))
        (U := (-(350054580804219201741 / 250000000000000000000 : ℚ)))
        (U' := (169805804420780798259 / 250000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (7210739241 / 16000000000 : ℚ))
      (s := (1080132558242513 / 5000000000000000 : ℚ))
      (q := (2465431317835013 / 10000000000000000 : ℚ))
      (U := (-(350054580804219201741 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_421_11 :
    Uω (aρ 11) (bρ 11) (7210739241 / 16000000000 : ℝ) ≤
      (-(4505909143362031622123 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (659634558201427 / 4000000000000000 : ℝ) ≤
      (-(4505909143362031622123 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (659634558201427 / 4000000000000000 : ℚ))
        (r' := (659634558201427 / 500000000000000 : ℚ))
        (U := (-(4505909143362031622123 / 2500000000000000000000 : ℚ)))
        (U' := (692694708887968377877 / 2500000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (7210739241 / 16000000000 : ℚ))
      (s := (189210379605427 / 2000000000000000 : ℚ))
      (q := (659634558201427 / 4000000000000000 : ℚ))
      (U := (-(4505909143362031622123 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_421_12 :
    Uω (aρ 12) (bρ 12) (7210739241 / 16000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_421_13 :
    Uω (aρ 13) (bρ 13) (7210739241 / 16000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_421_14 :
    Uω (aρ 14) (bρ 14) (7210739241 / 16000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_421_15 :
    Uω (aρ 15) (bρ 15) (7210739241 / 16000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_421_16 :
    Uω (aρ 16) (bρ 16) (7210739241 / 16000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_421 :
    Uρ (7210739241 / 16000000000 : ℝ) ≤
      (-(11945186561807156496291 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_421_1 U_421_2 U_421_3 U_421_4 U_421_5 U_421_6 U_421_7 U_421_8 U_421_9 U_421_10
    U_421_11 U_421_12 U_421_13 U_421_14 U_421_15 U_421_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_422_1 :
    Uω (aρ 1) (bρ 1) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(2024876757354868561347 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8897599934522477 / 20000000000000000 : ℝ) ≤
      (-(2024876757354868561347 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8897599934522477 / 20000000000000000 : ℚ))
        (r' := (8897599934522477 / 5000000000000000 : ℚ))
        (U := (-(2024876757354868561347 / 2500000000000000000000 : ℚ)))
        (U' := (1440859144145131438653 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1805333410003 / 4000000000000 : ℚ))
      (s := (4448763627599977 / 10000000000000000 : ℚ))
      (q := (8897599934522477 / 20000000000000000 : ℚ))
      (U := (-(2024876757354868561347 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_422_2 :
    Uω (aρ 2) (bρ 2) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(1630707583193492241937 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (442482752755881 / 1000000000000000 : ℝ) ≤
      (-(1630707583193492241937 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (442482752755881 / 1000000000000000 : ℚ))
        (r' := (442482752755881 / 250000000000000 : ℚ))
        (U := (-(1630707583193492241937 / 2000000000000000000000 : ℚ)))
        (U' := (1141881138006507758063 / 2000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1805333410003 / 4000000000000 : ℚ))
      (s := (27653673504407 / 62500000000000 : ℚ))
      (q := (442482752755881 / 1000000000000000 : ℚ))
      (U := (-(1630707583193492241937 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_422_3 :
    Uω (aρ 3) (bρ 3) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(4131306389108922398569 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4376826045910491 / 10000000000000000 : ℝ) ≤
      (-(4131306389108922398569 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4376826045910491 / 10000000000000000 : ℚ))
        (r' := (4376826045910491 / 2500000000000000 : ℚ))
        (U := (-(4131306389108922398569 / 5000000000000000000000 : ℚ)))
        (U' := (2800165413891077601431 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1805333410003 / 4000000000000 : ℚ))
      (s := (2187990451879241 / 5000000000000000 : ℚ))
      (q := (4376826045910491 / 10000000000000000 : ℚ))
      (U := (-(4131306389108922398569 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_422_4 :
    Uω (aρ 4) (bρ 4) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(8446845986117236546949 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2148464311712387 / 5000000000000000 : ℝ) ≤
      (-(8446845986117236546949 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2148464311712387 / 5000000000000000 : ℚ))
        (r' := (2148464311712387 / 1250000000000000 : ℚ))
        (U := (-(8446845986117236546949 / 10000000000000000000000 : ℚ)))
        (U' := (5416097619882763453051 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1805333410003 / 4000000000000 : ℚ))
      (s := (268405014990753 / 625000000000000 : ℚ))
      (q := (2148464311712387 / 5000000000000000 : ℚ))
      (U := (-(8446845986117236546949 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_422_5 :
    Uω (aρ 5) (bρ 5) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(8735165493515219476671 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8349617452008769 / 20000000000000000 : ℝ) ≤
      (-(8735165493515219476671 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8349617452008769 / 20000000000000000 : ℚ))
        (r' := (8349617452008769 / 5000000000000000 : ℚ))
        (U := (-(8735165493515219476671 / 10000000000000000000000 : ℚ)))
        (U' := (5127778112484780523329 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1805333410003 / 4000000000000 : ℚ))
      (s := (4168430364346269 / 10000000000000000 : ℚ))
      (q := (8349617452008769 / 20000000000000000 : ℚ))
      (U := (-(8735165493515219476671 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_422_6 :
    Uω (aρ 6) (bρ 6) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(9166405265891975863527 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7997202127490299 / 20000000000000000 : ℝ) ≤
      (-(9166405265891975863527 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7997202127490299 / 20000000000000000 : ℚ))
        (r' := (7997202127490299 / 5000000000000000 : ℚ))
        (U := (-(9166405265891975863527 / 10000000000000000000000 : ℚ)))
        (U' := (4696538340108024136473 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1805333410003 / 4000000000000 : ℚ))
      (s := (3983255414967799 / 10000000000000000 : ℚ))
      (q := (7997202127490299 / 20000000000000000 : ℚ))
      (U := (-(9166405265891975863527 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_422_7 :
    Uω (aρ 7) (bρ 7) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(4896474451519480225219 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7511516549429117 / 20000000000000000 : ℝ) ≤
      (-(4896474451519480225219 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7511516549429117 / 20000000000000000 : ℚ))
        (r' := (7511516549429117 / 5000000000000000 : ℚ))
        (U := (-(4896474451519480225219 / 5000000000000000000000 : ℚ)))
        (U' := (2034997351480519774781 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (1805333410003 / 4000000000000 : ℚ))
      (s := (3721231217666617 / 10000000000000000 : ℚ))
      (q := (7511516549429117 / 20000000000000000 : ℚ))
      (U := (-(4896474451519480225219 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_422_8 :
    Uω (aρ 8) (bρ 8) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(10690705368396436709341 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1373309916918359 / 4000000000000000 : ℝ) ≤
      (-(10690705368396436709341 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1373309916918359 / 4000000000000000 : ℚ))
        (r' := (1373309916918359 / 1000000000000000 : ℚ))
        (U := (-(10690705368396436709341 / 10000000000000000000000 : ℚ)))
        (U' := (3172238237603563290659 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (1805333410003 / 4000000000000 : ℚ))
      (s := (671961180833859 / 2000000000000000 : ℚ))
      (q := (1373309916918359 / 4000000000000000 : ℚ))
      (U := (-(10690705368396436709341 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_422_9 :
    Uω (aρ 9) (bρ 9) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(5993924322941902594337 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6031208519259153 / 20000000000000000 : ℝ) ≤
      (-(5993924322941902594337 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6031208519259153 / 20000000000000000 : ℚ))
        (r' := (6031208519259153 / 5000000000000000 : ℚ))
        (U := (-(5993924322941902594337 / 5000000000000000000000 : ℚ)))
        (U' := (937547480058097405663 / 5000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (1805333410003 / 4000000000000 : ℚ))
      (s := (2865430467196653 / 10000000000000000 : ℚ))
      (q := (6031208519259153 / 20000000000000000 : ℚ))
      (U := (-(5993924322941902594337 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_422_10 :
    Uω (aρ 10) (bρ 10) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(2794318392676469736287 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (618246233222387 / 2500000000000000 : ℝ) ≤
      (-(2794318392676469736287 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (618246233222387 / 2500000000000000 : ℚ))
        (r' := (618246233222387 / 312500000000000 : ℚ))
        (U := (-(2794318392676469736287 / 2000000000000000000000 : ℚ)))
        (U' := (1364564689123530263713 / 2000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (1805333410003 / 4000000000000 : ℚ))
      (s := (542187711802899 / 2500000000000000 : ℚ))
      (q := (618246233222387 / 2500000000000000 : ℚ))
      (U := (-(2794318392676469736287 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_422_11 :
    Uω (aρ 11) (bρ 11) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(3590848971023895272907 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3321138969712857 / 20000000000000000 : ℝ) ≤
      (-(3590848971023895272907 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3321138969712857 / 20000000000000000 : ℚ))
        (r' := (3321138969712857 / 2500000000000000 : ℚ))
        (U := (-(3590848971023895272907 / 2000000000000000000000 : ℚ)))
        (U' := (568034110776104727093 / 2000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (1805333410003 / 4000000000000 : ℚ))
      (s := (962396577350357 / 10000000000000000 : ℚ))
      (q := (3321138969712857 / 20000000000000000 : ℚ))
      (U := (-(3590848971023895272907 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_422_12 :
    Uω (aρ 12) (bρ 12) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_422_13 :
    Uω (aρ 13) (bρ 13) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_422_14 :
    Uω (aρ 14) (bρ 14) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_422_15 :
    Uω (aρ 15) (bρ 15) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_422_16 :
    Uω (aρ 16) (bρ 16) (1805333410003 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_422 :
    Uρ (1805333410003 / 4000000000000 : ℝ) ≤
      (-(11927242524291849257171 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_422_1 U_422_2 U_422_3 U_422_4 U_422_5 U_422_6 U_422_7 U_422_8 U_422_9 U_422_10
    U_422_11 U_422_12 U_422_13 U_422_14 U_422_15 U_422_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_423_1 :
    Uω (aρ 1) (bρ 1) (451995502439 / 1000000000000 : ℝ) ≤
      (-(4042317092986279800841 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (139231922520343 / 312500000000000 : ℝ) ≤
      (-(4042317092986279800841 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (139231922520343 / 312500000000000 : ℚ))
        (r' := (139231922520343 / 78125000000000 : ℚ))
        (U := (-(4042317092986279800841 / 5000000000000000000000 : ℚ)))
        (U' := (2889154710013720199159 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (451995502439 / 1000000000000 : ℚ))
      (s := (556923154374619 / 1250000000000000 : ℚ))
      (q := (139231922520343 / 312500000000000 : ℚ))
      (U := (-(4042317092986279800841 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_423_2 :
    Uω (aρ 2) (bρ 2) (451995502439 / 1000000000000 : ℝ) ≤
      (-(4069291934667686941101 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1772579754088731 / 4000000000000000 : ℝ) ≤
      (-(4069291934667686941101 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1772579754088731 / 4000000000000000 : ℚ))
        (r' := (1772579754088731 / 1000000000000000 : ℚ))
        (U := (-(4069291934667686941101 / 5000000000000000000000 : ℚ)))
        (U' := (2862179868332313058899 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (451995502439 / 1000000000000 : ℚ))
      (s := (886241995329731 / 2000000000000000 : ℚ))
      (q := (1772579754088731 / 4000000000000000 : ℚ))
      (U := (-(4069291934667686941101 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_423_3 :
    Uω (aρ 3) (bρ 3) (451995502439 / 1000000000000 : ℝ) ≤
      (-(4123746377996051450701 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4383448822184229 / 10000000000000000 : ℝ) ≤
      (-(4123746377996051450701 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4383448822184229 / 10000000000000000 : ℚ))
        (r' := (4383448822184229 / 2500000000000000 : ℚ))
        (U := (-(4123746377996051450701 / 5000000000000000000000 : ℚ)))
        (U' := (2807725425003948549299 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (451995502439 / 1000000000000 : ℚ))
      (s := (2191302478461729 / 5000000000000000 : ℚ))
      (q := (4383448822184229 / 10000000000000000 : ℚ))
      (U := (-(4123746377996051450701 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_423_4 :
    Uω (aρ 4) (bρ 4) (451995502439 / 1000000000000 : ℝ) ≤
      (-(4215719623000383988557 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33621514781749 / 78125000000000 : ℝ) ≤
      (-(4215719623000383988557 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (33621514781749 / 78125000000000 : ℚ))
        (r' := (33621514781749 / 19531250000000 : ℚ))
        (U := (-(4215719623000383988557 / 5000000000000000000000 : ℚ)))
        (U' := (2715752179999616011443 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (451995502439 / 1000000000000 : ℚ))
      (s := (134409664929617 / 312500000000000 : ℚ))
      (q := (33621514781749 / 78125000000000 : ℚ))
      (U := (-(4215719623000383988557 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_423_5 :
    Uω (aρ 5) (bρ 5) (451995502439 / 1000000000000 : ℝ) ≤
      (-(1743858652094064989949 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8362880682481939 / 20000000000000000 : ℝ) ≤
      (-(1743858652094064989949 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8362880682481939 / 20000000000000000 : ℚ))
        (r' := (8362880682481939 / 5000000000000000 : ℚ))
        (U := (-(1743858652094064989949 / 2000000000000000000000 : ℚ)))
        (U' := (1028730069105935010051 / 2000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (451995502439 / 1000000000000 : ℚ))
      (s := (4175072095436939 / 10000000000000000 : ℚ))
      (q := (8362880682481939 / 20000000000000000 : ℚ))
      (U := (-(1743858652094064989949 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_423_6 :
    Uω (aρ 6) (bρ 6) (451995502439 / 1000000000000 : ℝ) ≤
      (-(914979583729635317381 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2002624015108933 / 5000000000000000 : ℝ) ≤
      (-(914979583729635317381 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2002624015108933 / 5000000000000000 : ℚ))
        (r' := (2002624015108933 / 1250000000000000 : ℚ))
        (U := (-(914979583729635317381 / 1000000000000000000000 : ℚ)))
        (U' := (471314776870364682619 / 1000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (451995502439 / 1000000000000 : ℚ))
      (s := (997481962132683 / 2500000000000000 : ℚ))
      (q := (2002624015108933 / 5000000000000000 : ℚ))
      (U := (-(914979583729635317381 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_423_7 :
    Uω (aρ 7) (bρ 7) (451995502439 / 1000000000000 : ℝ) ≤
      (-(9775171167791601484043 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3762441100856269 / 10000000000000000 : ℝ) ≤
      (-(9775171167791601484043 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3762441100856269 / 10000000000000000 : ℚ))
        (r' := (3762441100856269 / 2500000000000000 : ℚ))
        (U := (-(9775171167791601484043 / 10000000000000000000000 : ℚ)))
        (U' := (4087772438208398515957 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (451995502439 / 1000000000000 : ℚ))
      (s := (1863987685283769 / 5000000000000000 : ℚ))
      (q := (3762441100856269 / 10000000000000000 : ℚ))
      (U := (-(9775171167791601484043 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_423_8 :
    Uω (aρ 8) (bρ 8) (451995502439 / 1000000000000 : ℝ) ≤
      (-(1067101762719614924343 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3440040793032031 / 10000000000000000 : ℝ) ≤
      (-(1067101762719614924343 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3440040793032031 / 10000000000000000 : ℚ))
        (r' := (3440040793032031 / 2500000000000000 : ℚ))
        (U := (-(1067101762719614924343 / 1000000000000000000000 : ℚ)))
        (U' := (319192597880385075657 / 1000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (451995502439 / 1000000000000 : ℚ))
      (s := (1683358203129531 / 5000000000000000 : ℚ))
      (q := (3440040793032031 / 10000000000000000 : ℚ))
      (U := (-(1067101762719614924343 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_423_9 :
    Uω (aρ 9) (bρ 9) (451995502439 / 1000000000000 : ℝ) ≤
      (-(239295397413106100289 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6045143884208817 / 20000000000000000 : ℝ) ≤
      (-(239295397413106100289 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6045143884208817 / 20000000000000000 : ℚ))
        (r' := (6045143884208817 / 5000000000000000 : ℚ))
        (U := (-(239295397413106100289 / 200000000000000000000 : ℚ)))
        (U' := (37963474706893899711 / 200000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (451995502439 / 1000000000000 : ℚ))
      (s := (2872744332763817 / 10000000000000000 : ℚ))
      (q := (6045143884208817 / 20000000000000000 : ℚ))
      (U := (-(239295397413106100289 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_423_10 :
    Uω (aρ 10) (bρ 10) (451995502439 / 1000000000000 : ℝ) ≤
      (-(6970560032833848866531 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2480532080237303 / 10000000000000000 : ℝ) ≤
      (-(6970560032833848866531 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2480532080237303 / 10000000000000000 : ℚ))
        (r' := (2480532080237303 / 1250000000000000 : ℚ))
        (U := (-(6970560032833848866531 / 5000000000000000000000 : ℚ)))
        (U' := (3426647671666151133469 / 5000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (451995502439 / 1000000000000 : ℚ))
      (s := (1088611821262303 / 5000000000000000 : ℚ))
      (q := (2480532080237303 / 10000000000000000 : ℚ))
      (U := (-(6970560032833848866531 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_423_11 :
    Uω (aρ 11) (bρ 11) (451995502439 / 1000000000000 : ℝ) ≤
      (-(4471503425795417789409 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (668775393450461 / 4000000000000000 : ℝ) ≤
      (-(4471503425795417789409 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (668775393450461 / 4000000000000000 : ℚ))
        (r' := (668775393450461 / 500000000000000 : ℚ))
        (U := (-(4471503425795417789409 / 2500000000000000000000 : ℚ)))
        (U' := (727100426454582210591 / 2500000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (451995502439 / 1000000000000 : ℚ))
      (s := (195702615101461 / 2000000000000000 : ℚ))
      (q := (668775393450461 / 4000000000000000 : ℚ))
      (U := (-(4471503425795417789409 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_423_12 :
    Uω (aρ 12) (bρ 12) (451995502439 / 1000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_423_13 :
    Uω (aρ 13) (bρ 13) (451995502439 / 1000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_423_14 :
    Uω (aρ 14) (bρ 14) (451995502439 / 1000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_423_15 :
    Uω (aρ 15) (bρ 15) (451995502439 / 1000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_423_16 :
    Uω (aρ 16) (bρ 16) (451995502439 / 1000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_423 :
    Uρ (451995502439 / 1000000000000 : ℝ) ≤
      (-(744338687036184402011 / 625000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_423_1 U_423_2 U_423_3 U_423_4 U_423_5 U_423_6 U_423_7 U_423_8 U_423_9 U_423_10
    U_423_11 U_423_12 U_423_13 U_423_14 U_423_15 U_423_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
