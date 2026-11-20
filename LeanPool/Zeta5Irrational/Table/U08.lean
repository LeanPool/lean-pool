/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U08) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_100_1 :
    Uω (aρ 1) (bρ 1) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(30651298815258709468093 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (373182261801303 / 8000000000000000 : ℝ) ≤
      (-(30651298815258709468093 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (373182261801303 / 8000000000000000 : ℚ))
        (r' := (373182261801303 / 250000000000000 : ℚ))
        (U := (-(30651298815258709468093 / 10000000000000000000000 : ℚ)))
        (U' := (4006060199741290531907 / 10000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1700229173627 / 32000000000000 : ℚ))
      (s := (23306562791491 / 500000000000000 : ℚ))
      (q := (373182261801303 / 8000000000000000 : ℚ))
      (U := (-(30651298815258709468093 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_100_2 :
    Uω (aρ 2) (bρ 2) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(78052365153972182917 / 25000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1762590931396799 / 40000000000000000 : ℝ) ≤
      (-(78052365153972182917 / 25000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1762590931396799 / 40000000000000000 : ℚ))
        (r' := (1762590931396799 / 1250000000000000 : ℚ))
        (U := (-(78052365153972182917 / 25000000000000000000 : ℚ)))
        (U' := (8591032383527817083 / 25000000000000000000 : ℚ))
        5 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1700229173627 / 32000000000000 : ℚ))
      (s := (219120039767481 / 5000000000000000 : ℚ))
      (q := (1762590931396799 / 40000000000000000 : ℚ))
      (U := (-(78052365153972182917 / 25000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_100_3 :
    Uω (aρ 3) (bρ 3) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(16271501953539078684187 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1544312862311407 / 40000000000000000 : ℝ) ≤
      (-(16271501953539078684187 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1544312862311407 / 40000000000000000 : ℚ))
        (r' := (1544312862311407 / 1250000000000000 : ℚ))
        (U := (-(16271501953539078684187 / 5000000000000000000000 : ℚ)))
        (U' := (1057177553960921315813 / 5000000000000000000000 : ℚ))
        5 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1700229173627 / 32000000000000 : ℚ))
      (s := (188248575671133 / 5000000000000000 : ℚ))
      (q := (1544312862311407 / 40000000000000000 : ℚ))
      (U := (-(16271501953539078684187 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_100_4 :
    Uω (aρ 4) (bρ 4) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(35764101527639732941787 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1119037901687173 / 40000000000000000 : ℝ) ≤
      (-(35764101527639732941787 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1119037901687173 / 40000000000000000 : ℚ))
        (r' := (1119037901687173 / 625000000000000 : ℚ))
        (U := (-(35764101527639732941787 / 10000000000000000000000 : ℚ)))
        (U' := (5824729290360267058213 / 10000000000000000000000 : ℚ))
        6 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1700229173627 / 32000000000000 : ℚ))
      (s := (242153852095149 / 10000000000000000 : ℚ))
      (q := (1119037901687173 / 40000000000000000 : ℚ))
      (U := (-(35764101527639732941787 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_100_5 :
    Uω (aρ 5) (bρ 5) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_100_6 :
    Uω (aρ 6) (bρ 6) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_100_7 :
    Uω (aρ 7) (bρ 7) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_100_8 :
    Uω (aρ 8) (bρ 8) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_100_9 :
    Uω (aρ 9) (bρ 9) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_100_10 :
    Uω (aρ 10) (bρ 10) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_100_11 :
    Uω (aρ 11) (bρ 11) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_100_12 :
    Uω (aρ 12) (bρ 12) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_100_13 :
    Uω (aρ 13) (bρ 13) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_100_14 :
    Uω (aρ 14) (bρ 14) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_100_15 :
    Uω (aρ 15) (bρ 15) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_100_16 :
    Uω (aρ 16) (bρ 16) (1700229173627 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_100 :
    Uρ (1700229173627 / 32000000000000 : ℝ) ≤
      (-(408736191272622967401 / 156250000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_100_1 U_100_2 U_100_3 U_100_4 U_100_5 U_100_6 U_100_7 U_100_8 U_100_9 U_100_10
    U_100_11 U_100_12 U_100_13 U_100_14 U_100_15 U_100_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_101_1 :
    Uω (aρ 1) (bρ 1) (107760667809 / 2000000000000 : ℝ) ≤
      (-(3049206840087526189059 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9479300486123 / 200000000000000 : ℝ) ≤
      (-(3049206840087526189059 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9479300486123 / 200000000000000 : ℚ))
        (r' := (9479300486123 / 6250000000000 : ℚ))
        (U := (-(3049206840087526189059 / 1000000000000000000000 : ℚ)))
        (U' := (416529061412473810941 / 1000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (107760667809 / 2000000000000 : ℚ))
      (s := (4736239276523 / 100000000000000 : ℚ))
      (q := (9479300486123 / 200000000000000 : ℚ))
      (U := (-(3049206840087526189059 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_101_2 :
    Uω (aρ 2) (bρ 2) (107760667809 / 2000000000000 : ℝ) ≤
      (-(3881460057703866310033 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (89633973091073 / 2000000000000000 : ℝ) ≤
      (-(3881460057703866310033 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (89633973091073 / 2000000000000000 : ℚ))
        (r' := (89633973091073 / 62500000000000 : ℚ))
        (U := (-(3881460057703866310033 / 1250000000000000000000 : ℚ)))
        (U' := (450709819171133689967 / 1250000000000000000000 : ℚ))
        5 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (107760667809 / 2000000000000 : ℚ))
      (s := (44580262246073 / 1000000000000000 : ℚ))
      (q := (89633973091073 / 2000000000000000 : ℚ))
      (U := (-(3881460057703866310033 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_101_3 :
    Uω (aρ 3) (bρ 3) (107760667809 / 2000000000000 : ℝ) ≤
      (-(126352851143046549433 / 39062500000000000000 : ℝ)) := by
  have hlg :
    Real.log (787493063159317 / 20000000000000000 : ℝ) ≤
      (-(126352851143046549433 / 39062500000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (787493063159317 / 20000000000000000 : ℚ))
        (r' := (787493063159317 / 625000000000000 : ℚ))
        (U := (-(126352851143046549433 / 39062500000000000000 : ℚ)))
        (U' := (9027457509297200567 / 39062500000000000000 : ℚ))
        5 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (107760667809 / 2000000000000 : ℚ))
      (s := (384352061059317 / 10000000000000000 : ℚ))
      (q := (787493063159317 / 20000000000000000 : ℚ))
      (U := (-(126352851143046549433 / 39062500000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_101_4 :
    Uω (aρ 4) (bρ 4) (107760667809 / 2000000000000 : ℝ) ≤
      (-(2216324696954452647823 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (288363216890881 / 10000000000000000 : ℝ) ≤
      (-(2216324696954452647823 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (288363216890881 / 10000000000000000 : ℚ))
        (r' := (288363216890881 / 156250000000000 : ℚ))
        (U := (-(2216324696954452647823 / 625000000000000000000 : ℚ)))
        (U' := (382977229170547352177 / 625000000000000000000 : ℚ))
        6 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (107760667809 / 2000000000000 : ℚ))
      (s := (125939806373381 / 5000000000000000 : ℚ))
      (q := (288363216890881 / 10000000000000000 : ℚ))
      (U := (-(2216324696954452647823 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_101_5 :
    Uω (aρ 5) (bρ 5) (107760667809 / 2000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_101_6 :
    Uω (aρ 6) (bρ 6) (107760667809 / 2000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_101_7 :
    Uω (aρ 7) (bρ 7) (107760667809 / 2000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_101_8 :
    Uω (aρ 8) (bρ 8) (107760667809 / 2000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_101_9 :
    Uω (aρ 9) (bρ 9) (107760667809 / 2000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_101_10 :
    Uω (aρ 10) (bρ 10) (107760667809 / 2000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_101_11 :
    Uω (aρ 11) (bρ 11) (107760667809 / 2000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_101_12 :
    Uω (aρ 12) (bρ 12) (107760667809 / 2000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_101_13 :
    Uω (aρ 13) (bρ 13) (107760667809 / 2000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_101_14 :
    Uω (aρ 14) (bρ 14) (107760667809 / 2000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_101_15 :
    Uω (aρ 15) (bρ 15) (107760667809 / 2000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_101_16 :
    Uω (aρ 16) (bρ 16) (107760667809 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_101 :
    Uρ (107760667809 / 2000000000000 : ℝ) ≤
      (-(13063189390197467979439 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_101_1 U_101_2 U_101_3 U_101_4 U_101_5 U_101_6 U_101_7 U_101_8 U_101_9 U_101_10
    U_101_11 U_101_12 U_101_13 U_101_14 U_101_15 U_101_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_102_1 :
    Uω (aρ 1) (bρ 1) (886026853789 / 16000000000000 : ℝ) ≤
      (-(7545257017708016980781 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (488938915059511 / 10000000000000000 : ℝ) ≤
      (-(7545257017708016980781 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (488938915059511 / 10000000000000000 : ℚ))
        (r' := (488938915059511 / 312500000000000 : ℚ))
        (U := (-(7545257017708016980781 / 2500000000000000000000 : ℚ)))
        (U' := (1119082736041983019219 / 2500000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (886026853789 / 16000000000000 : ℚ))
      (s := (488608264585897 / 10000000000000000 : ℚ))
      (q := (488938915059511 / 10000000000000000 : ℚ))
      (U := (-(7545257017708016980781 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_102_2 :
    Uω (aρ 2) (bρ 2) (886026853789 / 16000000000000 : ℝ) ≤
      (-(30721594805733174632861 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (926420347528863 / 20000000000000000 : ℝ) ≤
      (-(30721594805733174632861 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (926420347528863 / 20000000000000000 : ℚ))
        (r' := (926420347528863 / 625000000000000 : ℚ))
        (U := (-(30721594805733174632861 / 10000000000000000000000 : ℚ)))
        (U' := (3935764209266825367139 / 10000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (886026853789 / 16000000000000 : ℚ))
      (s := (230459897252869 / 5000000000000000 : ℚ))
      (q := (926420347528863 / 20000000000000000 : ℚ))
      (U := (-(30721594805733174632861 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_102_3 :
    Uω (aρ 3) (bρ 3) (886026853789 / 16000000000000 : ℝ) ≤
      (-(15982371816390557011147 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10226542571457 / 250000000000000 : ℝ) ≤
      (-(15982371816390557011147 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10226542571457 / 250000000000000 : ℚ))
        (r' := (10226542571457 / 7812500000000 : ℚ))
        (U := (-(15982371816390557011147 / 5000000000000000000000 : ℚ)))
        (U' := (1346307691109442988853 / 5000000000000000000000 : ℚ))
        5 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (886026853789 / 16000000000000 : ℚ))
      (s := (80003791808687 / 2000000000000000 : ℚ))
      (q := (10226542571457 / 250000000000000 : ℚ))
      (U := (-(15982371816390557011147 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_102_4 :
    Uω (aρ 4) (bρ 4) (886026853789 / 16000000000000 : ℝ) ≤
      (-(34888585885879677851941 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (610714120865997 / 20000000000000000 : ℝ) ≤
      (-(34888585885879677851941 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (610714120865997 / 20000000000000000 : ℚ))
        (r' := (610714120865997 / 312500000000000 : ℚ))
        (U := (-(34888585885879677851941 / 10000000000000000000000 : ℚ)))
        (U' := (6700244932120322148059 / 10000000000000000000000 : ℚ))
        6 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (886026853789 / 16000000000000 : ℚ))
      (s := (16931490953617 / 625000000000000 : ℚ))
      (q := (610714120865997 / 20000000000000000 : ℚ))
      (U := (-(34888585885879677851941 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_102_5 :
    Uω (aρ 5) (bρ 5) (886026853789 / 16000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_102_6 :
    Uω (aρ 6) (bρ 6) (886026853789 / 16000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_102_7 :
    Uω (aρ 7) (bρ 7) (886026853789 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_102_8 :
    Uω (aρ 8) (bρ 8) (886026853789 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_102_9 :
    Uω (aρ 9) (bρ 9) (886026853789 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_102_10 :
    Uω (aρ 10) (bρ 10) (886026853789 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_102_11 :
    Uω (aρ 11) (bρ 11) (886026853789 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_102_12 :
    Uω (aρ 12) (bρ 12) (886026853789 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_102_13 :
    Uω (aρ 13) (bρ 13) (886026853789 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_102_14 :
    Uω (aρ 14) (bρ 14) (886026853789 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_102_15 :
    Uω (aρ 15) (bρ 15) (886026853789 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_102_16 :
    Uω (aρ 16) (bρ 16) (886026853789 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_102 :
    Uρ (886026853789 / 16000000000000 : ℝ) ≤
      (-(26063668361683246214947 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_102_1 U_102_2 U_102_3 U_102_4 U_102_5 U_102_6 U_102_7 U_102_8 U_102_9 U_102_10
    U_102_11 U_102_12 U_102_13 U_102_14 U_102_15 U_102_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_103_1 :
    Uω (aρ 1) (bρ 1) (454984182553 / 8000000000000 : ℝ) ≤
      (-(14939691773495747728407 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (31494511537239 / 625000000000000 : ℝ) ≤
      (-(14939691773495747728407 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (31494511537239 / 625000000000000 : ℚ))
        (r' := (31494511537239 / 19531250000000 : ℚ))
        (U := (-(14939691773495747728407 / 5000000000000000000000 : ℚ)))
        (U' := (2388987734004252271593 / 5000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (454984182553 / 8000000000000 : ℚ))
      (s := (251795679542699 / 5000000000000000 : ℚ))
      (q := (31494511537239 / 625000000000000 : ℚ))
      (U := (-(14939691773495747728407 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_103_2 :
    Uω (aρ 2) (bρ 2) (454984182553 / 8000000000000 : ℝ) ≤
      (-(7600539775674981056863 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (478245625030189 / 10000000000000000 : ℝ) ≤
      (-(7600539775674981056863 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (478245625030189 / 10000000000000000 : ℚ))
        (r' := (478245625030189 / 312500000000000 : ℚ))
        (U := (-(7600539775674981056863 / 2500000000000000000000 : ℚ)))
        (U' := (1063799978075018943137 / 2500000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (454984182553 / 8000000000000 : ℚ))
      (s := (929740727469 / 19531250000000 : ℚ))
      (q := (478245625030189 / 10000000000000000 : ℚ))
      (U := (-(7600539775674981056863 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_103_3 :
    Uω (aρ 3) (bρ 3) (454984182553 / 8000000000000 : ℝ) ≤
      (-(1974862208469201710963 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (848701910179767 / 20000000000000000 : ℝ) ≤
      (-(1974862208469201710963 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (848701910179767 / 20000000000000000 : ℚ))
        (r' := (848701910179767 / 625000000000000 : ℚ))
        (U := (-(1974862208469201710963 / 625000000000000000000 : ℚ)))
        (U' := (191222729968298289037 / 625000000000000000000 : ℚ))
        5 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (454984182553 / 8000000000000 : ℚ))
      (s := (415634018933517 / 10000000000000000 : ℚ))
      (q := (848701910179767 / 20000000000000000 : ℚ))
      (U := (-(1974862208469201710963 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_103_4 :
    Uω (aρ 4) (bρ 4) (454984182553 / 8000000000000 : ℝ) ≤
      (-(17177194607766529470513 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (322112688666289 / 10000000000000000 : ℝ) ≤
      (-(17177194607766529470513 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (322112688666289 / 10000000000000000 : ℚ))
        (r' := (322112688666289 / 312500000000000 : ℚ))
        (U := (-(17177194607766529470513 / 5000000000000000000000 : ℚ)))
        (U' := (151484899733470529487 / 5000000000000000000000 : ℚ))
        5 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (454984182553 / 8000000000000 : ℚ))
      (s := (9045364598479 / 312500000000000 : ℚ))
      (q := (322112688666289 / 10000000000000000 : ℚ))
      (U := (-(17177194607766529470513 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_103_5 :
    Uω (aρ 5) (bρ 5) (454984182553 / 8000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_103_6 :
    Uω (aρ 6) (bρ 6) (454984182553 / 8000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_103_7 :
    Uω (aρ 7) (bρ 7) (454984182553 / 8000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_103_8 :
    Uω (aρ 8) (bρ 8) (454984182553 / 8000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_103_9 :
    Uω (aρ 9) (bρ 9) (454984182553 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_103_10 :
    Uω (aρ 10) (bρ 10) (454984182553 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_103_11 :
    Uω (aρ 11) (bρ 11) (454984182553 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_103_12 :
    Uω (aρ 12) (bρ 12) (454984182553 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_103_13 :
    Uω (aρ 13) (bρ 13) (454984182553 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_103_14 :
    Uω (aρ 14) (bρ 14) (454984182553 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_103_15 :
    Uω (aρ 15) (bρ 15) (454984182553 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_103_16 :
    Uω (aρ 16) (bρ 16) (454984182553 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_103 :
    Uρ (454984182553 / 8000000000000 : ℝ) ≤
      (-(26004234865315178925071 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_103_1 U_103_2 U_103_3 U_103_4 U_103_5 U_103_6 U_103_7 U_103_8 U_103_9 U_103_10
    U_103_11 U_103_12 U_103_13 U_103_14 U_103_15 U_103_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_104_1 :
    Uω (aρ 1) (bρ 1) (47892569387 / 800000000000 : ℝ) ≤
      (-(3662765284919319541649 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (533857069350801 / 10000000000000000 : ℝ) ≤
      (-(3662765284919319541649 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (533857069350801 / 10000000000000000 : ℚ))
        (r' := (533857069350801 / 312500000000000 : ℚ))
        (U := (-(3662765284919319541649 / 1250000000000000000000 : ℚ)))
        (U' := (669404591955680458351 / 1250000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (47892569387 / 800000000000 : ℚ))
      (s := (266777119724551 / 5000000000000000 : ℚ))
      (q := (533857069350801 / 10000000000000000 : ℚ))
      (U := (-(3662765284919319541649 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_104_2 :
    Uω (aρ 2) (bρ 2) (47892569387 / 800000000000 : ℝ) ≤
      (-(3724076594691395072657 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (508303695593581 / 10000000000000000 : ℝ) ≤
      (-(3724076594691395072657 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (508303695593581 / 10000000000000000 : ℚ))
        (r' := (508303695593581 / 312500000000000 : ℚ))
        (U := (-(3724076594691395072657 / 1250000000000000000000 : ℚ)))
        (U' := (608093282183604927343 / 1250000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (47892569387 / 800000000000 : ℚ))
      (s := (253108252222331 / 5000000000000000 : ℚ))
      (q := (508303695593581 / 10000000000000000 : ℚ))
      (U := (-(3724076594691395072657 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_104_3 :
    Uω (aρ 3) (bρ 3) (47892569387 / 800000000000 : ℝ) ≤
      (-(6180690102931800358943 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (181945026151459 / 4000000000000000 : ℝ) ≤
      (-(6180690102931800358943 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (181945026151459 / 4000000000000000 : ℚ))
        (r' := (181945026151459 / 125000000000000 : ℚ))
        (U := (-(6180690102931800358943 / 2000000000000000000000 : ℚ)))
        (U' := (750781700068199641057 / 2000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (47892569387 / 800000000000 : ℚ))
      (s := (89346070072959 / 2000000000000000 : ℚ))
      (q := (181945026151459 / 4000000000000000 : ℚ))
      (U := (-(6180690102931800358943 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_104_4 :
    Uω (aρ 4) (bρ 4) (47892569387 / 800000000000 : ℝ) ≤
      (-(33380218915095679924057 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (710142503980007 / 20000000000000000 : ℝ) ≤
      (-(33380218915095679924057 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (710142503980007 / 20000000000000000 : ℚ))
        (r' := (710142503980007 / 625000000000000 : ℚ))
        (U := (-(33380218915095679924057 / 10000000000000000000000 : ℚ)))
        (U' := (1277140099904320075943 / 10000000000000000000000 : ℚ))
        5 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (47892569387 / 800000000000 : ℚ))
      (s := (325441904652507 / 10000000000000000 : ℚ))
      (q := (710142503980007 / 20000000000000000 : ℚ))
      (U := (-(33380218915095679924057 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_104_5 :
    Uω (aρ 5) (bρ 5) (47892569387 / 800000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_104_6 :
    Uω (aρ 6) (bρ 6) (47892569387 / 800000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_104_7 :
    Uω (aρ 7) (bρ 7) (47892569387 / 800000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_104_8 :
    Uω (aρ 8) (bρ 8) (47892569387 / 800000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_104_9 :
    Uω (aρ 9) (bρ 9) (47892569387 / 800000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_104_10 :
    Uω (aρ 10) (bρ 10) (47892569387 / 800000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_104_11 :
    Uω (aρ 11) (bρ 11) (47892569387 / 800000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_104_12 :
    Uω (aρ 12) (bρ 12) (47892569387 / 800000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_104_13 :
    Uω (aρ 13) (bρ 13) (47892569387 / 800000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_104_14 :
    Uω (aρ 14) (bρ 14) (47892569387 / 800000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_104_15 :
    Uω (aρ 15) (bρ 15) (47892569387 / 800000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_104_16 :
    Uω (aρ 16) (bρ 16) (47892569387 / 800000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_104 :
    Uρ (47892569387 / 800000000000 : ℝ) ≤
      (-(25893688140692916112373 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_104_1 U_104_2 U_104_3 U_104_4 U_104_5 U_104_6 U_104_7 U_104_8 U_104_9 U_104_10
    U_104_11 U_104_12 U_104_13 U_104_14 U_104_15 U_104_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_105_1 :
    Uω (aρ 1) (bρ 1) (502867205187 / 8000000000000 : ℝ) ≤
      (-(7189101795739181296169 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1127600083104993 / 20000000000000000 : ℝ) ≤
      (-(7189101795739181296169 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1127600083104993 / 20000000000000000 : ℚ))
        (r' := (1127600083104993 / 625000000000000 : ℚ))
        (U := (-(7189101795739181296169 / 2500000000000000000000 : ℚ)))
        (U' := (1475237958010818703831 / 2500000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (502867205187 / 8000000000000 : ℚ))
      (s := (563513294706243 / 10000000000000000 : ℚ))
      (q := (1127600083104993 / 20000000000000000 : ℚ))
      (U := (-(7189101795739181296169 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_105_2 :
    Uω (aρ 2) (bρ 2) (502867205187 / 8000000000000 : ℝ) ≤
      (-(1826148073864402492947 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1076694127943669 / 20000000000000000 : ℝ) ≤
      (-(1826148073864402492947 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1076694127943669 / 20000000000000000 : ℚ))
        (r' := (1076694127943669 / 625000000000000 : ℚ))
        (U := (-(1826148073864402492947 / 625000000000000000000 : ℚ)))
        (U' := (339936864573097507053 / 625000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (502867205187 / 8000000000000 : ℚ))
      (s := (536376352054919 / 10000000000000000 : ℚ))
      (q := (1076694127943669 / 20000000000000000 : ℚ))
      (U := (-(1826148073864402492947 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_105_3 :
    Uω (aρ 3) (bρ 3) (502867205187 / 8000000000000 : ℝ) ≤
      (-(1210229666652526991207 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (970598978574067 / 20000000000000000 : ℝ) ≤
      (-(1210229666652526991207 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (970598978574067 / 20000000000000000 : ℚ))
        (r' := (970598978574067 / 625000000000000 : ℚ))
        (U := (-(1210229666652526991207 / 400000000000000000000 : ℚ)))
        (U' := (176064693947473008793 / 400000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (502867205187 / 8000000000000 : ℚ))
      (s := (477677309035317 / 10000000000000000 : ℚ))
      (q := (970598978574067 / 20000000000000000 : ℚ))
      (U := (-(1210229666652526991207 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_105_4 :
    Uω (aρ 4) (bρ 4) (502867205187 / 8000000000000 : ℝ) ≤
      (-(16253431555359706555137 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (38747605742901 / 1000000000000000 : ℝ) ≤
      (-(16253431555359706555137 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (38747605742901 / 1000000000000000 : ℚ))
        (r' := (38747605742901 / 31250000000000 : ℚ))
        (U := (-(16253431555359706555137 / 5000000000000000000000 : ℚ)))
        (U' := (1075247952140293444863 / 5000000000000000000000 : ℚ))
        5 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (502867205187 / 8000000000000 : ℚ))
      (s := (36032462638427 / 1000000000000000 : ℚ))
      (q := (38747605742901 / 1000000000000000 : ℚ))
      (U := (-(16253431555359706555137 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_105_5 :
    Uω (aρ 5) (bρ 5) (502867205187 / 8000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_105_6 :
    Uω (aρ 6) (bρ 6) (502867205187 / 8000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_105_7 :
    Uω (aρ 7) (bρ 7) (502867205187 / 8000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_105_8 :
    Uω (aρ 8) (bρ 8) (502867205187 / 8000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_105_9 :
    Uω (aρ 9) (bρ 9) (502867205187 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_105_10 :
    Uω (aρ 10) (bρ 10) (502867205187 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_105_11 :
    Uω (aρ 11) (bρ 11) (502867205187 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_105_12 :
    Uω (aρ 12) (bρ 12) (502867205187 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_105_13 :
    Uω (aρ 13) (bρ 13) (502867205187 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_105_14 :
    Uω (aρ 14) (bρ 14) (502867205187 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_105_15 :
    Uω (aρ 15) (bρ 15) (502867205187 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_105_16 :
    Uω (aρ 16) (bρ 16) (502867205187 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_105 :
    Uρ (502867205187 / 8000000000000 : ℝ) ≤
      (-(1289619184650899952501 / 500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_105_1 U_105_2 U_105_3 U_105_4 U_105_5 U_105_6 U_105_7 U_105_8 U_105_9 U_105_10
    U_105_11 U_105_12 U_105_13 U_105_14 U_105_15 U_105_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_106_1 :
    Uω (aρ 1) (bρ 1) (65851089563 / 1000000000000 : ℝ) ≤
      (-(28238965150618197558677 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1187482781690451 / 20000000000000000 : ℝ) ≤
      (-(28238965150618197558677 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1187482781690451 / 20000000000000000 : ℚ))
        (r' := (1187482781690451 / 625000000000000 : ℚ))
        (U := (-(28238965150618197558677 / 10000000000000000000000 : ℚ)))
        (U' := (6418393864381802441323 / 10000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (65851089563 / 1000000000000 : ℚ))
      (s := (593469104145451 / 10000000000000000 : ℚ))
      (q := (1187482781690451 / 20000000000000000 : ℚ))
      (U := (-(28238965150618197558677 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_106_2 :
    Uω (aρ 2) (bρ 2) (65851089563 / 1000000000000 : ℝ) ≤
      (-(28675535425575934481119 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (568378078312381 / 10000000000000000 : ℝ) ≤
      (-(28675535425575934481119 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (568378078312381 / 10000000000000000 : ℚ))
        (r' := (568378078312381 / 312500000000000 : ℚ))
        (U := (-(28675535425575934481119 / 10000000000000000000000 : ℚ)))
        (U' := (5981823589424065518881 / 10000000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (65851089563 / 1000000000000 : ℚ))
      (s := (283255745794881 / 5000000000000000 : ℚ))
      (q := (568378078312381 / 10000000000000000 : ℚ))
      (U := (-(28675535425575934481119 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_106_3 :
    Uω (aρ 3) (bρ 3) (65851089563 / 1000000000000 : ℝ) ≤
      (-(29648629442586589394293 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1031350726414239 / 20000000000000000 : ℝ) ≤
      (-(29648629442586589394293 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1031350726414239 / 20000000000000000 : ℚ))
        (r' := (1031350726414239 / 625000000000000 : ℚ))
        (U := (-(29648629442586589394293 / 10000000000000000000000 : ℚ)))
        (U' := (5008729572413410605707 / 10000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (65851089563 / 1000000000000 : ℚ))
      (s := (508502167729239 / 10000000000000000 : ℚ))
      (q := (1031350726414239 / 20000000000000000 : ℚ))
      (U := (-(29648629442586589394293 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_106_4 :
    Uω (aρ 4) (bρ 4) (65851089563 / 1000000000000 : ℝ) ≤
      (-(7928346505977301990569 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (419474093477657 / 10000000000000000 : ℝ) ≤
      (-(7928346505977301990569 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (419474093477657 / 10000000000000000 : ℚ))
        (r' := (419474093477657 / 312500000000000 : ℚ))
        (U := (-(7928346505977301990569 / 2500000000000000000000 : ℚ)))
        (U' := (735993247772698009431 / 2500000000000000000000 : ℚ))
        5 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (65851089563 / 1000000000000 : ℚ))
      (s := (197196904667657 / 5000000000000000 : ℚ))
      (q := (419474093477657 / 10000000000000000 : ℚ))
      (U := (-(7928346505977301990569 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_106_5 :
    Uω (aρ 5) (bρ 5) (65851089563 / 1000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_106_6 :
    Uω (aρ 6) (bρ 6) (65851089563 / 1000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_106_7 :
    Uω (aρ 7) (bρ 7) (65851089563 / 1000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_106_8 :
    Uω (aρ 8) (bρ 8) (65851089563 / 1000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_106_9 :
    Uω (aρ 9) (bρ 9) (65851089563 / 1000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_106_10 :
    Uω (aρ 10) (bρ 10) (65851089563 / 1000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_106_11 :
    Uω (aρ 11) (bρ 11) (65851089563 / 1000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_106_12 :
    Uω (aρ 12) (bρ 12) (65851089563 / 1000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_106_13 :
    Uω (aρ 13) (bρ 13) (65851089563 / 1000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_106_14 :
    Uω (aρ 14) (bρ 14) (65851089563 / 1000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_106_15 :
    Uω (aρ 15) (bρ 15) (65851089563 / 1000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_106_16 :
    Uω (aρ 16) (bρ 16) (65851089563 / 1000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_106 :
    Uρ (65851089563 / 1000000000000 : ℝ) ≤
      (-(25698694525139896448587 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_106_1 U_106_2 U_106_3 U_106_4 U_106_5 U_106_6 U_106_7 U_106_8 U_106_9 U_106_10
    U_106_11 U_106_12 U_106_13 U_106_14 U_106_15 U_106_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_107_1 :
    Uω (aρ 1) (bρ 1) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(7015858174040562655969 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (483404390005741 / 8000000000000000 : ℝ) ≤
      (-(7015858174040562655969 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (483404390005741 / 8000000000000000 : ℚ))
        (r' := (483404390005741 / 250000000000000 : ℚ))
        (U := (-(7015858174040562655969 / 2500000000000000000000 : ℚ)))
        (U' := (1648481579709437344031 / 2500000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2140864814337 / 32000000000000 : ℚ))
      (s := (3774924616369 / 62500000000000 : ℚ))
      (q := (483404390005741 / 8000000000000000 : ℚ))
      (U := (-(7015858174040562655969 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_107_2 :
    Uω (aρ 2) (bρ 2) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(3561466998880705627953 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (463137145245269 / 8000000000000000 : ℝ) ≤
      (-(3561466998880705627953 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (463137145245269 / 8000000000000000 : ℚ))
        (r' := (463137145245269 / 250000000000000 : ℚ))
        (U := (-(3561466998880705627953 / 1250000000000000000000 : ℚ)))
        (U' := (770702877994294372047 / 1250000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2140864814337 / 32000000000000 : ℚ))
      (s := (28854441961393 / 500000000000000 : ℚ))
      (q := (463137145245269 / 8000000000000000 : ℚ))
      (U := (-(3561466998880705627953 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_107_3 :
    Uω (aρ 3) (bρ 3) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(14722060556063304097267 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (421063944006301 / 8000000000000000 : ℝ) ≤
      (-(14722060556063304097267 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (421063944006301 / 8000000000000000 : ℚ))
        (r' := (421063944006301 / 250000000000000 : ℚ))
        (U := (-(14722060556063304097267 / 5000000000000000000000 : ℚ)))
        (U' := (2606618951436695902733 / 5000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2140864814337 / 32000000000000 : ℚ))
      (s := (12982548562011 / 250000000000000 : ℚ))
      (q := (421063944006301 / 8000000000000000 : ℚ))
      (U := (-(14722060556063304097267 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_107_4 :
    Uω (aρ 4) (bρ 4) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(6290166566300702968681 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1722533495644141 / 40000000000000000 : ℝ) ≤
      (-(6290166566300702968681 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1722533495644141 / 40000000000000000 : ℚ))
        (r' := (1722533495644141 / 1250000000000000 : ℚ))
        (U := (-(6290166566300702968681 / 2000000000000000000000 : ℚ)))
        (U' := (641305236699297031319 / 2000000000000000000000 : ℚ))
        5 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2140864814337 / 32000000000000 : ℚ))
      (s := (203101505675879 / 5000000000000000 : ℚ))
      (q := (1722533495644141 / 40000000000000000 : ℚ))
      (U := (-(6290166566300702968681 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_107_5 :
    Uω (aρ 5) (bρ 5) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(38623722698065706631519 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (840723189842747 / 40000000000000000 : ℝ) ≤
      (-(38623722698065706631519 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (840723189842747 / 40000000000000000 : ℚ))
        (r' := (840723189842747 / 625000000000000 : ℚ))
        (U := (-(38623722698065706631519 / 10000000000000000000000 : ℚ)))
        (U' := (2965108119934293368481 / 10000000000000000000000 : ℚ))
        6 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2140864814337 / 32000000000000 : ℚ))
      (s := (83487777786061 / 10000000000000000 : ℚ))
      (q := (840723189842747 / 40000000000000000 : ℚ))
      (U := (-(38623722698065706631519 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_107_6 :
    Uω (aρ 6) (bρ 6) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_107_7 :
    Uω (aρ 7) (bρ 7) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_107_8 :
    Uω (aρ 8) (bρ 8) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_107_9 :
    Uω (aρ 9) (bρ 9) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_107_10 :
    Uω (aρ 10) (bρ 10) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_107_11 :
    Uω (aρ 11) (bρ 11) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_107_12 :
    Uω (aρ 12) (bρ 12) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_107_13 :
    Uω (aρ 13) (bρ 13) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_107_14 :
    Uω (aρ 14) (bρ 14) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_107_15 :
    Uω (aρ 15) (bρ 15) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_107_16 :
    Uω (aρ 16) (bρ 16) (2140864814337 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_107 :
    Uρ (2140864814337 / 32000000000000 : ℝ) ≤
      (-(12746317531850535099639 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_107_1 U_107_2 U_107_3 U_107_4 U_107_5 U_107_6 U_107_7 U_107_8 U_107_9 U_107_10
    U_107_11 U_107_12 U_107_13 U_107_14 U_107_15 U_107_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_108_1 :
    Uω (aρ 1) (bρ 1) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(13945465483393786464533 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1229538844085863 / 20000000000000000 : ℝ) ≤
      (-(13945465483393786464533 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1229538844085863 / 20000000000000000 : ℚ))
        (r' := (1229538844085863 / 625000000000000 : ℚ))
        (U := (-(13945465483393786464533 / 5000000000000000000000 : ℚ)))
        (U' := (3383214024106213535467 / 5000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1087247381329 / 16000000000000 : ℚ))
      (s := (307253224420119 / 5000000000000000 : ℚ))
      (q := (1229538844085863 / 20000000000000000 : ℚ))
      (U := (-(13945465483393786464533 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_108_2 :
    Uω (aρ 2) (bρ 2) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(14155637296061263611593 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1178927130014927 / 20000000000000000 : ℝ) ≤
      (-(14155637296061263611593 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1178927130014927 / 20000000000000000 : ℚ))
        (r' := (1178927130014927 / 625000000000000 : ℚ))
        (U := (-(14155637296061263611593 / 5000000000000000000000 : ℚ)))
        (U' := (3173042211438736388407 / 5000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1087247381329 / 16000000000000 : ℚ))
      (s := (293831873639651 / 5000000000000000 : ℚ))
      (q := (1178927130014927 / 20000000000000000 : ℚ))
      (U := (-(14155637296061263611593 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_108_3 :
    Uω (aρ 3) (bρ 3) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(29243820169079584143899 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1073957319292933 / 20000000000000000 : ℝ) ≤
      (-(29243820169079584143899 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1073957319292933 / 20000000000000000 : ℚ))
        (r' := (1073957319292933 / 625000000000000 : ℚ))
        (U := (-(29243820169079584143899 / 10000000000000000000000 : ℚ)))
        (U' := (5413538845920415856101 / 10000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1087247381329 / 16000000000000 : ℚ))
      (s := (132522510726827 / 2500000000000000 : ℚ))
      (q := (1073957319292933 / 20000000000000000 : ℚ))
      (U := (-(29243820169079584143899 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_108_4 :
    Uω (aρ 4) (bρ 4) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(31195782612954482994049 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (883515901536191 / 20000000000000000 : ℝ) ≤
      (-(31195782612954482994049 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (883515901536191 / 20000000000000000 : ℚ))
        (r' := (883515901536191 / 625000000000000 : ℚ))
        (U := (-(31195782612954482994049 / 10000000000000000000000 : ℚ)))
        (U' := (3461576402045517005951 / 10000000000000000000000 : ℚ))
        5 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1087247381329 / 16000000000000 : ℚ))
      (s := (208971403107783 / 5000000000000000 : ℚ))
      (q := (883515901536191 / 20000000000000000 : ℚ))
      (U := (-(31195782612954482994049 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_108_5 :
    Uω (aρ 5) (bρ 5) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(1174524119975398790487 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (466384484071707 / 20000000000000000 : ℝ) ≤
      (-(1174524119975398790487 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (466384484071707 / 20000000000000000 : ℚ))
        (r' := (466384484071707 / 312500000000000 : ℚ))
        (U := (-(1174524119975398790487 / 312500000000000000000 : ℚ)))
        (U' := (125126843087101209513 / 312500000000000000000 : ℚ))
        6 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1087247381329 / 16000000000000 : ℚ))
      (s := (59500654043041 / 5000000000000000 : ℚ))
      (q := (466384484071707 / 20000000000000000 : ℚ))
      (U := (-(1174524119975398790487 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_108_6 :
    Uω (aρ 6) (bρ 6) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_108_7 :
    Uω (aρ 7) (bρ 7) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_108_8 :
    Uω (aρ 8) (bρ 8) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_108_9 :
    Uω (aρ 9) (bρ 9) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_108_10 :
    Uω (aρ 10) (bρ 10) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_108_11 :
    Uω (aρ 11) (bρ 11) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_108_12 :
    Uω (aρ 12) (bρ 12) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_108_13 :
    Uω (aρ 13) (bρ 13) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_108_14 :
    Uω (aρ 14) (bρ 14) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_108_15 :
    Uω (aρ 15) (bρ 15) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_108_16 :
    Uω (aρ 16) (bρ 16) (1087247381329 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_108 :
    Uρ (1087247381329 / 16000000000000 : ℝ) ≤
      (-(25390331102288743661441 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_108_1 U_108_2 U_108_3 U_108_4 U_108_5 U_108_6 U_108_7 U_108_8 U_108_9 U_108_10
    U_108_11 U_108_12 U_108_13 U_108_14 U_108_15 U_108_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_109_1 :
    Uω (aρ 1) (bρ 1) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(13860678498047024113487 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2501132810550933 / 40000000000000000 : ℝ) ≤
      (-(13860678498047024113487 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2501132810550933 / 40000000000000000 : ℚ))
        (r' := (2501132810550933 / 2500000000000000 : ℚ))
        (U := (-(13860678498047024113487 / 5000000000000000000000 : ℚ)))
        (U' := (2265107952975886513 / 5000000000000000000000 : ℚ))
        4 2 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2208124710979 / 32000000000000 : ℚ))
      (s := (625024651179529 / 10000000000000000 : ℚ))
      (q := (2501132810550933 / 40000000000000000 : ℚ))
      (U := (-(13860678498047024113487 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_109_2 :
    Uω (aρ 2) (bρ 2) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(7033507858092569809221 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2400018173404683 / 40000000000000000 : ℝ) ≤
      (-(7033507858092569809221 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2400018173404683 / 40000000000000000 : ℚ))
        (r' := (2400018173404683 / 1250000000000000 : ℚ))
        (U := (-(7033507858092569809221 / 2500000000000000000000 : ℚ)))
        (U' := (1630831895657430190779 / 2500000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2208124710979 / 32000000000000 : ℚ))
      (s := (149559086279101 / 2500000000000000 : ℚ))
      (q := (2400018173404683 / 40000000000000000 : ℚ))
      (U := (-(7033507858092569809221 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_109_3 :
    Uω (aρ 3) (bρ 3) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(29047552827988840937373 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2190487605624223 / 40000000000000000 : ℝ) ≤
      (-(29047552827988840937373 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2190487605624223 / 40000000000000000 : ℚ))
        (r' := (2190487605624223 / 1250000000000000 : ℚ))
        (U := (-(29047552827988840937373 / 10000000000000000000000 : ℚ)))
        (U' := (5609806187011159062627 / 10000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2208124710979 / 32000000000000 : ℚ))
      (s := (270433583788087 / 5000000000000000 : ℚ))
      (q := (2190487605624223 / 40000000000000000 : ℚ))
      (U := (-(29047552827988840937373 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_109_4 :
    Uω (aρ 4) (bρ 4) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(7736944871340474206587 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1811402676018173 / 40000000000000000 : ℝ) ≤
      (-(7736944871340474206587 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1811402676018173 / 40000000000000000 : ℚ))
        (r' := (1811402676018173 / 1250000000000000 : ℚ))
        (U := (-(7736944871340474206587 / 2500000000000000000000 : ℚ)))
        (U' := (927394882409525793413 / 2500000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2208124710979 / 32000000000000 : ℚ))
      (s := (429618883838149 / 10000000000000000 : ℚ))
      (q := (1811402676018173 / 40000000000000000 : ℚ))
      (U := (-(7736944871340474206587 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_109_5 :
    Uω (aρ 5) (bρ 5) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(36793825325521051304251 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1009542158843399 / 40000000000000000 : ℝ) ≤
      (-(36793825325521051304251 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1009542158843399 / 40000000000000000 : ℚ))
        (r' := (1009542158843399 / 625000000000000 : ℚ))
        (U := (-(36793825325521051304251 / 10000000000000000000000 : ℚ)))
        (U' := (4795005492478948695749 / 10000000000000000000000 : ℚ))
        6 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2208124710979 / 32000000000000 : ℚ))
      (s := (73439272292881 / 5000000000000000 : ℚ))
      (q := (1009542158843399 / 40000000000000000 : ℚ))
      (U := (-(36793825325521051304251 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_109_6 :
    Uω (aρ 6) (bρ 6) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_109_7 :
    Uω (aρ 7) (bρ 7) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_109_8 :
    Uω (aρ 8) (bρ 8) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_109_9 :
    Uω (aρ 9) (bρ 9) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_109_10 :
    Uω (aρ 10) (bρ 10) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_109_11 :
    Uω (aρ 11) (bρ 11) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_109_12 :
    Uω (aρ 12) (bρ 12) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_109_13 :
    Uω (aρ 13) (bρ 13) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_109_14 :
    Uω (aρ 14) (bρ 14) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_109_15 :
    Uω (aρ 15) (bρ 15) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_109_16 :
    Uω (aρ 16) (bρ 16) (2208124710979 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_109 :
    Uρ (2208124710979 / 32000000000000 : ℝ) ≤
      (-(5061171551165133003801 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_109_1 U_109_2 U_109_3 U_109_4 U_109_5 U_109_6 U_109_7 U_109_8 U_109_9 U_109_10
    U_109_11 U_109_12 U_109_13 U_109_14 U_109_15 U_109_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_110_1 :
    Uω (aρ 1) (bρ 1) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(3454704645218149241057 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5044320300925587 / 80000000000000000 : ℝ) ≤
      (-(3454704645218149241057 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5044320300925587 / 80000000000000000 : ℚ))
        (r' := (5044320300925587 / 5000000000000000 : ℚ))
        (U := (-(3454704645218149241057 / 1250000000000000000000 : ℚ)))
        (U' := (11031256281850758943 / 1250000000000000000000 : ℚ))
        4 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4449879370279 / 64000000000000 : ℚ))
      (s := (630283641710303 / 10000000000000000 : ℚ))
      (q := (5044320300925587 / 80000000000000000 : ℚ))
      (U := (-(3454704645218149241057 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_110_2 :
    Uω (aρ 2) (bρ 2) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(28046581010402783172551 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4842196946632063 / 80000000000000000 : ℝ) ≤
      (-(28046581010402783172551 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4842196946632063 / 80000000000000000 : ℚ))
        (r' := (4842196946632063 / 2500000000000000 : ℚ))
        (U := (-(28046581010402783172551 / 10000000000000000000000 : ℚ)))
        (U' := (6610778004597216827449 / 10000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4449879370279 / 64000000000000 : ℚ))
      (s := (301760907823461 / 5000000000000000 : ℚ))
      (q := (4842196946632063 / 80000000000000000 : ℚ))
      (U := (-(28046581010402783172551 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_110_3 :
    Uω (aρ 3) (bρ 3) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(28950880422802094840081 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4423532526790299 / 80000000000000000 : ℝ) ≤
      (-(28950880422802094840081 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4423532526790299 / 80000000000000000 : ℚ))
        (r' := (4423532526790299 / 2500000000000000 : ℚ))
        (U := (-(28950880422802094840081 / 10000000000000000000000 : ℚ)))
        (U' := (5706478592197905159919 / 10000000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4449879370279 / 64000000000000 : ℚ))
      (s := (546251817036481 / 10000000000000000 : ℚ))
      (q := (4423532526790299 / 80000000000000000 : ℚ))
      (U := (-(28950880422802094840081 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_110_4 :
    Uω (aρ 4) (bρ 4) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(30826290029214530827127 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3667087060613467 / 80000000000000000 : ℝ) ≤
      (-(30826290029214530827127 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3667087060613467 / 80000000000000000 : ℚ))
        (r' := (3667087060613467 / 2500000000000000 : ℚ))
        (U := (-(30826290029214530827127 / 10000000000000000000000 : ℚ)))
        (U' := (3831068985785469172873 / 10000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4449879370279 / 64000000000000 : ℚ))
      (s := (435434631557273 / 10000000000000000 : ℚ))
      (q := (3667087060613467 / 80000000000000000 : ℚ))
      (U := (-(30826290029214530827127 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_110_5 :
    Uω (aρ 5) (bρ 5) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(36450498271319145357943 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (417921732650731 / 16000000000000000 : ℝ) ≤
      (-(36450498271319145357943 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (417921732650731 / 16000000000000000 : ℚ))
        (r' := (417921732650731 / 250000000000000 : ℚ))
        (U := (-(36450498271319145357943 / 10000000000000000000000 : ℚ)))
        (U' := (5138332546680854642057 / 10000000000000000000000 : ℚ))
        6 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4449879370279 / 64000000000000 : ℚ))
      (s := (497671723601 / 31250000000000 : ℚ))
      (q := (417921732650731 / 16000000000000000 : ℚ))
      (U := (-(36450498271319145357943 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_110_6 :
    Uω (aρ 6) (bρ 6) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_110_7 :
    Uω (aρ 7) (bρ 7) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_110_8 :
    Uω (aρ 8) (bρ 8) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_110_9 :
    Uω (aρ 9) (bρ 9) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_110_10 :
    Uω (aρ 10) (bρ 10) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_110_11 :
    Uω (aρ 11) (bρ 11) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_110_12 :
    Uω (aρ 12) (bρ 12) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_110_13 :
    Uω (aρ 13) (bρ 13) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_110_14 :
    Uω (aρ 14) (bρ 14) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_110_15 :
    Uω (aρ 15) (bρ 15) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_110_16 :
    Uω (aρ 16) (bρ 16) (4449879370279 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_110 :
    Uρ (4449879370279 / 64000000000000 : ℝ) ≤
      (-(12633737911984751501131 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_110_1 U_110_2 U_110_3 U_110_4 U_110_5 U_110_6 U_110_7 U_110_8 U_110_9 U_110_10
    U_110_11 U_110_12 U_110_13 U_110_14 U_110_15 U_110_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_111_1 :
    Uω (aρ 1) (bρ 1) (22417546593 / 320000000000 : ℝ) ≤
      (-(27554612974095860072559 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (63579683693473 / 1000000000000000 : ℝ) ≤
      (-(27554612974095860072559 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (63579683693473 / 1000000000000000 : ℚ))
        (r' := (63579683693473 / 62500000000000 : ℚ))
        (U := (-(27554612974095860072559 / 10000000000000000000000 : ℚ)))
        (U' := (171274237904139927441 / 10000000000000000000000 : ℚ))
        4 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (22417546593 / 320000000000 : ℚ))
      (s := (63554256092321 / 1000000000000000 : ℚ))
      (q := (63579683693473 / 1000000000000000 : ℚ))
      (U := (-(27554612974095860072559 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_111_2 :
    Uω (aρ 2) (bρ 2) (22417546593 / 320000000000 : ℝ) ≤
      (-(2795989308656552345633 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (610544426766827 / 10000000000000000 : ℝ) ≤
      (-(2795989308656552345633 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (610544426766827 / 10000000000000000 : ℚ))
        (r' := (610544426766827 / 312500000000000 : ℚ))
        (U := (-(2795989308656552345633 / 1000000000000000000000 : ℚ)))
        (U' := (669746592843447654367 / 1000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (22417546593 / 320000000000 : ℚ))
      (s := (152201688274351 / 2500000000000000 : ℚ))
      (q := (610544426766827 / 10000000000000000 : ℚ))
      (U := (-(2795989308656552345633 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_111_3 :
    Uω (aρ 3) (bρ 3) (22417546593 / 320000000000 : ℝ) ≤
      (-(14427578041578170897611 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1116519953864983 / 20000000000000000 : ℝ) ≤
      (-(14427578041578170897611 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1116519953864983 / 20000000000000000 : ℚ))
        (r' := (1116519953864983 / 625000000000000 : ℚ))
        (U := (-(14427578041578170897611 / 5000000000000000000000 : ℚ)))
        (U' := (2901101465921829102389 / 5000000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (22417546593 / 320000000000 : ℚ))
      (s := (551633959778733 / 10000000000000000 : ℚ))
      (q := (1116519953864983 / 20000000000000000 : ℚ))
      (U := (-(14427578041578170897611 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_111_4 :
    Uω (aρ 4) (bρ 4) (22417546593 / 320000000000 : ℝ) ≤
      (-(3838301319880865820711 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (927828115562441 / 20000000000000000 : ℝ) ≤
      (-(3838301319880865820711 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (927828115562441 / 20000000000000000 : ℚ))
        (r' := (927828115562441 / 625000000000000 : ℚ))
        (U := (-(3838301319880865820711 / 1250000000000000000000 : ℚ)))
        (U' := (493868556994134179289 / 1250000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (22417546593 / 320000000000 : ℚ))
      (s := (441236302541191 / 10000000000000000 : ℚ))
      (q := (927828115562441 / 20000000000000000 : ℚ))
      (U := (-(3838301319880865820711 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_111_5 :
    Uω (aρ 5) (bρ 5) (22417546593 / 320000000000 : ℝ) ≤
      (-(36132153701588461327473 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (134825024062817 / 5000000000000000 : ℝ) ≤
      (-(36132153701588461327473 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (134825024062817 / 5000000000000000 : ℚ))
        (r' := (134825024062817 / 78125000000000 : ℚ))
        (U := (-(36132153701588461327473 / 10000000000000000000000 : ℚ)))
        (U' := (5456677116411538672527 / 10000000000000000000000 : ℚ))
        6 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (22417546593 / 320000000000 : ℚ))
      (s := (85449101282509 / 5000000000000000 : ℚ))
      (q := (134825024062817 / 5000000000000000 : ℚ))
      (U := (-(36132153701588461327473 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_111_6 :
    Uω (aρ 6) (bρ 6) (22417546593 / 320000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_111_7 :
    Uω (aρ 7) (bρ 7) (22417546593 / 320000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_111_8 :
    Uω (aρ 8) (bρ 8) (22417546593 / 320000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_111_9 :
    Uω (aρ 9) (bρ 9) (22417546593 / 320000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_111_10 :
    Uω (aρ 10) (bρ 10) (22417546593 / 320000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_111_11 :
    Uω (aρ 11) (bρ 11) (22417546593 / 320000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_111_12 :
    Uω (aρ 12) (bρ 12) (22417546593 / 320000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_111_13 :
    Uω (aρ 13) (bρ 13) (22417546593 / 320000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_111_14 :
    Uω (aρ 14) (bρ 14) (22417546593 / 320000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_111_15 :
    Uω (aρ 15) (bρ 15) (22417546593 / 320000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_111_16 :
    Uω (aρ 16) (bρ 16) (22417546593 / 320000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_111 :
    Uρ (22417546593 / 320000000000 : ℝ) ≤
      (-(25230982823289889081561 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_111_1 U_111_2 U_111_3 U_111_4 U_111_5 U_111_6 U_111_7 U_111_8 U_111_9 U_111_10
    U_111_11 U_111_12 U_111_13 U_111_14 U_111_15 U_111_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
