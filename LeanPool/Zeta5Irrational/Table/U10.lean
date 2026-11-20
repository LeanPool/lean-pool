/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U10) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_124_1 :
    Uω (aρ 1) (bρ 1) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(13399246969653145294021 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10971756942039611 / 160000000000000000 : ℝ) ≤
      (-(13399246969653145294021 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10971756942039611 / 160000000000000000 : ℚ))
        (r' := (10971756942039611 / 10000000000000000 : ℚ))
        (U := (-(13399246969653145294021 / 5000000000000000000000 : ℚ)))
        (U' := (463696636346854705979 / 5000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (9605987655299 / 128000000000000 : ℚ))
      (s := (685499050269717 / 10000000000000000 : ℚ))
      (q := (10971756942039611 / 160000000000000000 : ℚ))
      (U := (-(13399246969653145294021 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_124_2 :
    Uω (aρ 2) (bρ 2) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(27171986109213034869943 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2113905724869911 / 32000000000000000 : ℝ) ≤
      (-(27171986109213034869943 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2113905724869911 / 32000000000000000 : ℚ))
        (r' := (2113905724869911 / 2000000000000000 : ℚ))
        (U := (-(27171986109213034869943 / 10000000000000000000000 : ℚ)))
        (U' := (553901102786965130057 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (9605987655299 / 128000000000000 : ℚ))
      (s := (32949476153423 / 500000000000000 : ℚ))
      (q := (2113905724869911 / 32000000000000000 : ℚ))
      (U := (-(27171986109213034869943 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_124_3 :
    Uω (aρ 3) (bρ 3) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(13994837736555882275651 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9739660556868003 / 160000000000000000 : ℝ) ≤
      (-(13994837736555882275651 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9739660556868003 / 160000000000000000 : ℚ))
        (r' := (9739660556868003 / 5000000000000000 : ℚ))
        (U := (-(13994837736555882275651 / 5000000000000000000000 : ℚ)))
        (U' := (3333841770944117724349 / 5000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (9605987655299 / 128000000000000 : ℚ))
      (s := (301326060491633 / 5000000000000000 : ℚ))
      (q := (9739660556868003 / 160000000000000000 : ℚ))
      (U := (-(13994837736555882275651 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_124_4 :
    Uω (aρ 4) (bρ 4) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(14819930885633522672703 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8258043018870651 / 160000000000000000 : ℝ) ≤
      (-(14819930885633522672703 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8258043018870651 / 160000000000000000 : ℚ))
        (r' := (8258043018870651 / 5000000000000000 : ℚ))
        (U := (-(14819930885633522672703 / 5000000000000000000000 : ℚ)))
        (U' := (2508748621866477327297 / 5000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (9605987655299 / 128000000000000 : ℚ))
      (s := (495744109798597 / 10000000000000000 : ℚ))
      (q := (8258043018870651 / 160000000000000000 : ℚ))
      (U := (-(14819930885633522672703 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_124_5 :
    Uω (aρ 5) (bρ 5) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(16906927768461829373233 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1088010008964823 / 32000000000000000 : ℝ) ≤
      (-(16906927768461829373233 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1088010008964823 / 32000000000000000 : ℚ))
        (r' := (1088010008964823 / 1000000000000000 : ℚ))
        (U := (-(16906927768461829373233 / 5000000000000000000000 : ℚ)))
        (U' := (421751739038170626767 / 5000000000000000000000 : ℚ))
        5 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (9605987655299 / 128000000000000 : ℚ))
      (s := (13084245368889 / 500000000000000 : ℚ))
      (q := (1088010008964823 / 32000000000000000 : ℚ))
      (U := (-(16906927768461829373233 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_124_6 :
    Uω (aρ 6) (bρ 6) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_124_7 :
    Uω (aρ 7) (bρ 7) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_124_8 :
    Uω (aρ 8) (bρ 8) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_124_9 :
    Uω (aρ 9) (bρ 9) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_124_10 :
    Uω (aρ 10) (bρ 10) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_124_11 :
    Uω (aρ 11) (bρ 11) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_124_12 :
    Uω (aρ 12) (bρ 12) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_124_13 :
    Uω (aρ 13) (bρ 13) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_124_14 :
    Uω (aρ 14) (bρ 14) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_124_15 :
    Uω (aρ 15) (bρ 15) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_124_16 :
    Uω (aρ 16) (bρ 16) (9605987655299 / 128000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_124 :
    Uρ (9605987655299 / 128000000000000 : ℝ) ≤
      (-(24940524488693670762209 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_124_1 U_124_2 U_124_3 U_124_4 U_124_5 U_124_6 U_124_7 U_124_8 U_124_9 U_124_10
    U_124_11 U_124_12 U_124_13 U_124_14 U_124_15 U_124_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_125_1 :
    Uω (aρ 1) (bρ 1) (481980880181 / 6400000000000 : ℝ) ≤
      (-(6690059962646030184617 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2753452194961219 / 40000000000000000 : ℝ) ≤
      (-(6690059962646030184617 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2753452194961219 / 40000000000000000 : ℚ))
        (r' := (2753452194961219 / 2500000000000000 : ℚ))
        (U := (-(6690059962646030184617 / 2500000000000000000000 : ℚ)))
        (U' := (241411840353969815383 / 2500000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (481980880181 / 6400000000000 : ℚ))
      (s := (688128190282797 / 10000000000000000 : ℚ))
      (q := (2753452194961219 / 40000000000000000 : ℚ))
      (U := (-(6690059962646030184617 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_125_2 :
    Uω (aρ 2) (bρ 2) (481980880181 / 6400000000000 : ℝ) ≤
      (-(1085287861694982018329 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2652917025223531 / 40000000000000000 : ℝ) ≤
      (-(1085287861694982018329 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2652917025223531 / 40000000000000000 : ℚ))
        (r' := (2652917025223531 / 2500000000000000 : ℚ))
        (U := (-(1085287861694982018329 / 400000000000000000000 : ℚ)))
        (U' := (23747626785017981671 / 400000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (481980880181 / 6400000000000 : ℚ))
      (s := (661629617923953 / 10000000000000000 : ℚ))
      (q := (2652917025223531 / 40000000000000000 : ℚ))
      (U := (-(1085287861694982018329 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_125_3 :
    Uω (aρ 3) (bρ 3) (481980880181 / 6400000000000 : ℝ) ≤
      (-(6986543959626957316373 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2445530001495253 / 40000000000000000 : ℝ) ≤
      (-(6986543959626957316373 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2445530001495253 / 40000000000000000 : ℚ))
        (r' := (2445530001495253 / 1250000000000000 : ℚ))
        (U := (-(6986543959626957316373 / 2500000000000000000000 : ℚ)))
        (U' := (1677795794123042683627 / 2500000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (481980880181 / 6400000000000 : ℚ))
      (s := (302666106204907 / 5000000000000000 : ℚ))
      (q := (2445530001495253 / 40000000000000000 : ℚ))
      (U := (-(6986543959626957316373 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_125_4 :
    Uω (aρ 4) (bρ 4) (481980880181 / 6400000000000 : ℝ) ≤
      (-(1849188452354571814583 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2075449857638049 / 40000000000000000 : ℝ) ≤
      (-(1849188452354571814583 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2075449857638049 / 40000000000000000 : ℚ))
        (r' := (2075449857638049 / 1250000000000000 : ℚ))
        (U := (-(1849188452354571814583 / 625000000000000000000 : ℚ)))
        (U' := (316896486082928185417 / 625000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (481980880181 / 6400000000000 : ℚ))
      (s := (124646580386553 / 2500000000000000 : ℚ))
      (q := (2075449857638049 / 40000000000000000 : ℚ))
      (U := (-(1849188452354571814583 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_125_5 :
    Uω (aρ 5) (bρ 5) (481980880181 / 6400000000000 : ℝ) ≤
      (-(33714249304541786608363 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (274725354828193 / 8000000000000000 : ℝ) ≤
      (-(33714249304541786608363 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (274725354828193 / 8000000000000000 : ℚ))
        (r' := (274725354828193 / 250000000000000 : ℚ))
        (U := (-(33714249304541786608363 / 10000000000000000000000 : ℚ)))
        (U' := (943109710458213391637 / 10000000000000000000000 : ℚ))
        5 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (481980880181 / 6400000000000 : ℚ))
      (s := (26586469913267 / 1000000000000000 : ℚ))
      (q := (274725354828193 / 8000000000000000 : ℚ))
      (U := (-(33714249304541786608363 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_125_6 :
    Uω (aρ 6) (bρ 6) (481980880181 / 6400000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_125_7 :
    Uω (aρ 7) (bρ 7) (481980880181 / 6400000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_125_8 :
    Uω (aρ 8) (bρ 8) (481980880181 / 6400000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_125_9 :
    Uω (aρ 9) (bρ 9) (481980880181 / 6400000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_125_10 :
    Uω (aρ 10) (bρ 10) (481980880181 / 6400000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_125_11 :
    Uω (aρ 11) (bρ 11) (481980880181 / 6400000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_125_12 :
    Uω (aρ 12) (bρ 12) (481980880181 / 6400000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_125_13 :
    Uω (aρ 13) (bρ 13) (481980880181 / 6400000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_125_14 :
    Uω (aρ 14) (bρ 14) (481980880181 / 6400000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_125_15 :
    Uω (aρ 15) (bρ 15) (481980880181 / 6400000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_125_16 :
    Uω (aρ 16) (bρ 16) (481980880181 / 6400000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_125 :
    Uρ (481980880181 / 6400000000000 : ℝ) ≤
      (-(12463564729009360759451 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_125_1 U_125_2 U_125_3 U_125_4 U_125_5 U_125_6 U_125_7 U_125_8 U_125_9 U_125_10
    U_125_11 U_125_12 U_125_13 U_125_14 U_125_15 U_125_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_126_1 :
    Uω (aρ 1) (bρ 1) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(26722131641032751290407 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11055860508051669 / 160000000000000000 : ℝ) ≤
      (-(26722131641032751290407 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11055860508051669 / 160000000000000000 : ℚ))
        (r' := (11055860508051669 / 10000000000000000 : ℚ))
        (U := (-(26722131641032751290407 / 10000000000000000000000 : ℚ)))
        (U' := (1003755570967248709593 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (9673247551941 / 128000000000000 : ℚ))
      (s := (172689329149017 / 2500000000000000 : ℚ))
      (q := (11055860508051669 / 160000000000000000 : ℚ))
      (U := (-(26722131641032751290407 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_126_2 :
    Uω (aρ 2) (bρ 2) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(3386570678593159343237 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10653806768286813 / 160000000000000000 : ℝ) ≤
      (-(3386570678593159343237 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10653806768286813 / 160000000000000000 : ℚ))
        (r' := (10653806768286813 / 10000000000000000 : ℚ))
        (U := (-(3386570678593159343237 / 1250000000000000000000 : ℚ)))
        (U' := (79165222906840656763 / 1250000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (9673247551941 / 128000000000000 : ℚ))
      (s := (664269611635461 / 10000000000000000 : ℚ))
      (q := (10653806768286813 / 160000000000000000 : ℚ))
      (U := (-(3386570678593159343237 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_126_3 :
    Uω (aρ 3) (bρ 3) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(697571708901889533809 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9824575771271253 / 160000000000000000 : ℝ) ≤
      (-(697571708901889533809 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9824575771271253 / 160000000000000000 : ℚ))
        (r' := (9824575771271253 / 5000000000000000 : ℚ))
        (U := (-(697571708901889533809 / 250000000000000000000 : ℚ)))
        (U' := (168862266473110466191 / 250000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (9673247551941 / 128000000000000 : ℚ))
      (s := (152002960839629 / 2500000000000000 : ℚ))
      (q := (9824575771271253 / 160000000000000000 : ℚ))
      (U := (-(697571708901889533809 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_126_4 :
    Uω (aρ 4) (bρ 4) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(2953446897992292134223 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8345537091702853 / 160000000000000000 : ℝ) ≤
      (-(2953446897992292134223 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8345537091702853 / 160000000000000000 : ℚ))
        (r' := (8345537091702853 / 5000000000000000 : ℚ))
        (U := (-(2953446897992292134223 / 1000000000000000000000 : ℚ)))
        (U' := (512289003507707865777 / 1000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (9673247551941 / 128000000000000 : ℚ))
      (s := (250713094738733 / 5000000000000000 : ℚ))
      (q := (8345537091702853 / 160000000000000000 : ℚ))
      (U := (-(2953446897992292134223 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_126_5 :
    Uω (aρ 5) (bρ 5) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(6723237936362052732691 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5548651058829061 / 160000000000000000 : ℝ) ≤
      (-(6723237936362052732691 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5548651058829061 / 160000000000000000 : ℚ))
        (r' := (5548651058829061 / 5000000000000000 : ℚ))
        (U := (-(6723237936362052732691 / 2000000000000000000000 : ℚ)))
        (U' := (208233866637947267309 / 2000000000000000000000 : ℚ))
        5 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (9673247551941 / 128000000000000 : ℚ))
      (s := (135002677351621 / 5000000000000000 : ℚ))
      (q := (5548651058829061 / 160000000000000000 : ℚ))
      (U := (-(6723237936362052732691 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_126_6 :
    Uω (aρ 6) (bρ 6) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_126_7 :
    Uω (aρ 7) (bρ 7) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_126_8 :
    Uω (aρ 8) (bρ 8) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_126_9 :
    Uω (aρ 9) (bρ 9) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_126_10 :
    Uω (aρ 10) (bρ 10) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_126_11 :
    Uω (aρ 11) (bρ 11) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_126_12 :
    Uω (aρ 12) (bρ 12) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_126_13 :
    Uω (aρ 13) (bρ 13) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_126_14 :
    Uω (aρ 14) (bρ 14) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_126_15 :
    Uω (aρ 15) (bρ 15) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_126_16 :
    Uω (aρ 16) (bρ 16) (9673247551941 / 128000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_126 :
    Uρ (9673247551941 / 128000000000000 : ℝ) ≤
      (-(6228468283187341352323 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_126_1 U_126_2 U_126_3 U_126_4 U_126_5 U_126_6 U_126_7 U_126_8 U_126_9 U_126_10
    U_126_11 U_126_12 U_126_13 U_126_14 U_126_15 U_126_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_127_1 :
    Uω (aρ 1) (bρ 1) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(2668416820153121014947 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5548956063953347 / 80000000000000000 : ℝ) ≤
      (-(2668416820153121014947 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5548956063953347 / 80000000000000000 : ℚ))
        (r' := (5548956063953347 / 5000000000000000 : ℚ))
        (U := (-(2668416820153121014947 / 1000000000000000000000 : ℚ)))
        (U' := (104171901046878985053 / 1000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4853438750131 / 64000000000000 : ℚ))
      (s := (86673303670671 / 1250000000000000 : ℚ))
      (q := (5548956063953347 / 80000000000000000 : ℚ))
      (U := (-(2668416820153121014947 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_127_2 :
    Uω (aρ 2) (bρ 2) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(13526545752678102531631 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1069594463613683 / 16000000000000000 : ℝ) ≤
      (-(13526545752678102531631 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1069594463613683 / 16000000000000000 : ℚ))
        (r' := (1069594463613683 / 1000000000000000 : ℚ))
        (U := (-(13526545752678102531631 / 5000000000000000000000 : ℚ)))
        (U' := (336397853321897468369 / 5000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4853438750131 / 64000000000000 : ℚ))
      (s := (133381901080827 / 2000000000000000 : ℚ))
      (q := (1069594463613683 / 16000000000000000 : ℚ))
      (U := (-(13526545752678102531631 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_127_3 :
    Uω (aρ 3) (bρ 3) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(1392987565165561452741 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (986702790123111 / 16000000000000000 : ℝ) ≤
      (-(1392987565165561452741 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (986702790123111 / 16000000000000000 : ℚ))
        (r' := (986702790123111 / 500000000000000 : ℚ))
        (U := (-(1392987565165561452741 / 500000000000000000000 : ℚ)))
        (U' := (339880385584438547259 / 500000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4853438750131 / 64000000000000 : ℚ))
      (s := (15267275497273 / 250000000000000 : ℚ))
      (q := (986702790123111 / 16000000000000000 : ℚ))
      (U := (-(1392987565165561452741 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_127_4 :
    Uω (aρ 4) (bρ 4) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(14741109681724341615633 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4194628159557691 / 80000000000000000 : ℝ) ≤
      (-(14741109681724341615633 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4194628159557691 / 80000000000000000 : ℚ))
        (r' := (4194628159557691 / 2500000000000000 : ℚ))
        (U := (-(14741109681724341615633 / 5000000000000000000000 : ℚ)))
        (U' := (2587569825775658384367 / 5000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4853438750131 / 64000000000000 : ℚ))
      (s := (252131876595727 / 5000000000000000 : ℚ))
      (q := (4194628159557691 / 80000000000000000 : ℚ))
      (U := (-(14741109681724341615633 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_127_5 :
    Uω (aρ 5) (bρ 5) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(33519615797620916311619 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2801248060076399 / 80000000000000000 : ℝ) ≤
      (-(33519615797620916311619 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2801248060076399 / 80000000000000000 : ℚ))
        (r' := (2801248060076399 / 2500000000000000 : ℚ))
        (U := (-(33519615797620916311619 / 10000000000000000000000 : ℚ)))
        (U' := (1137743217379083688381 / 10000000000000000000000 : ℚ))
        5 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4853438750131 / 64000000000000 : ℚ))
      (s := (274108647656131 / 10000000000000000 : ℚ))
      (q := (2801248060076399 / 80000000000000000 : ℚ))
      (U := (-(33519615797620916311619 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_127_6 :
    Uω (aρ 6) (bρ 6) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_127_7 :
    Uω (aρ 7) (bρ 7) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_127_8 :
    Uω (aρ 8) (bρ 8) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_127_9 :
    Uω (aρ 9) (bρ 9) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_127_10 :
    Uω (aρ 10) (bρ 10) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_127_11 :
    Uω (aρ 11) (bρ 11) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_127_12 :
    Uω (aρ 12) (bρ 12) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_127_13 :
    Uω (aρ 13) (bρ 13) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_127_14 :
    Uω (aρ 14) (bρ 14) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_127_15 :
    Uω (aρ 15) (bρ 15) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_127_16 :
    Uω (aρ 16) (bρ 16) (4853438750131 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_127 :
    Uρ (4853438750131 / 64000000000000 : ℝ) ≤
      (-(24900750976102301112917 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_127_1 U_127_2 U_127_3 U_127_4 U_127_5 U_127_6 U_127_7 U_127_8 U_127_9 U_127_10
    U_127_11 U_127_12 U_127_13 U_127_14 U_127_15 U_127_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_128_1 :
    Uω (aρ 1) (bρ 1) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(5321734251810154824021 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (349437970232949 / 5000000000000000 : ℝ) ≤
      (-(5321734251810154824021 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (349437970232949 / 5000000000000000 : ℚ))
        (r' := (349437970232949 / 312500000000000 : ℚ))
        (U := (-(5321734251810154824021 / 2000000000000000000000 : ℚ)))
        (U' := (223443190589845175979 / 2000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1221767174613 / 16000000000000 : ℚ))
      (s := (698644614883671 / 10000000000000000 : ℚ))
      (q := (349437970232949 / 5000000000000000 : ℚ))
      (U := (-(5321734251810154824021 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_128_2 :
    Uω (aρ 2) (bρ 2) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(26974610252730626450719 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (269505450272227 / 4000000000000000 : ℝ) ≤
      (-(26974610252730626450719 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (269505450272227 / 4000000000000000 : ℚ))
        (r' := (269505450272227 / 250000000000000 : ℚ))
        (U := (-(26974610252730626450719 / 10000000000000000000000 : ℚ)))
        (U' := (751276959269373549281 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1221767174613 / 16000000000000 : ℚ))
      (s := (67218899782301 / 1000000000000000 : ℚ))
      (q := (269505450272227 / 4000000000000000 : ℚ))
      (U := (-(26974610252730626450719 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_128_3 :
    Uω (aρ 3) (bρ 3) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(27774081713696468351641 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (621995090304443 / 10000000000000000 : ℝ) ≤
      (-(27774081713696468351641 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (621995090304443 / 10000000000000000 : ℚ))
        (r' := (621995090304443 / 312500000000000 : ℚ))
        (U := (-(27774081713696468351641 / 10000000000000000000000 : ℚ)))
        (U' := (6883277301303531648359 / 10000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1221767174613 / 16000000000000 : ℚ))
      (s := (616048033420761 / 10000000000000000 : ℚ))
      (q := (621995090304443 / 10000000000000000 : ℚ))
      (U := (-(27774081713696468351641 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_128_4 :
    Uω (aρ 4) (bρ 4) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(14689297930419472306447 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1059580087923863 / 20000000000000000 : ℝ) ≤
      (-(14689297930419472306447 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1059580087923863 / 20000000000000000 : ℚ))
        (r' := (1059580087923863 / 625000000000000 : ℚ))
        (U := (-(14689297930419472306447 / 5000000000000000000000 : ℚ)))
        (U' := (2639381577080527693553 / 5000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1221767174613 / 16000000000000 : ℚ))
      (s := (254966060900369 / 5000000000000000 : ℚ))
      (q := (1059580087923863 / 20000000000000000 : ℚ))
      (U := (-(14689297930419472306447 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_128_5 :
    Uω (aρ 5) (bρ 5) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(33330701080104509943517 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (356833848352817 / 10000000000000000 : ℝ) ≤
      (-(33330701080104509943517 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (356833848352817 / 10000000000000000 : ℚ))
        (r' := (356833848352817 / 312500000000000 : ℚ))
        (U := (-(33330701080104509943517 / 10000000000000000000000 : ℚ)))
        (U' := (1326657934895490056483 / 10000000000000000000000 : ℚ))
        5 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1221767174613 / 16000000000000 : ℚ))
      (s := (282209649917509 / 10000000000000000 : ℚ))
      (q := (356833848352817 / 10000000000000000 : ℚ))
      (U := (-(33330701080104509943517 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_128_6 :
    Uω (aρ 6) (bρ 6) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_128_7 :
    Uω (aρ 7) (bρ 7) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_128_8 :
    Uω (aρ 8) (bρ 8) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_128_9 :
    Uω (aρ 9) (bρ 9) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_128_10 :
    Uω (aρ 10) (bρ 10) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_128_11 :
    Uω (aρ 11) (bρ 11) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_128_12 :
    Uω (aρ 12) (bρ 12) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_128_13 :
    Uω (aρ 13) (bρ 13) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_128_14 :
    Uω (aρ 14) (bρ 14) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_128_15 :
    Uω (aρ 15) (bρ 15) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_128_16 :
    Uω (aρ 16) (bρ 16) (1221767174613 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_128 :
    Uρ (1221767174613 / 16000000000000 : ℝ) ≤
      (-(24874892383294093360151 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_128_1 U_128_2 U_128_3 U_128_4 U_128_5 U_128_6 U_128_7 U_128_8 U_128_9 U_128_10
    U_128_11 U_128_12 U_128_13 U_128_14 U_128_15 U_128_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_129_1 :
    Uω (aρ 1) (bρ 1) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(26533740398960545318349 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1126611754809097 / 16000000000000000 : ℝ) ≤
      (-(26533740398960545318349 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1126611754809097 / 16000000000000000 : ℚ))
        (r' := (1126611754809097 / 1000000000000000 : ℚ))
        (U := (-(26533740398960545318349 / 10000000000000000000000 : ℚ)))
        (U' := (1192146813039454681651 / 10000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4920698646773 / 64000000000000 : ℚ))
      (s := (70390274803809 / 1000000000000000 : ℚ))
      (q := (1126611754809097 / 16000000000000000 : ℚ))
      (U := (-(26533740398960545318349 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_129_2 :
    Uω (aρ 2) (bρ 2) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(26896742978634930657697 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5432244149519873 / 80000000000000000 : ℝ) ≤
      (-(26896742978634930657697 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5432244149519873 / 80000000000000000 : ℚ))
        (r' := (5432244149519873 / 5000000000000000 : ℚ))
        (U := (-(26896742978634930657697 / 10000000000000000000000 : ℚ)))
        (U' := (829144233365069342303 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4920698646773 / 64000000000000 : ℚ))
      (s := (677468104416687 / 10000000000000000 : ℚ))
      (q := (5432244149519873 / 80000000000000000 : ℚ))
      (U := (-(26896742978634930657697 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_129_3 :
    Uω (aρ 3) (bρ 3) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(27689153753963773397029 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1003680100806941 / 16000000000000000 : ℝ) ≤
      (-(27689153753963773397029 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1003680100806941 / 16000000000000000 : ℚ))
        (r' := (1003680100806941 / 1000000000000000 : ℚ))
        (U := (-(27689153753963773397029 / 10000000000000000000000 : ℚ)))
        (U' := (36733458036226602971 / 10000000000000000000000 : ℚ))
        4 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4920698646773 / 64000000000000 : ℚ))
      (s := (124280659879079 / 2000000000000000 : ℚ))
      (q := (1003680100806941 / 16000000000000000 : ℚ))
      (U := (-(27689153753963773397029 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_129_4 :
    Uω (aρ 4) (bρ 4) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(14638058503645561336247 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4281977487348057 / 80000000000000000 : ℝ) ≤
      (-(14638058503645561336247 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4281977487348057 / 80000000000000000 : ℚ))
        (r' := (4281977487348057 / 2500000000000000 : ℚ))
        (U := (-(14638058503645561336247 / 5000000000000000000000 : ℚ)))
        (U' := (2690621003854438663753 / 5000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4920698646773 / 64000000000000 : ℚ))
      (s := (515591726288733 / 10000000000000000 : ℚ))
      (q := (4281977487348057 / 80000000000000000 : ℚ))
      (U := (-(14638058503645561336247 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_129_5 :
    Uω (aρ 5) (bρ 5) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(8286772710427584474673 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (581513923481993 / 16000000000000000 : ℝ) ≤
      (-(8286772710427584474673 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (581513923481993 / 16000000000000000 : ℚ))
        (r' := (581513923481993 / 500000000000000 : ℚ))
        (U := (-(8286772710427584474673 / 2500000000000000000000 : ℚ)))
        (U' := (377567043322415525327 / 2500000000000000000000 : ℚ))
        5 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4920698646773 / 64000000000000 : ℚ))
      (s := (29017967813921 / 1000000000000000 : ℚ))
      (q := (581513923481993 / 16000000000000000 : ℚ))
      (U := (-(8286772710427584474673 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_129_6 :
    Uω (aρ 6) (bρ 6) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_129_7 :
    Uω (aρ 7) (bρ 7) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_129_8 :
    Uω (aρ 8) (bρ 8) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_129_9 :
    Uω (aρ 9) (bρ 9) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_129_10 :
    Uω (aρ 10) (bρ 10) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_129_11 :
    Uω (aρ 11) (bρ 11) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_129_12 :
    Uω (aρ 12) (bρ 12) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_129_13 :
    Uω (aρ 13) (bρ 13) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_129_14 :
    Uω (aρ 14) (bρ 14) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_129_15 :
    Uω (aρ 15) (bρ 15) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_129_16 :
    Uω (aρ 16) (bρ 16) (4920698646773 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_129 :
    Uρ (4920698646773 / 64000000000000 : ℝ) ≤
      (-(12424761255821240445021 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_129_1 U_129_2 U_129_3 U_129_4 U_129_5 U_129_6 U_129_7 U_129_8 U_129_9 U_129_10
    U_129_11 U_129_12 U_129_13 U_129_14 U_129_15 U_129_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_130_1 :
    Uω (aρ 1) (bρ 1) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(5291873437976526183487 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2837554909783663 / 40000000000000000 : ℝ) ≤
      (-(5291873437976526183487 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2837554909783663 / 40000000000000000 : ℚ))
        (r' := (2837554909783663 / 2500000000000000 : ℚ))
        (U := (-(5291873437976526183487 / 2000000000000000000000 : ℚ)))
        (U' := (253304004423473816513 / 2000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2477164297547 / 32000000000000 : ℚ))
      (s := (354580414996697 / 5000000000000000 : ℚ))
      (q := (2837554909783663 / 40000000000000000 : ℚ))
      (U := (-(5291873437976526183487 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_130_2 :
    Uω (aρ 2) (bρ 2) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(26819480107653810847137 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2737188893046777 / 40000000000000000 : ℝ) ≤
      (-(26819480107653810847137 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2737188893046777 / 40000000000000000 : ℚ))
        (r' := (2737188893046777 / 2500000000000000 : ℚ))
        (U := (-(26819480107653810847137 / 10000000000000000000000 : ℚ)))
        (U' := (906407104346189152863 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2477164297547 / 32000000000000 : ℚ))
      (s := (682746834134951 / 10000000000000000 : ℚ))
      (q := (2737188893046777 / 40000000000000000 : ℚ))
      (U := (-(26819480107653810847137 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_130_3 :
    Uω (aρ 3) (bρ 3) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(13802477227999504398421 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2530416737297469 / 40000000000000000 : ℝ) ≤
      (-(13802477227999504398421 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2530416737297469 / 40000000000000000 : ℚ))
        (r' := (2530416737297469 / 2500000000000000 : ℚ))
        (U := (-(13802477227999504398421 / 5000000000000000000000 : ℚ)))
        (U' := (60466378000495601579 / 5000000000000000000000 : ℚ))
        4 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2477164297547 / 32000000000000 : ℚ))
      (s := (626756862610297 / 10000000000000000 : ℚ))
      (q := (2530416737297469 / 40000000000000000 : ℚ))
      (U := (-(13802477227999504398421 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_130_4 :
    Uω (aρ 4) (bρ 4) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(5834951221022183615197 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2162800354217801 / 40000000000000000 : ℝ) ≤
      (-(5834951221022183615197 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2162800354217801 / 40000000000000000 : ℚ))
        (r' := (2162800354217801 / 1250000000000000 : ℚ))
        (U := (-(5834951221022183615197 / 2000000000000000000000 : ℚ)))
        (U' := (1096520581977816384803 / 2000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2477164297547 / 32000000000000 : ℚ))
      (s := (521242852135463 / 10000000000000000 : ℚ))
      (q := (2162800354217801 / 40000000000000000 : ℚ))
      (U := (-(5834951221022183615197 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_130_5 :
    Uω (aρ 5) (bρ 5) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(8242104744242823723913 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1479993291679967 / 40000000000000000 : ℝ) ≤
      (-(8242104744242823723913 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1479993291679967 / 40000000000000000 : ℚ))
        (r' := (1479993291679967 / 1250000000000000 : ℚ))
        (U := (-(8242104744242823723913 / 2500000000000000000000 : ℚ)))
        (U' := (422235009507176276087 / 2500000000000000000000 : ℚ))
        5 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2477164297547 / 32000000000000 : ℚ))
      (s := (149014620100773 / 5000000000000000 : ℚ))
      (q := (1479993291679967 / 40000000000000000 : ℚ))
      (U := (-(8242104744242823723913 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_130_6 :
    Uω (aρ 6) (bρ 6) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_130_7 :
    Uω (aρ 7) (bρ 7) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_130_8 :
    Uω (aρ 8) (bρ 8) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_130_9 :
    Uω (aρ 9) (bρ 9) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_130_10 :
    Uω (aρ 10) (bρ 10) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_130_11 :
    Uω (aρ 11) (bρ 11) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_130_12 :
    Uω (aρ 12) (bρ 12) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_130_13 :
    Uω (aρ 13) (bρ 13) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_130_14 :
    Uω (aρ 14) (bρ 14) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_130_15 :
    Uω (aρ 15) (bρ 15) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_130_16 :
    Uω (aρ 16) (bρ 16) (2477164297547 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_130 :
    Uρ (2477164297547 / 32000000000000 : ℝ) ≤
      (-(24824613604535232933069 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_130_1 U_130_2 U_130_3 U_130_4 U_130_5 U_130_6 U_130_7 U_130_8 U_130_9 U_130_10
    U_130_11 U_130_12 U_130_13 U_130_14 U_130_15 U_130_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_131_1 :
    Uω (aρ 1) (bρ 1) (997591708683 / 12800000000000 : ℝ) ≤
      (-(26385543387535192161299 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (228686426592583 / 3200000000000000 : ℝ) ≤
      (-(26385543387535192161299 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (228686426592583 / 3200000000000000 : ℚ))
        (r' := (228686426592583 / 200000000000000 : ℚ))
        (U := (-(26385543387535192161299 / 10000000000000000000000 : ℚ)))
        (U' := (1340343824464807838701 / 10000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (997591708683 / 12800000000000 : ℚ))
      (s := (14288377237601 / 200000000000000 : ℚ))
      (q := (228686426592583 / 3200000000000000 : ℚ))
      (U := (-(26385543387535192161299 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_131_2 :
    Uω (aρ 2) (bρ 2) (997591708683 / 12800000000000 : ℝ) ≤
      (-(1069712491504947096903 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1103301989972711 / 16000000000000000 : ℝ) ≤
      (-(1069712491504947096903 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1103301989972711 / 16000000000000000 : ℚ))
        (r' := (1103301989972711 / 1000000000000000 : ℚ))
        (U := (-(1069712491504947096903 / 400000000000000000000 : ℚ)))
        (U' := (39322996975052903097 / 400000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (997591708683 / 12800000000000 : ℚ))
      (s := (137605039130459 / 2000000000000000 : ℚ))
      (q := (1103301989972711 / 16000000000000000 : ℚ))
      (U := (-(1069712491504947096903 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_131_3 :
    Uω (aρ 3) (bρ 3) (997591708683 / 12800000000000 : ℝ) ≤
      (-(27521471202141578539429 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (326608627659 / 5120000000000 : ℝ) ≤
      (-(27521471202141578539429 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (326608627659 / 5120000000000 : ℚ))
        (r' := (326608627659 / 320000000000 : ℚ))
        (U := (-(27521471202141578539429 / 10000000000000000000000 : ℚ)))
        (U' := (204416009858421460571 / 10000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (997591708683 / 12800000000000 : ℚ))
      (s := (1011374026127 / 16000000000000 : ℚ))
      (q := (326608627659 / 5120000000000 : ℚ))
      (U := (-(27521471202141578539429 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_131_4 :
    Uω (aρ 4) (bρ 4) (997591708683 / 12800000000000 : ℝ) ≤
      (-(1453724371476601447869 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4369191106212779 / 80000000000000000 : ℝ) ≤
      (-(1453724371476601447869 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4369191106212779 / 80000000000000000 : ℚ))
        (r' := (4369191106212779 / 2500000000000000 : ℚ))
        (U := (-(1453724371476601447869 / 500000000000000000000 : ℚ)))
        (U' := (279143579273398552131 / 500000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (997591708683 / 12800000000000 : ℚ))
      (s := (526885772154601 / 10000000000000000 : ℚ))
      (q := (4369191106212779 / 80000000000000000 : ℚ))
      (U := (-(1453724371476601447869 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_131_5 :
    Uω (aρ 5) (bρ 5) (997591708683 / 12800000000000 : ℝ) ≤
      (-(32794360034669585926951 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3011958796030119 / 80000000000000000 : ℝ) ≤
      (-(32794360034669585926951 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3011958796030119 / 80000000000000000 : ℚ))
        (r' := (3011958796030119 / 2500000000000000 : ℚ))
        (U := (-(32794360034669585926951 / 10000000000000000000000 : ℚ)))
        (U' := (1862998980330414073049 / 10000000000000000000000 : ℚ))
        5 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (997591708683 / 12800000000000 : ℚ))
      (s := (2388809483937 / 78125000000000 : ℚ))
      (q := (3011958796030119 / 80000000000000000 : ℚ))
      (U := (-(32794360034669585926951 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_131_6 :
    Uω (aρ 6) (bρ 6) (997591708683 / 12800000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_131_7 :
    Uω (aρ 7) (bρ 7) (997591708683 / 12800000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_131_8 :
    Uω (aρ 8) (bρ 8) (997591708683 / 12800000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_131_9 :
    Uω (aρ 9) (bρ 9) (997591708683 / 12800000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_131_10 :
    Uω (aρ 10) (bρ 10) (997591708683 / 12800000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_131_11 :
    Uω (aρ 11) (bρ 11) (997591708683 / 12800000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_131_12 :
    Uω (aρ 12) (bρ 12) (997591708683 / 12800000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_131_13 :
    Uω (aρ 13) (bρ 13) (997591708683 / 12800000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_131_14 :
    Uω (aρ 14) (bρ 14) (997591708683 / 12800000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_131_15 :
    Uω (aρ 15) (bρ 15) (997591708683 / 12800000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_131_16 :
    Uω (aρ 16) (bρ 16) (997591708683 / 12800000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_131 :
    Uρ (997591708683 / 12800000000000 : ℝ) ≤
      (-(49600281584509713859 / 20000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_131_1 U_131_2 U_131_3 U_131_4 U_131_5 U_131_6 U_131_7 U_131_8 U_131_9 U_131_10
    U_131_11 U_131_12 U_131_13 U_131_14 U_131_15 U_131_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_132_1 :
    Uω (aρ 1) (bρ 1) (627698561467 / 8000000000000 : ℝ) ≤
      (-(5262452185846792494703 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (359950707136057 / 5000000000000000 : ℝ) ≤
      (-(5262452185846792494703 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (359950707136057 / 5000000000000000 : ℚ))
        (r' := (359950707136057 / 312500000000000 : ℚ))
        (U := (-(5262452185846792494703 / 2000000000000000000000 : ℚ)))
        (U' := (282725256553207505297 / 2000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (627698561467 / 8000000000000 : ℚ))
      (s := (359838422397739 / 5000000000000000 : ℚ))
      (q := (359950707136057 / 5000000000000000 : ℚ))
      (U := (-(5262452185846792494703 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_132_2 :
    Uω (aρ 2) (bρ 2) (627698561467 / 8000000000000 : ℝ) ≤
      (-(6666682595679150360093 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1389660168617201 / 20000000000000000 : ℝ) ≤
      (-(6666682595679150360093 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1389660168617201 / 20000000000000000 : ℚ))
        (r' := (1389660168617201 / 1250000000000000 : ℚ))
        (U := (-(6666682595679150360093 / 2500000000000000000000 : ℚ)))
        (U' := (264789207320849639907 / 2500000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (627698561467 / 8000000000000 : ℚ))
      (s := (693303197378451 / 10000000000000000 : ℚ))
      (q := (1389660168617201 / 20000000000000000 : ℚ))
      (U := (-(6666682595679150360093 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_132_3 :
    Uω (aρ 3) (bρ 3) (627698561467 / 8000000000000 : ℝ) ≤
      (-(3429836462828796430307 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (64320995861959 / 1000000000000000 : ℝ) ≤
      (-(3429836462828796430307 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (64320995861959 / 1000000000000000 : ℚ))
        (r' := (64320995861959 / 62500000000000 : ℚ))
        (U := (-(3429836462828796430307 / 1250000000000000000000 : ℚ)))
        (U' := (35899438671203569693 / 1250000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (627698561467 / 8000000000000 : ℚ))
      (s := (63745905235043 / 1000000000000000 : ℚ))
      (q := (64320995861959 / 1000000000000000 : ℚ))
      (U := (-(3429836462828796430307 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_132_4 :
    Uω (aρ 4) (bρ 4) (627698561467 / 8000000000000 : ℝ) ≤
      (-(28975286180128640663519 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1103187431032073 / 20000000000000000 : ℝ) ≤
      (-(28975286180128640663519 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1103187431032073 / 20000000000000000 : ℚ))
        (r' := (1103187431032073 / 625000000000000 : ℚ))
        (U := (-(28975286180128640663519 / 10000000000000000000000 : ℚ)))
        (U' := (5682072834871359336481 / 10000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (627698561467 / 8000000000000 : ℚ))
      (s := (532520747208323 / 10000000000000000 : ℚ))
      (q := (1103187431032073 / 20000000000000000 : ℚ))
      (U := (-(28975286180128640663519 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_132_5 :
    Uω (aρ 5) (bρ 5) (627698561467 / 8000000000000 : ℝ) ≤
      (-(32624623126546358520591 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (95734975020517 / 2500000000000000 : ℝ) ≤
      (-(32624623126546358520591 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (95734975020517 / 2500000000000000 : ℚ))
        (r' := (95734975020517 / 78125000000000 : ℚ))
        (U := (-(32624623126546358520591 / 10000000000000000000000 : ℚ)))
        (U' := (2032735888453641479409 / 10000000000000000000000 : ℚ))
        5 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (627698561467 / 8000000000000 : ℚ))
      (s := (156701517837693 / 5000000000000000 : ℚ))
      (q := (95734975020517 / 2500000000000000 : ℚ))
      (U := (-(32624623126546358520591 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_132_6 :
    Uω (aρ 6) (bρ 6) (627698561467 / 8000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_132_7 :
    Uω (aρ 7) (bρ 7) (627698561467 / 8000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_132_8 :
    Uω (aρ 8) (bρ 8) (627698561467 / 8000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_132_9 :
    Uω (aρ 9) (bρ 9) (627698561467 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_132_10 :
    Uω (aρ 10) (bρ 10) (627698561467 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_132_11 :
    Uω (aρ 11) (bρ 11) (627698561467 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_132_12 :
    Uω (aρ 12) (bρ 12) (627698561467 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_132_13 :
    Uω (aρ 13) (bρ 13) (627698561467 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_132_14 :
    Uω (aρ 14) (bρ 14) (627698561467 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_132_15 :
    Uω (aρ 15) (bρ 15) (627698561467 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_132_16 :
    Uω (aρ 16) (bρ 16) (627698561467 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_132 :
    Uρ (627698561467 / 8000000000000 : ℝ) ≤
      (-(24776081667392410080527 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_132_1 U_132_2 U_132_3 U_132_4 U_132_5 U_132_6 U_132_7 U_132_8 U_132_9 U_132_10
    U_132_11 U_132_12 U_132_13 U_132_14 U_132_15 U_132_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_133_1 :
    Uω (aρ 1) (bρ 1) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(5247902385718883216969 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46410094175333 / 640000000000000 : ℝ) ≤
      (-(5247902385718883216969 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46410094175333 / 640000000000000 : ℚ))
        (r' := (46410094175333 / 40000000000000 : ℚ))
        (U := (-(5247902385718883216969 / 2000000000000000000000 : ℚ)))
        (U' := (297275056681116783031 / 2000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (5055218440057 / 64000000000000 : ℚ))
      (s := (2899739119221 / 40000000000000 : ℚ))
      (q := (46410094175333 / 640000000000000 : ℚ))
      (U := (-(5247902385718883216969 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_133_2 :
    Uω (aρ 2) (bρ 2) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(5318245093358236445799 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5600769992529341 / 80000000000000000 : ℝ) ≤
      (-(5318245093358236445799 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5600769992529341 / 80000000000000000 : ℚ))
        (r' := (5600769992529341 / 5000000000000000 : ℚ))
        (U := (-(5318245093358236445799 / 2000000000000000000000 : ℚ)))
        (U' := (226932349041763554201 / 2000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (5055218440057 / 64000000000000 : ℚ))
      (s := (698580847468429 / 10000000000000000 : ℚ))
      (q := (5600769992529341 / 80000000000000000 : ℚ))
      (U := (-(5318245093358236445799 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_133_3 :
    Uω (aρ 3) (bρ 3) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(27356603986588711129289 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5188093221524637 / 80000000000000000 : ℝ) ≤
      (-(27356603986588711129289 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5188093221524637 / 80000000000000000 : ℚ))
        (r' := (5188093221524637 / 5000000000000000 : ℚ))
        (U := (-(27356603986588711129289 / 10000000000000000000000 : ℚ)))
        (U' := (369283225411288870711 / 10000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (5055218440057 / 64000000000000 : ℚ))
      (s := (642807761067253 / 10000000000000000 : ℚ))
      (q := (5188093221524637 / 80000000000000000 : ℚ))
      (U := (-(27356603986588711129289 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_133_4 :
    Uω (aρ 4) (bρ 4) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(14438564217655403680117 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4456277560487961 / 80000000000000000 : ℝ) ≤
      (-(14438564217655403680117 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4456277560487961 / 80000000000000000 : ℚ))
        (r' := (4456277560487961 / 2500000000000000 : ℚ))
        (U := (-(14438564217655403680117 / 5000000000000000000000 : ℚ)))
        (U' := (2890115289844596319883 / 5000000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (5055218440057 / 64000000000000 : ℚ))
      (s := (134537006718271 / 2500000000000000 : ℚ))
      (q := (4456277560487961 / 80000000000000000 : ℚ))
      (U := (-(14438564217655403680117 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_133_5 :
    Uω (aρ 5) (bρ 5) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(4057368370546522140043 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (622939437810389 / 16000000000000000 : ℝ) ≤
      (-(4057368370546522140043 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (622939437810389 / 16000000000000000 : ℚ))
        (r' := (622939437810389 / 500000000000000 : ℚ))
        (U := (-(4057368370546522140043 / 1250000000000000000000 : ℚ)))
        (U' := (274801506328477859957 / 1250000000000000000000 : ℚ))
        5 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (5055218440057 / 64000000000000 : ℚ))
      (s := (8023571333727 / 250000000000000 : ℚ))
      (q := (622939437810389 / 16000000000000000 : ℚ))
      (U := (-(4057368370546522140043 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_133_6 :
    Uω (aρ 6) (bρ 6) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_133_7 :
    Uω (aρ 7) (bρ 7) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_133_8 :
    Uω (aρ 8) (bρ 8) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_133_9 :
    Uω (aρ 9) (bρ 9) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_133_10 :
    Uω (aρ 10) (bρ 10) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_133_11 :
    Uω (aρ 11) (bρ 11) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_133_12 :
    Uω (aρ 12) (bρ 12) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_133_13 :
    Uω (aρ 13) (bρ 13) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_133_14 :
    Uω (aρ 14) (bρ 14) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_133_15 :
    Uω (aρ 15) (bρ 15) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_133_16 :
    Uω (aρ 16) (bρ 16) (5055218440057 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_133 :
    Uρ (5055218440057 / 64000000000000 : ℝ) ≤
      (-(24752415938931362015277 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_133_1 U_133_2 U_133_3 U_133_4 U_133_5 U_133_6 U_133_7 U_133_8 U_133_9 U_133_10
    U_133_11 U_133_12 U_133_13 U_133_14 U_133_15 U_133_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_134_1 :
    Uω (aρ 1) (bρ 1) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(26167288670425871360889 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2921656021086593 / 40000000000000000 : ℝ) ≤
      (-(26167288670425871360889 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2921656021086593 / 40000000000000000 : ℚ))
        (r' := (2921656021086593 / 2500000000000000 : ℚ))
        (U := (-(26167288670425871360889 / 10000000000000000000000 : ℚ)))
        (U' := (1558598541574128639111 / 10000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2544424194189 / 32000000000000 : ℚ))
      (s := (365096333972117 / 5000000000000000 : ℚ))
      (q := (2921656021086593 / 40000000000000000 : ℚ))
      (U := (-(26167288670425871360889 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_134_2 :
    Uω (aρ 2) (bρ 2) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(26516288816997824638059 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2821448967842361 / 40000000000000000 : ℝ) ≤
      (-(26516288816997824638059 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2821448967842361 / 40000000000000000 : ℚ))
        (r' := (2821448967842361 / 2500000000000000 : ℚ))
        (U := (-(26516288816997824638059 / 10000000000000000000000 : ℚ)))
        (U' := (1209598395002175361941 / 10000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2544424194189 / 32000000000000 : ℚ))
      (s := (351929076916059 / 5000000000000000 : ℚ))
      (q := (2821448967842361 / 40000000000000000 : ℚ))
      (U := (-(26516288816997824638059 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_134_3 :
    Uω (aρ 3) (bρ 3) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(2727519639092246926631 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2615250310535261 / 40000000000000000 : ℝ) ≤
      (-(2727519639092246926631 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2615250310535261 / 40000000000000000 : ℚ))
        (r' := (2615250310535261 / 2500000000000000 : ℚ))
        (U := (-(2727519639092246926631 / 1000000000000000000000 : ℚ)))
        (U' := (45069082107753073369 / 1000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2544424194189 / 32000000000000 : ℚ))
      (s := (81019366441071 / 1250000000000000 : ℚ))
      (q := (2615250310535261 / 40000000000000000 : ℚ))
      (U := (-(2727519639092246926631 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_134_4 :
    Uω (aρ 4) (bρ 4) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(28779991109665995308087 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2249887785468721 / 40000000000000000 : ℝ) ≤
      (-(28779991109665995308087 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2249887785468721 / 40000000000000000 : ℚ))
        (r' := (2249887785468721 / 1250000000000000 : ℚ))
        (U := (-(28779991109665995308087 / 10000000000000000000000 : ℚ)))
        (U' := (5877367905334004691913 / 10000000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2544424194189 / 32000000000000 : ℚ))
      (s := (271883925030149 / 5000000000000000 : ℚ))
      (q := (2249887785468721 / 40000000000000000 : ℚ))
      (U := (-(28779991109665995308087 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_134_5 :
    Uω (aρ 5) (bρ 5) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(16148547889847596668857 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1582759550979519 / 40000000000000000 : ℝ) ≤
      (-(16148547889847596668857 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1582759550979519 / 40000000000000000 : ℚ))
        (r' := (1582759550979519 / 1250000000000000 : ℚ))
        (U := (-(16148547889847596668857 / 5000000000000000000000 : ℚ)))
        (U' := (1180131617652403331143 / 5000000000000000000000 : ℚ))
        5 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2544424194189 / 32000000000000 : ℚ))
      (s := (328393652150697 / 10000000000000000 : ℚ))
      (q := (1582759550979519 / 40000000000000000 : ℚ))
      (U := (-(16148547889847596668857 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_134_6 :
    Uω (aρ 6) (bρ 6) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_134_7 :
    Uω (aρ 7) (bρ 7) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_134_8 :
    Uω (aρ 8) (bρ 8) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_134_9 :
    Uω (aρ 9) (bρ 9) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_134_10 :
    Uω (aρ 10) (bρ 10) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_134_11 :
    Uω (aρ 11) (bρ 11) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_134_12 :
    Uω (aρ 12) (bρ 12) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_134_13 :
    Uω (aρ 13) (bρ 13) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_134_14 :
    Uω (aρ 14) (bρ 14) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_134_15 :
    Uω (aρ 15) (bρ 15) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_134_16 :
    Uω (aρ 16) (bρ 16) (2544424194189 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_134 :
    Uρ (2544424194189 / 32000000000000 : ℝ) ≤
      (-(6182281286838750952367 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_134_1 U_134_2 U_134_3 U_134_4 U_134_5 U_134_6 U_134_7 U_134_8 U_134_9 U_134_10
    U_134_11 U_134_12 U_134_13 U_134_14 U_134_15 U_134_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_135_1 :
    Uω (aρ 1) (bρ 1) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(13047791802904571252103 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (235414485158707 / 3200000000000000 : ℝ) ≤
      (-(13047791802904571252103 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (235414485158707 / 3200000000000000 : ℚ))
        (r' := (235414485158707 / 200000000000000 : ℚ))
        (U := (-(13047791802904571252103 / 5000000000000000000000 : ℚ)))
        (U' := (815151803095428747897 / 5000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (5122478336699 / 64000000000000 : ℚ))
      (s := (7354505102177 / 100000000000000 : ℚ))
      (q := (235414485158707 / 3200000000000000 : ℚ))
      (U := (-(13047791802904571252103 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_135_2 :
    Uω (aρ 2) (bρ 2) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(13220955953813518373719 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5685024534630623 / 80000000000000000 : ℝ) ≤
      (-(13220955953813518373719 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5685024534630623 / 80000000000000000 : ℚ))
        (r' := (5685024534630623 / 5000000000000000 : ℚ))
        (U := (-(13220955953813518373719 / 5000000000000000000000 : ℚ)))
        (U' := (641987652186481626281 / 5000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (5122478336699 / 64000000000000 : ℚ))
      (s := (709135124143437 / 10000000000000000 : ℚ))
      (q := (5685024534630623 / 80000000000000000 : ℚ))
      (U := (-(13220955953813518373719 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_135_3 :
    Uω (aρ 3) (bρ 3) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(13597228774851769235177 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5272902018632919 / 80000000000000000 : ℝ) ≤
      (-(13597228774851769235177 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5272902018632919 / 80000000000000000 : ℚ))
        (r' := (5272902018632919 / 5000000000000000 : ℚ))
        (U := (-(13597228774851769235177 / 5000000000000000000000 : ℚ)))
        (U' := (265714831148230764823 / 5000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (5122478336699 / 64000000000000 : ℚ))
      (s := (653500601494011 / 10000000000000000 : ℚ))
      (q := (5272902018632919 / 80000000000000000 : ℚ))
      (U := (-(13597228774851769235177 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_135_4 :
    Uω (aρ 4) (bρ 4) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(7170962978482870943403 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4543244670778931 / 80000000000000000 : ℝ) ≤
      (-(7170962978482870943403 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4543244670778931 / 80000000000000000 : ℚ))
        (r' := (4543244670778931 / 2500000000000000 : ℚ))
        (U := (-(7170962978482870943403 / 2500000000000000000000 : ℚ)))
        (U' := (1493376775267129056597 / 2500000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (5122478336699 / 64000000000000 : ℚ))
      (s := (274690222797757 / 5000000000000000 : ℚ))
      (q := (4543244670778931 / 80000000000000000 : ℚ))
      (U := (-(7170962978482870943403 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_135_5 :
    Uω (aρ 5) (bρ 5) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(6427771188288008699121 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3216008644341211 / 80000000000000000 : ℝ) ≤
      (-(6427771188288008699121 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3216008644341211 / 80000000000000000 : ℚ))
        (r' := (3216008644341211 / 2500000000000000 : ℚ))
        (U := (-(6427771188288008699121 / 2000000000000000000000 : ℚ)))
        (U' := (503700614711991300879 / 2000000000000000000000 : ℚ))
        5 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (5122478336699 / 64000000000000 : ℚ))
      (s := (83940339580271 / 2500000000000000 : ℚ))
      (q := (3216008644341211 / 80000000000000000 : ℚ))
      (U := (-(6427771188288008699121 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_135_6 :
    Uω (aρ 6) (bρ 6) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_135_7 :
    Uω (aρ 7) (bρ 7) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_135_8 :
    Uω (aρ 8) (bρ 8) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_135_9 :
    Uω (aρ 9) (bρ 9) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_135_10 :
    Uω (aρ 10) (bρ 10) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_135_11 :
    Uω (aρ 11) (bρ 11) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_135_12 :
    Uω (aρ 12) (bρ 12) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_135_13 :
    Uω (aρ 13) (bρ 13) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_135_14 :
    Uω (aρ 14) (bρ 14) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_135_15 :
    Uω (aρ 15) (bρ 15) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_135_16 :
    Uω (aρ 16) (bρ 16) (5122478336699 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_135 :
    Uρ (5122478336699 / 64000000000000 : ℝ) ≤
      (-(3088274053514358657371 / 1250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_135_1 U_135_2 U_135_3 U_135_4 U_135_5 U_135_6 U_135_7 U_135_8 U_135_9 U_135_10
    U_135_11 U_135_12 U_135_13 U_135_14 U_135_15 U_135_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
