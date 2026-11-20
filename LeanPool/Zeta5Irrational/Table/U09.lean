/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U09) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_112_1 :
    Uω (aρ 1) (bρ 1) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(5494454591738893614821 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5128428811782121 / 80000000000000000 : ℝ) ≤
      (-(5494454591738893614821 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5128428811782121 / 80000000000000000 : ℚ))
        (r' := (5128428811782121 / 5000000000000000 : ℚ))
        (U := (-(5494454591738893614821 / 2000000000000000000000 : ℚ)))
        (U' := (50722850661106385179 / 2000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4517139266921 / 64000000000000 : ℚ))
      (s := (160200352643531 / 2500000000000000 : ℚ))
      (q := (5128428811782121 / 80000000000000000 : ℚ))
      (U := (-(5494454591738893614821 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_112_2 :
    Uω (aρ 2) (bρ 2) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(27873954405000162249769 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (985302360873997 / 16000000000000000 : ℝ) ≤
      (-(27873954405000162249769 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (985302360873997 / 16000000000000000 : ℚ))
        (r' := (985302360873997 / 500000000000000 : ℚ))
        (U := (-(27873954405000162249769 / 10000000000000000000000 : ℚ)))
        (U' := (6783404609999837750231 / 10000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4517139266921 / 64000000000000 : ℚ))
      (s := (61409117123109 / 1000000000000000 : ℚ))
      (q := (985302360873997 / 16000000000000000 : ℚ))
      (U := (-(27873954405000162249769 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_112_3 :
    Uω (aρ 3) (bρ 3) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(179752256073111659559 / 62500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4508617367911213 / 80000000000000000 : ℝ) ≤
      (-(179752256073111659559 / 62500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4508617367911213 / 80000000000000000 : ℚ))
        (r' := (4508617367911213 / 2500000000000000 : ℚ))
        (U := (-(179752256073111659559 / 62500000000000000000 : ℚ)))
        (U' := (36856237770638340441 / 62500000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4517139266921 / 64000000000000 : ℚ))
      (s := (557013668466397 / 10000000000000000 : ℚ))
      (q := (4508617367911213 / 80000000000000000 : ℚ))
      (U := (-(179752256073111659559 / 62500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_112_4 :
    Uω (aρ 4) (bρ 4) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(15294047642102670013741 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3755483749271957 / 80000000000000000 : ℝ) ≤
      (-(15294047642102670013741 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3755483749271957 / 80000000000000000 : ℚ))
        (r' := (3755483749271957 / 2500000000000000 : ℚ))
        (U := (-(15294047642102670013741 / 5000000000000000000000 : ℚ)))
        (U' := (2034631865397329986259 / 5000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4517139266921 / 64000000000000 : ℚ))
      (s := (447024444871583 / 10000000000000000 : ℚ))
      (q := (3755483749271957 / 80000000000000000 : ℚ))
      (U := (-(15294047642102670013741 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_112_5 :
    Uω (aρ 5) (bρ 5) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(35834287293306577019241 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (444484538504269 / 16000000000000000 : ℝ) ≤
      (-(35834287293306577019241 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (444484538504269 / 16000000000000000 : ℚ))
        (r' := (444484538504269 / 250000000000000 : ℚ))
        (U := (-(35834287293306577019241 / 10000000000000000000000 : ℚ)))
        (U' := (5754543524693422980759 / 10000000000000000000000 : ℚ))
        6 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4517139266921 / 64000000000000 : ℚ))
      (s := (18194910001893 / 1000000000000000 : ℚ))
      (q := (444484538504269 / 16000000000000000 : ℚ))
      (U := (-(35834287293306577019241 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_112_6 :
    Uω (aρ 6) (bρ 6) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_112_7 :
    Uω (aρ 7) (bρ 7) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_112_8 :
    Uω (aρ 8) (bρ 8) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_112_9 :
    Uω (aρ 9) (bρ 9) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_112_10 :
    Uω (aρ 10) (bρ 10) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_112_11 :
    Uω (aρ 11) (bρ 11) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_112_12 :
    Uω (aρ 12) (bρ 12) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_112_13 :
    Uω (aρ 13) (bρ 13) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_112_14 :
    Uω (aρ 14) (bρ 14) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_112_15 :
    Uω (aρ 15) (bρ 15) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_112_16 :
    Uω (aρ 16) (bρ 16) (4517139266921 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_112 :
    Uρ (4517139266921 / 64000000000000 : ℝ) ≤
      (-(25196063800726208672673 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_112_1 U_112_2 U_112_3 U_112_4 U_112_5 U_112_6 U_112_7 U_112_8 U_112_9 U_112_10
    U_112_11 U_112_12 U_112_13 U_112_14 U_112_15 U_112_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_113_1 :
    Uω (aρ 1) (bρ 1) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(27390605922888495679481 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (517048265663313 / 8000000000000000 : ℝ) ≤
      (-(27390605922888495679481 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (517048265663313 / 8000000000000000 : ℚ))
        (r' := (517048265663313 / 500000000000000 : ℚ))
        (U := (-(27390605922888495679481 / 10000000000000000000000 : ℚ)))
        (U' := (335281289111504320519 / 10000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2275384607621 / 32000000000000 : ℚ))
      (s := (16151504809043 / 250000000000000 : ℚ))
      (q := (517048265663313 / 8000000000000000 : ℚ))
      (U := (-(27390605922888495679481 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_113_2 :
    Uω (aρ 2) (bρ 2) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(13894376027202381802373 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2484333085253499 / 40000000000000000 : ℝ) ≤
      (-(13894376027202381802373 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2484333085253499 / 40000000000000000 : ℚ))
        (r' := (2484333085253499 / 1250000000000000 : ℚ))
        (U := (-(13894376027202381802373 / 5000000000000000000000 : ℚ)))
        (U' := (3434303480297618197627 / 5000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2275384607621 / 32000000000000 : ℚ))
      (s := (619375083340187 / 10000000000000000 : ℚ))
      (q := (2484333085253499 / 40000000000000000 : ℚ))
      (U := (-(13894376027202381802373 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_113_3 :
    Uω (aρ 3) (bρ 3) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(14333238409323982707187 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2275572731773867 / 40000000000000000 : ℝ) ≤
      (-(14333238409323982707187 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2275572731773867 / 40000000000000000 : ℚ))
        (r' := (2275572731773867 / 1250000000000000 : ℚ))
        (U := (-(14333238409323982707187 / 5000000000000000000000 : ℚ)))
        (U' := (2995441098176017292813 / 5000000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2275384607621 / 32000000000000 : ℚ))
      (s := (562391012950371 / 10000000000000000 : ℚ))
      (q := (2275572731773867 / 40000000000000000 : ℚ))
      (U := (-(14333238409323982707187 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_113_4 :
    Uω (aρ 4) (bρ 4) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(15235650232966056679897 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1899801498462243 / 40000000000000000 : ℝ) ≤
      (-(15235650232966056679897 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1899801498462243 / 40000000000000000 : ℚ))
        (r' := (1899801498462243 / 1250000000000000 : ℚ))
        (U := (-(15235650232966056679897 / 5000000000000000000000 : ℚ)))
        (U' := (2093029274533943320103 / 5000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2275384607621 / 32000000000000 : ℚ))
      (s := (452799577359559 / 10000000000000000 : ℚ))
      (q := (1899801498462243 / 40000000000000000 : ℚ))
      (U := (-(15235650232966056679897 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_113_5 :
    Uω (aρ 5) (bρ 5) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(17776807122822487646779 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (228568373818183 / 8000000000000000 : ℝ) ≤
      (-(17776807122822487646779 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (228568373818183 / 8000000000000000 : ℚ))
        (r' := (228568373818183 / 125000000000000 : ℚ))
        (U := (-(17776807122822487646779 / 5000000000000000000000 : ℚ)))
        (U' := (3017608286177512353221 / 5000000000000000000000 : ℚ))
        6 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2275384607621 / 32000000000000 : ℚ))
      (s := (38501936401779 / 2000000000000000 : ℚ))
      (q := (228568373818183 / 8000000000000000 : ℚ))
      (U := (-(17776807122822487646779 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_113_6 :
    Uω (aρ 6) (bρ 6) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_113_7 :
    Uω (aρ 7) (bρ 7) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_113_8 :
    Uω (aρ 8) (bρ 8) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_113_9 :
    Uω (aρ 9) (bρ 9) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_113_10 :
    Uω (aρ 10) (bρ 10) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_113_11 :
    Uω (aρ 11) (bρ 11) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_113_12 :
    Uω (aρ 12) (bρ 12) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_113_13 :
    Uω (aρ 13) (bρ 13) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_113_14 :
    Uω (aρ 14) (bρ 14) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_113_15 :
    Uω (aρ 15) (bρ 15) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_113_16 :
    Uω (aρ 16) (bρ 16) (2275384607621 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_113 :
    Uρ (2275384607621 / 32000000000000 : ℝ) ≤
      (-(5032497630608943774487 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_113_1 U_113_2 U_113_3 U_113_4 U_113_5 U_113_6 U_113_7 U_113_8 U_113_9 U_113_10
    U_113_11 U_113_12 U_113_13 U_113_14 U_113_15 U_113_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_114_1 :
    Uω (aρ 1) (bρ 1) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(853425029583273381449 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5212536236606059 / 80000000000000000 : ℝ) ≤
      (-(853425029583273381449 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5212536236606059 / 80000000000000000 : ℚ))
        (r' := (5212536236606059 / 5000000000000000 : ℚ))
        (U := (-(853425029583273381449 / 312500000000000000000 : ℚ)))
        (U' := (13008945791726618551 / 312500000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4584399163563 / 64000000000000 : ℚ))
      (s := (162829726982449 / 2500000000000000 : ℚ))
      (q := (5212536236606059 / 80000000000000000 : ℚ))
      (U := (-(853425029583273381449 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_114_2 :
    Uω (aρ 2) (bρ 2) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(13852136729366462766811 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (200432742556419 / 3200000000000000 : ℝ) ≤
      (-(13852136729366462766811 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (200432742556419 / 3200000000000000 : ℚ))
        (r' := (200432742556419 / 200000000000000 : ℚ))
        (U := (-(13852136729366462766811 / 5000000000000000000000 : ℚ)))
        (U' := (10806876633537233189 / 5000000000000000000000 : ℚ))
        4 2 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4584399163563 / 64000000000000 : ℚ))
      (s := (6246585022659 / 100000000000000 : ℚ))
      (q := (200432742556419 / 3200000000000000 : ℚ))
      (U := (-(13852136729366462766811 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_114_3 :
    Uω (aρ 3) (bρ 3) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(3571685737350867667193 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (918732874213519 / 16000000000000000 : ℝ) ≤
      (-(3571685737350867667193 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (918732874213519 / 16000000000000000 : ℚ))
        (r' := (918732874213519 / 500000000000000 : ℚ))
        (U := (-(3571685737350867667193 / 1250000000000000000000 : ℚ)))
        (U' := (760484139524132332807 / 1250000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4584399163563 / 64000000000000 : ℚ))
      (s := (28388303020259 / 500000000000000 : ℚ))
      (q := (918732874213519 / 16000000000000000 : ℚ))
      (U := (-(3571685737350867667193 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_114_4 :
    Uω (aρ 4) (bρ 4) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(30355984291079358506601 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3843672171359951 / 80000000000000000 : ℝ) ≤
      (-(30355984291079358506601 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3843672171359951 / 80000000000000000 : ℚ))
        (r' := (3843672171359951 / 2500000000000000 : ℚ))
        (U := (-(30355984291079358506601 / 10000000000000000000000 : ℚ)))
        (U' := (4301374723920641493399 / 10000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4584399163563 / 64000000000000 : ℚ))
      (s := (458562191543269 / 10000000000000000 : ℚ))
      (q := (3843672171359951 / 80000000000000000 : ℚ))
      (U := (-(30355984291079358506601 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_114_5 :
    Uω (aρ 5) (bρ 5) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(8821912704169286925593 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2347290188291931 / 80000000000000000 : ℝ) ≤
      (-(8821912704169286925593 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2347290188291931 / 80000000000000000 : ℚ))
        (r' := (2347290188291931 / 1250000000000000 : ℚ))
        (U := (-(8821912704169286925593 / 2500000000000000000000 : ℚ)))
        (U' := (1575295000330713074407 / 2500000000000000000000 : ℚ))
        6 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4584399163563 / 64000000000000 : ℚ))
      (s := (6333019222227 / 312500000000000 : ℚ))
      (q := (2347290188291931 / 80000000000000000 : ℚ))
      (U := (-(8821912704169286925593 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_114_6 :
    Uω (aρ 6) (bρ 6) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_114_7 :
    Uω (aρ 7) (bρ 7) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_114_8 :
    Uω (aρ 8) (bρ 8) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_114_9 :
    Uω (aρ 9) (bρ 9) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_114_10 :
    Uω (aρ 10) (bρ 10) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_114_11 :
    Uω (aρ 11) (bρ 11) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_114_12 :
    Uω (aρ 12) (bρ 12) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_114_13 :
    Uω (aρ 13) (bρ 13) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_114_14 :
    Uω (aρ 14) (bρ 14) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_114_15 :
    Uω (aρ 15) (bρ 15) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_114_16 :
    Uω (aρ 16) (bρ 16) (4584399163563 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_114 :
    Uρ (4584399163563 / 64000000000000 : ℝ) ≤
      (-(25130080728420120270839 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_114_1 U_114_2 U_114_3 U_114_4 U_114_5 U_114_6 U_114_7 U_114_8 U_114_9 U_114_10
    U_114_11 U_114_12 U_114_13 U_114_14 U_114_15 U_114_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_115_1 :
    Uω (aρ 1) (bρ 1) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(13614623686929618077151 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1313647389516337 / 20000000000000000 : ℝ) ≤
      (-(13614623686929618077151 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1313647389516337 / 20000000000000000 : ℚ))
        (r' := (1313647389516337 / 1250000000000000 : ℚ))
        (U := (-(13614623686929618077151 / 5000000000000000000000 : ℚ)))
        (U' := (248319919070381922849 / 5000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1154507277971 / 16000000000000 : ℚ))
      (s := (328288779434731 / 5000000000000000 : ℚ))
      (q := (1313647389516337 / 20000000000000000 : ℚ))
      (U := (-(13614623686929618077151 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_115_2 :
    Uω (aρ 2) (bρ 2) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(27620506355407504983373 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (631621129277163 / 10000000000000000 : ℝ) ≤
      (-(27620506355407504983373 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (631621129277163 / 10000000000000000 : ℚ))
        (r' := (631621129277163 / 625000000000000 : ℚ))
        (U := (-(27620506355407504983373 / 10000000000000000000000 : ℚ)))
        (U' := (105380856592495016627 / 10000000000000000000000 : ℚ))
        4 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1154507277971 / 16000000000000 : ℚ))
      (s := (629941440417451 / 10000000000000000 : ℚ))
      (q := (631621129277163 / 10000000000000000 : ℚ))
      (U := (-(27620506355407504983373 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_115_3 :
    Uω (aρ 3) (bρ 3) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(28481371009729646648441 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1159043587244137 / 20000000000000000 : ℝ) ≤
      (-(28481371009729646648441 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1159043587244137 / 20000000000000000 : ℚ))
        (r' := (1159043587244137 / 625000000000000 : ℚ))
        (U := (-(28481371009729646648441 / 10000000000000000000000 : ℚ)))
        (U' := (6175988005270353351559 / 10000000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1154507277971 / 16000000000000 : ℚ))
      (s := (286569437728631 / 5000000000000000 : ℚ))
      (q := (1159043587244137 / 20000000000000000 : ℚ))
      (U := (-(28481371009729646648441 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_115_4 :
    Uω (aρ 4) (bρ 4) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(15121053377842898206551 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (971923284241157 / 20000000000000000 : ℝ) ≤
      (-(15121053377842898206551 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (971923284241157 / 20000000000000000 : ℚ))
        (r' := (971923284241157 / 625000000000000 : ℚ))
        (U := (-(15121053377842898206551 / 5000000000000000000000 : ℚ)))
        (U' := (2207626129657101793449 / 5000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1154507277971 / 16000000000000 : ℚ))
      (s := (232156376759641 / 5000000000000000 : ℚ))
      (q := (971923284241157 / 20000000000000000 : ℚ))
      (U := (-(15121053377842898206551 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_115_5 :
    Uω (aρ 5) (bρ 5) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(8758616067257419857111 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (150467447175143 / 5000000000000000 : ℝ) ≤
      (-(8758616067257419857111 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (150467447175143 / 5000000000000000 : ℚ))
        (r' := (150467447175143 / 78125000000000 : ℚ))
        (U := (-(8758616067257419857111 / 2500000000000000000000 : ℚ)))
        (U' := (1638591637242580142889 / 2500000000000000000000 : ℚ))
        6 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1154507277971 / 16000000000000 : ℚ))
      (s := (212449177313697 / 10000000000000000 : ℚ))
      (q := (150467447175143 / 5000000000000000 : ℚ))
      (U := (-(8758616067257419857111 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_115_6 :
    Uω (aρ 6) (bρ 6) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_115_7 :
    Uω (aρ 7) (bρ 7) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_115_8 :
    Uω (aρ 8) (bρ 8) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_115_9 :
    Uω (aρ 9) (bρ 9) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_115_10 :
    Uω (aρ 10) (bρ 10) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_115_11 :
    Uω (aρ 11) (bρ 11) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_115_12 :
    Uω (aρ 12) (bρ 12) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_115_13 :
    Uω (aρ 13) (bρ 13) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_115_14 :
    Uω (aρ 14) (bρ 14) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_115_15 :
    Uω (aρ 15) (bρ 15) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_115_16 :
    Uω (aρ 16) (bρ 16) (1154507277971 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_115 :
    Uρ (1154507277971 / 16000000000000 : ℝ) ≤
      (-(25098704554830257436931 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_115_1 U_115_2 U_115_3 U_115_4 U_115_5 U_115_6 U_115_7 U_115_8 U_115_9 U_115_10
    U_115_11 U_115_12 U_115_13 U_115_14 U_115_15 U_115_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_116_1 :
    Uω (aρ 1) (bρ 1) (930331812041 / 12800000000000 : ℝ) ≤
      (-(6787383700929643976333 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1059328525434621 / 16000000000000000 : ℝ) ≤
      (-(6787383700929643976333 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1059328525434621 / 16000000000000000 : ℚ))
        (r' := (1059328525434621 / 1000000000000000 : ℚ))
        (U := (-(6787383700929643976333 / 2500000000000000000000 : ℚ)))
        (U' := (144088102070356023667 / 2500000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (930331812041 / 12800000000000 : ℚ))
      (s := (132367229344249 / 2000000000000000 : ℚ))
      (q := (1059328525434621 / 16000000000000000 : ℚ))
      (U := (-(6787383700929643976333 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_116_2 :
    Uω (aρ 2) (bρ 2) (930331812041 / 12800000000000 : ℝ) ≤
      (-(3442179850001808571531 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5095117629408681 / 80000000000000000 : ℝ) ≤
      (-(3442179850001808571531 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5095117629408681 / 80000000000000000 : ℚ))
        (r' := (5095117629408681 / 5000000000000000 : ℚ))
        (U := (-(3442179850001808571531 / 1250000000000000000000 : ℚ)))
        (U' := (23556051498191428469 / 1250000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (930331812041 / 12800000000000 : ℚ))
      (s := (635223909790139 / 10000000000000000 : ℚ))
      (q := (5095117629408681 / 80000000000000000 : ℚ))
      (U := (-(3442179850001808571531 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_116_3 :
    Uω (aρ 3) (bρ 3) (930331812041 / 12800000000000 : ℝ) ≤
      (-(14195057725500391424769 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4678675646071621 / 80000000000000000 : ℝ) ≤
      (-(14195057725500391424769 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4678675646071621 / 80000000000000000 : ℚ))
        (r' := (4678675646071621 / 2500000000000000 : ℚ))
        (U := (-(14195057725500391424769 / 5000000000000000000000 : ℚ)))
        (U' := (3133621781999608575231 / 5000000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (930331812041 / 12800000000000 : ℚ))
      (s := (289254760152937 / 5000000000000000 : ℚ))
      (q := (4678675646071621 / 80000000000000000 : ℚ))
      (U := (-(14195057725500391424769 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_116_4 :
    Uω (aρ 4) (bρ 4) (930331812041 / 12800000000000 : ℝ) ≤
      (-(30129629557487540673771 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3931667663084301 / 80000000000000000 : ℝ) ≤
      (-(30129629557487540673771 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3931667663084301 / 80000000000000000 : ℚ))
        (r' := (3931667663084301 / 2500000000000000 : ℚ))
        (U := (-(30129629557487540673771 / 10000000000000000000000 : ℚ)))
        (U' := (4527729457512459326229 / 10000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (930331812041 / 12800000000000 : ℚ))
      (s := (117512926406011 / 2500000000000000 : ℚ))
      (q := (3931667663084301 / 80000000000000000 : ℚ))
      (U := (-(30129629557487540673771 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_116_5 :
    Uω (aρ 5) (bρ 5) (930331812041 / 12800000000000 : ℝ) ≤
      (-(34792515104179698616019 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2466438291419753 / 80000000000000000 : ℝ) ≤
      (-(34792515104179698616019 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2466438291419753 / 80000000000000000 : ℚ))
        (r' := (2466438291419753 / 1250000000000000 : ℚ))
        (U := (-(34792515104179698616019 / 10000000000000000000000 : ℚ)))
        (U' := (6796315713820301383981 / 10000000000000000000000 : ℚ))
        6 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (930331812041 / 12800000000000 : ℚ))
      (s := (221934282042907 / 10000000000000000 : ℚ))
      (q := (2466438291419753 / 80000000000000000 : ℚ))
      (U := (-(34792515104179698616019 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_116_6 :
    Uω (aρ 6) (bρ 6) (930331812041 / 12800000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_116_7 :
    Uω (aρ 7) (bρ 7) (930331812041 / 12800000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_116_8 :
    Uω (aρ 8) (bρ 8) (930331812041 / 12800000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_116_9 :
    Uω (aρ 9) (bρ 9) (930331812041 / 12800000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_116_10 :
    Uω (aρ 10) (bρ 10) (930331812041 / 12800000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_116_11 :
    Uω (aρ 11) (bρ 11) (930331812041 / 12800000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_116_12 :
    Uω (aρ 12) (bρ 12) (930331812041 / 12800000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_116_13 :
    Uω (aρ 13) (bρ 13) (930331812041 / 12800000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_116_14 :
    Uω (aρ 14) (bρ 14) (930331812041 / 12800000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_116_15 :
    Uω (aρ 15) (bρ 15) (930331812041 / 12800000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_116_16 :
    Uω (aρ 16) (bρ 16) (930331812041 / 12800000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_116 :
    Uρ (930331812041 / 12800000000000 : ℝ) ≤
      (-(25068249941190760208499 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_116_1 U_116_2 U_116_3 U_116_4 U_116_5 U_116_6 U_116_7 U_116_8 U_116_9 U_116_10
    U_116_11 U_116_12 U_116_13 U_116_14 U_116_15 U_116_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_117_1 :
    Uω (aρ 1) (bρ 1) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(13535226541398232719239 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (106773908997941 / 1600000000000000 : ℝ) ≤
      (-(13535226541398232719239 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (106773908997941 / 1600000000000000 : ℚ))
        (r' := (106773908997941 / 100000000000000 : ℚ))
        (U := (-(13535226541398232719239 / 5000000000000000000000 : ℚ)))
        (U' := (327717064601767280761 / 5000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2342644504263 / 32000000000000 : ℚ))
      (s := (26683786919083 / 400000000000000 : ℚ))
      (q := (106773908997941 / 1600000000000000 : ℚ))
      (U := (-(13535226541398232719239 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_117_2 :
    Uω (aρ 2) (bρ 2) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(6863764786365759850067 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2568632197939373 / 40000000000000000 : ℝ) ≤
      (-(6863764786365759850067 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2568632197939373 / 40000000000000000 : ℚ))
        (r' := (2568632197939373 / 2500000000000000 : ℚ))
        (U := (-(6863764786365759850067 / 2500000000000000000000 : ℚ)))
        (U' := (67707016634240149933 / 2500000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2342644504263 / 32000000000000 : ℚ))
      (s := (640505921982499 / 10000000000000000 : ℚ))
      (q := (2568632197939373 / 40000000000000000 : ℚ))
      (U := (-(6863764786365759850067 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_117_3 :
    Uω (aρ 3) (bρ 3) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(14149851502271592942073 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (472116850189721 / 8000000000000000 : ℝ) ≤
      (-(14149851502271592942073 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (472116850189721 / 8000000000000000 : ℚ))
        (r' := (472116850189721 / 250000000000000 : ℚ))
        (U := (-(14149851502271592942073 / 5000000000000000000000 : ℚ)))
        (U' := (3178828005228407057927 / 5000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2342644504263 / 32000000000000 : ℚ))
      (s := (116775610967423 / 2000000000000000 : ℚ))
      (q := (472116850189721 / 8000000000000000 : ℚ))
      (U := (-(14149851502271592942073 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_117_4 :
    Uω (aρ 4) (bρ 4) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(30018515996535756825573 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1987798715104119 / 40000000000000000 : ℝ) ≤
      (-(30018515996535756825573 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1987798715104119 / 40000000000000000 : ℚ))
        (r' := (1987798715104119 / 1250000000000000 : ℚ))
        (U := (-(30018515996535756825573 / 10000000000000000000000 : ℚ)))
        (U' := (4638843018464243174427 / 10000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2342644504263 / 32000000000000 : ℚ))
      (s := (14868108374371 / 312500000000000 : ℚ))
      (q := (1987798715104119 / 40000000000000000 : ℚ))
      (U := (-(30018515996535756825573 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_117_5 :
    Uω (aρ 5) (bρ 5) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(34560553073273099210261 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1262159503365177 / 40000000000000000 : ℝ) ≤
      (-(34560553073273099210261 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1262159503365177 / 40000000000000000 : ℚ))
        (r' := (1262159503365177 / 1250000000000000 : ℚ))
        (U := (-(34560553073273099210261 / 10000000000000000000000 : ℚ)))
        (U' := (96805941726900789739 / 10000000000000000000000 : ℚ))
        5 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2342644504263 / 32000000000000 : ℚ))
      (s := (231149781445401 / 10000000000000000 : ℚ))
      (q := (1262159503365177 / 40000000000000000 : ℚ))
      (U := (-(34560553073273099210261 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_117_6 :
    Uω (aρ 6) (bρ 6) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_117_7 :
    Uω (aρ 7) (bρ 7) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_117_8 :
    Uω (aρ 8) (bρ 8) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_117_9 :
    Uω (aρ 9) (bρ 9) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_117_10 :
    Uω (aρ 10) (bρ 10) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_117_11 :
    Uω (aρ 11) (bρ 11) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_117_12 :
    Uω (aρ 12) (bρ 12) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_117_13 :
    Uω (aρ 13) (bρ 13) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_117_14 :
    Uω (aρ 14) (bρ 14) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_117_15 :
    Uω (aρ 15) (bρ 15) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_117_16 :
    Uω (aρ 16) (bρ 16) (2342644504263 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_117 :
    Uρ (2342644504263 / 32000000000000 : ℝ) ≤
      (-(1001545091634398708323 / 400000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_117_1 U_117_2 U_117_3 U_117_4 U_117_5 U_117_6 U_117_7 U_117_8 U_117_9 U_117_10
    U_117_11 U_117_12 U_117_13 U_117_14 U_117_15 U_117_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_118_1 :
    Uω (aρ 1) (bρ 1) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(6757786420885346854021 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2143888708271497 / 32000000000000000 : ℝ) ≤
      (-(6757786420885346854021 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2143888708271497 / 32000000000000000 : ℚ))
        (r' := (2143888708271497 / 2000000000000000 : ℚ))
        (U := (-(6757786420885346854021 / 2500000000000000000000 : ℚ)))
        (U' := (173685382114653145979 / 2500000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (9404207965373 / 128000000000000 : ℚ))
      (s := (8371548918249 / 125000000000000 : ℚ))
      (q := (2143888708271497 / 32000000000000000 : ℚ))
      (U := (-(6757786420885346854021 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_118_2 :
    Uω (aρ 2) (bρ 2) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(1096564948833060777743 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10316674214847229 / 160000000000000000 : ℝ) ≤
      (-(1096564948833060777743 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10316674214847229 / 160000000000000000 : ℚ))
        (r' := (10316674214847229 / 10000000000000000 : ℚ))
        (U := (-(1096564948833060777743 / 400000000000000000000 : ℚ)))
        (U' := (12470539646939222257 / 400000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (9404207965373 / 128000000000000 : ℚ))
      (s := (321573380078069 / 5000000000000000 : ℚ))
      (q := (10316674214847229 / 160000000000000000 : ℚ))
      (U := (-(1096564948833060777743 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_118_3 :
    Uω (aρ 3) (bρ 3) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(110370343779415330577 / 39062500000000000000 : ℝ)) := by
  have hlg :
    Real.log (379392946941437 / 6400000000000000 : ℝ) ≤
      (-(110370343779415330577 / 39062500000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (379392946941437 / 6400000000000000 : ℚ))
        (r' := (379392946941437 / 200000000000000 : ℚ))
        (U := (-(110370343779415330577 / 39062500000000000000 : ℚ)))
        (U' := (25009964872928419423 / 39062500000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (9404207965373 / 128000000000000 : ℚ))
      (s := (23462461953689 / 400000000000000 : ℚ))
      (q := (379392946941437 / 6400000000000000 : ℚ))
      (U := (-(110370343779415330577 / 39062500000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_118_4 :
    Uω (aρ 4) (bρ 4) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(1198538381065681381673 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1599018412565393 / 32000000000000000 : ℝ) ≤
      (-(1198538381065681381673 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1599018412565393 / 32000000000000000 : ℚ))
        (r' := (1599018412565393 / 1000000000000000 : ℚ))
        (U := (-(1198538381065681381673 / 400000000000000000000 : ℚ)))
        (U' := (187755979534318618327 / 400000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (9404207965373 / 128000000000000 : ℚ))
      (s := (95727855713721 / 2000000000000000 : ℚ))
      (q := (1599018412565393 / 32000000000000000 : ℚ))
      (U := (-(1198538381065681381673 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_118_5 :
    Uω (aρ 5) (bρ 5) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(34447987663370110448543 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5105789273487933 / 160000000000000000 : ℝ) ≤
      (-(34447987663370110448543 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5105789273487933 / 160000000000000000 : ℚ))
        (r' := (5105789273487933 / 5000000000000000 : ℚ))
        (U := (-(34447987663370110448543 / 10000000000000000000000 : ℚ)))
        (U' := (209371351629889551457 / 10000000000000000000000 : ℚ))
        5 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (9404207965373 / 128000000000000 : ℚ))
      (s := (117833174618113 / 5000000000000000 : ℚ))
      (q := (5105789273487933 / 160000000000000000 : ℚ))
      (U := (-(34447987663370110448543 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_118_6 :
    Uω (aρ 6) (bρ 6) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_118_7 :
    Uω (aρ 7) (bρ 7) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_118_8 :
    Uω (aρ 8) (bρ 8) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_118_9 :
    Uω (aρ 9) (bρ 9) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_118_10 :
    Uω (aρ 10) (bρ 10) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_118_11 :
    Uω (aρ 11) (bρ 11) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_118_12 :
    Uω (aρ 12) (bρ 12) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_118_13 :
    Uω (aρ 13) (bρ 13) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_118_14 :
    Uω (aρ 14) (bρ 14) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_118_15 :
    Uω (aρ 15) (bρ 15) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_118_16 :
    Uω (aρ 16) (bρ 16) (9404207965373 / 128000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_118 :
    Uρ (9404207965373 / 128000000000000 : ℝ) ≤
      (-(625602605153547579439 / 250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_118_1 U_118_2 U_118_3 U_118_4 U_118_5 U_118_6 U_118_7 U_118_8 U_118_9 U_118_10
    U_118_11 U_118_12 U_118_13 U_118_14 U_118_15 U_118_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_119_1 :
    Uω (aρ 1) (bρ 1) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(26991992297169125119499 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5380748032018147 / 80000000000000000 : ℝ) ≤
      (-(26991992297169125119499 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5380748032018147 / 80000000000000000 : ℚ))
        (r' := (5380748032018147 / 5000000000000000 : ℚ))
        (U := (-(26991992297169125119499 / 10000000000000000000000 : ℚ)))
        (U' := (733894914830874880501 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4718918956847 / 64000000000000 : ℚ))
      (s := (672353139082193 / 10000000000000000 : ℚ))
      (q := (5380748032018147 / 80000000000000000 : ℚ))
      (U := (-(26991992297169125119499 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_119_2 :
    Uω (aρ 2) (bρ 2) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(27373356034580663451179 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5179409378499819 / 80000000000000000 : ℝ) ≤
      (-(27373356034580663451179 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5179409378499819 / 80000000000000000 : ℚ))
        (r' := (5179409378499819 / 5000000000000000 : ℚ))
        (U := (-(27373356034580663451179 / 10000000000000000000000 : ℚ)))
        (U' := (352531177419336548821 / 10000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4718918956847 / 64000000000000 : ℚ))
      (s := (645787488212611 / 10000000000000000 : ℚ))
      (q := (5179409378499819 / 80000000000000000 : ℚ))
      (U := (-(27373356034580663451179 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_119_3 :
    Uω (aρ 3) (bρ 3) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(28210117915897178442261 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4763653147175431 / 80000000000000000 : ℝ) ≤
      (-(28210117915897178442261 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4763653147175431 / 80000000000000000 : ℚ))
        (r' := (4763653147175431 / 2500000000000000 : ℚ))
        (U := (-(28210117915897178442261 / 10000000000000000000000 : ℚ)))
        (U' := (6447241099102821557739 / 10000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4718918956847 / 64000000000000 : ℚ))
      (s := (294622268365757 / 5000000000000000 : ℚ))
      (q := (4763653147175431 / 80000000000000000 : ℚ))
      (U := (-(28210117915897178442261 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_119_4 :
    Uω (aρ 4) (bρ 4) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(29908730883182997431499 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (32155872285303 / 640000000000000 : ℝ) ≤
      (-(29908730883182997431499 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (32155872285303 / 640000000000000 : ℚ))
        (r' := (32155872285303 / 20000000000000 : ℚ))
        (U := (-(29908730883182997431499 / 10000000000000000000000 : ℚ)))
        (U' := (4748628131817002568501 / 10000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4718918956847 / 64000000000000 : ℚ))
      (s := (3851971519347 / 80000000000000 : ℚ))
      (q := (32155872285303 / 640000000000000 : ℚ))
      (U := (-(29908730883182997431499 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_119_5 :
    Uω (aρ 5) (bρ 5) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(34337546103835562865811 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2581245470590107 / 80000000000000000 : ℝ) ≤
      (-(34337546103835562865811 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2581245470590107 / 80000000000000000 : ℚ))
        (r' := (2581245470590107 / 2500000000000000 : ℚ))
        (U := (-(34337546103835562865811 / 10000000000000000000000 : ℚ)))
        (U' := (319812911164437134189 / 10000000000000000000000 : ℚ))
        5 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4718918956847 / 64000000000000 : ℚ))
      (s := (240126717985183 / 10000000000000000 : ℚ))
      (q := (2581245470590107 / 80000000000000000 : ℚ))
      (U := (-(34337546103835562865811 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_119_6 :
    Uω (aρ 6) (bρ 6) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_119_7 :
    Uω (aρ 7) (bρ 7) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_119_8 :
    Uω (aρ 8) (bρ 8) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_119_9 :
    Uω (aρ 9) (bρ 9) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_119_10 :
    Uω (aρ 10) (bρ 10) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_119_11 :
    Uω (aρ 11) (bρ 11) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_119_12 :
    Uω (aρ 12) (bρ 12) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_119_13 :
    Uω (aρ 13) (bρ 13) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_119_14 :
    Uω (aρ 14) (bρ 14) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_119_15 :
    Uω (aρ 15) (bρ 15) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_119_16 :
    Uω (aρ 16) (bρ 16) (4718918956847 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_119 :
    Uρ (4718918956847 / 64000000000000 : ℝ) ≤
      (-(1563110136778042269237 / 625000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_119_1 U_119_2 U_119_3 U_119_4 U_119_5 U_119_6 U_119_7 U_119_8 U_119_9 U_119_10
    U_119_11 U_119_12 U_119_13 U_119_14 U_119_15 U_119_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_120_1 :
    Uω (aρ 1) (bρ 1) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(26952991720637376599691 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10803548469219799 / 160000000000000000 : ℝ) ≤
      (-(26952991720637376599691 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10803548469219799 / 160000000000000000 : ℚ))
        (r' := (10803548469219799 / 10000000000000000 : ℚ))
        (U := (-(26952991720637376599691 / 10000000000000000000000 : ℚ)))
        (U' := (772895491362623400309 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1894293572403 / 25600000000000 : ℚ))
      (s := (674982350017553 / 10000000000000000 : ℚ))
      (q := (10803548469219799 / 160000000000000000 : ℚ))
      (U := (-(26952991720637376599691 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_120_2 :
    Uω (aρ 2) (bρ 2) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(13666377355402748850127 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10400962428977599 / 160000000000000000 : ℝ) ≤
      (-(13666377355402748850127 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10400962428977599 / 160000000000000000 : ℚ))
        (r' := (10400962428977599 / 10000000000000000 : ℚ))
        (U := (-(13666377355402748850127 / 5000000000000000000000 : ℚ)))
        (U' := (196566250597251149873 / 5000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1894293572403 / 25600000000000 : ℚ))
      (s := (324214053748639 / 5000000000000000 : ℚ))
      (q := (10400962428977599 / 160000000000000000 : ℚ))
      (U := (-(13666377355402748850127 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_120_3 :
    Uω (aρ 3) (bρ 3) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(28165630829855142778867 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1913956984259227 / 32000000000000000 : ℝ) ≤
      (-(28165630829855142778867 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1913956984259227 / 32000000000000000 : ℚ))
        (r' := (1913956984259227 / 1000000000000000 : ℚ))
        (U := (-(28165630829855142778867 / 10000000000000000000000 : ℚ)))
        (U' := (6491728185144857221133 / 10000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1894293572403 / 25600000000000 : ℚ))
      (s := (118385405077419 / 2000000000000000 : ℚ))
      (q := (1913956984259227 / 32000000000000000 : ℚ))
      (U := (-(28165630829855142778867 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_120_4 :
    Uω (aρ 4) (bρ 4) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(5970865177888741761793 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8082823260978207 / 160000000000000000 : ℝ) ≤
      (-(5970865177888741761793 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8082823260978207 / 160000000000000000 : ℚ))
        (r' := (8082823260978207 / 5000000000000000 : ℚ))
        (U := (-(5970865177888741761793 / 2000000000000000000000 : ℚ)))
        (U' := (960606625111258238207 / 2000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1894293572403 / 25600000000000 : ℚ))
      (s := (242175499456177 / 5000000000000000 : ℚ))
      (q := (8082823260978207 / 160000000000000000 : ℚ))
      (U := (-(5970865177888741761793 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_120_5 :
    Uω (aρ 5) (bρ 5) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(3422912528271636769997 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1043753523753371 / 32000000000000000 : ℝ) ≤
      (-(3422912528271636769997 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1043753523753371 / 32000000000000000 : ℚ))
        (r' := (1043753523753371 / 1000000000000000 : ℚ))
        (U := (-(3422912528271636769997 / 1000000000000000000000 : ℚ)))
        (U' := (42823373228363230003 / 1000000000000000000000 : ℚ))
        5 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1894293572403 / 25600000000000 : ℚ))
      (s := (48906792594187 / 2000000000000000 : ℚ))
      (q := (1043753523753371 / 32000000000000000 : ℚ))
      (U := (-(3422912528271636769997 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_120_6 :
    Uω (aρ 6) (bρ 6) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_120_7 :
    Uω (aρ 7) (bρ 7) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_120_8 :
    Uω (aρ 8) (bρ 8) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_120_9 :
    Uω (aρ 9) (bρ 9) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_120_10 :
    Uω (aρ 10) (bρ 10) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_120_11 :
    Uω (aρ 11) (bρ 11) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_120_12 :
    Uω (aρ 12) (bρ 12) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_120_13 :
    Uω (aρ 13) (bρ 13) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_120_14 :
    Uω (aρ 14) (bρ 14) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_120_15 :
    Uω (aρ 15) (bρ 15) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_120_16 :
    Uω (aρ 16) (bρ 16) (1894293572403 / 25600000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_120 :
    Uρ (1894293572403 / 25600000000000 : ℝ) ≤
      (-(24995593741306154908533 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_120_1 U_120_2 U_120_3 U_120_4 U_120_5 U_120_6 U_120_7 U_120_8 U_120_9 U_120_10
    U_120_11 U_120_12 U_120_13 U_120_14 U_120_15 U_120_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_121_1 :
    Uω (aρ 1) (bρ 1) (297034306573 / 4000000000000 : ℝ) ≤
      (-(6728535691238731355147 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1355700094784461 / 20000000000000000 : ℝ) ≤
      (-(6728535691238731355147 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1355700094784461 / 20000000000000000 : ℚ))
        (r' := (1355700094784461 / 1250000000000000 : ℚ))
        (U := (-(6728535691238731355147 / 2500000000000000000000 : ℚ)))
        (U' := (202936111761268644853 / 2500000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (297034306573 / 4000000000000 : ℚ))
      (s := (677611546436961 / 10000000000000000 : ℚ))
      (q := (1355700094784461 / 20000000000000000 : ℚ))
      (U := (-(6728535691238731355147 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_121_2 :
    Uω (aρ 2) (bρ 2) (297034306573 / 4000000000000 : ℝ) ≤
      (-(3411539798815513981353 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (652694077585557 / 10000000000000000 : ℝ) ≤
      (-(3411539798815513981353 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (652694077585557 / 10000000000000000 : ℚ))
        (r' := (652694077585557 / 625000000000000 : ℚ))
        (U := (-(3411539798815513981353 / 1250000000000000000000 : ℚ)))
        (U' := (54196102684486018647 / 1250000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (297034306573 / 4000000000000 : ℚ))
      (s := (325534309666807 / 5000000000000000 : ℚ))
      (q := (652694077585557 / 10000000000000000 : ℚ))
      (U := (-(3411539798815513981353 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_121_3 :
    Uω (aρ 3) (bρ 3) (297034306573 / 4000000000000 : ℝ) ≤
      (-(7030336219103306552713 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (600766225526559 / 10000000000000000 : ℝ) ≤
      (-(7030336219103306552713 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (600766225526559 / 10000000000000000 : ℚ))
        (r' := (600766225526559 / 312500000000000 : ℚ))
        (U := (-(7030336219103306552713 / 2500000000000000000000 : ℚ)))
        (U' := (1634003534646693447287 / 2500000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (297034306573 / 4000000000000 : ℚ))
      (s := (297304510782809 / 5000000000000000 : ℚ))
      (q := (600766225526559 / 10000000000000000 : ℚ))
      (U := (-(7030336219103306552713 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_121_4 :
    Uω (aρ 4) (bρ 4) (297034306573 / 4000000000000 : ℝ) ≤
      (-(3725030056597356522343 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (507916124857619 / 10000000000000000 : ℝ) ≤
      (-(3725030056597356522343 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (507916124857619 / 10000000000000000 : ℚ))
        (r' := (507916124857619 / 312500000000000 : ℚ))
        (U := (-(3725030056597356522343 / 1250000000000000000000 : ℚ)))
        (U' := (607139820277643477657 / 1250000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (297034306573 / 4000000000000 : ℚ))
      (s := (243601500646369 / 5000000000000000 : ℚ))
      (q := (507916124857619 / 10000000000000000 : ℚ))
      (U := (-(3725030056597356522343 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_121_5 :
    Uω (aρ 5) (bρ 5) (297034306573 / 4000000000000 : ℝ) ≤
      (-(682452605272557036629 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (82416279421253 / 2500000000000000 : ℝ) ≤
      (-(682452605272557036629 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (82416279421253 / 2500000000000000 : ℚ))
        (r' := (82416279421253 / 78125000000000 : ℚ))
        (U := (-(682452605272557036629 / 200000000000000000000 : ℚ)))
        (U' := (10694575027442963371 / 200000000000000000000 : ℚ))
        5 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (297034306573 / 4000000000000 : ℚ))
      (s := (62222726570631 / 2500000000000000 : ℚ))
      (q := (82416279421253 / 2500000000000000 : ℚ))
      (U := (-(682452605272557036629 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_121_6 :
    Uω (aρ 6) (bρ 6) (297034306573 / 4000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_121_7 :
    Uω (aρ 7) (bρ 7) (297034306573 / 4000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_121_8 :
    Uω (aρ 8) (bρ 8) (297034306573 / 4000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_121_9 :
    Uω (aρ 9) (bρ 9) (297034306573 / 4000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_121_10 :
    Uω (aρ 10) (bρ 10) (297034306573 / 4000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_121_11 :
    Uω (aρ 11) (bρ 11) (297034306573 / 4000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_121_12 :
    Uω (aρ 12) (bρ 12) (297034306573 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_121_13 :
    Uω (aρ 13) (bρ 13) (297034306573 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_121_14 :
    Uω (aρ 14) (bρ 14) (297034306573 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_121_15 :
    Uω (aρ 15) (bρ 15) (297034306573 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_121_16 :
    Uω (aρ 16) (bρ 16) (297034306573 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_121 :
    Uρ (297034306573 / 4000000000000 : ℝ) ≤
      (-(24981591939352846305661 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_121_1 U_121_2 U_121_3 U_121_4 U_121_5 U_121_6 U_121_7 U_121_8 U_121_9 U_121_10
    U_121_11 U_121_12 U_121_13 U_121_14 U_121_15 U_121_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_122_1 :
    Uω (aρ 1) (bρ 1) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(26875444254963523057139 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10887652932550481 / 160000000000000000 : ℝ) ≤
      (-(26875444254963523057139 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10887652932550481 / 160000000000000000 : ℚ))
        (r' := (10887652932550481 / 10000000000000000 : ℚ))
        (U := (-(26875444254963523057139 / 10000000000000000000000 : ℚ)))
        (U' := (850442957036476942861 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (9538727758657 / 128000000000000 : ℚ))
      (s := (170060182127183 / 2500000000000000 : ℚ))
      (q := (10887652932550481 / 160000000000000000 : ℚ))
      (U := (-(26875444254963523057139 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_122_2 :
    Uω (aρ 2) (bρ 2) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(27252045731424229280841 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10485247204589921 / 160000000000000000 : ℝ) ≤
      (-(27252045731424229280841 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10485247204589921 / 160000000000000000 : ℚ))
        (r' := (10485247204589921 / 10000000000000000 : ℚ))
        (U := (-(27252045731424229280841 / 10000000000000000000000 : ℚ)))
        (U' := (473841480575770719159 / 10000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (9538727758657 / 128000000000000 : ℚ))
      (s := (326854512511831 / 5000000000000000 : ℚ))
      (q := (10485247204589921 / 160000000000000000 : ℚ))
      (U := (-(27252045731424229280841 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_122_3 :
    Uω (aρ 3) (bρ 3) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(28077258208867713837771 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9654730408809841 / 160000000000000000 : ℝ) ≤
      (-(28077258208867713837771 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9654730408809841 / 160000000000000000 : ℚ))
        (r' := (9654730408809841 / 5000000000000000 : ℚ))
        (U := (-(28077258208867713837771 / 10000000000000000000000 : ℚ)))
        (U' := (6580100806132286162229 / 10000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (9538727758657 / 128000000000000 : ℚ))
      (s := (18665329121911 / 312500000000000 : ℚ))
      (q := (9654730408809841 / 160000000000000000 : ℚ))
      (U := (-(28077258208867713837771 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_122_4 :
    Uω (aρ 4) (bρ 4) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(14873235281136487034493 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8170472638651729 / 160000000000000000 : ℝ) ≤
      (-(14873235281136487034493 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8170472638651729 / 160000000000000000 : ℚ))
        (r' := (8170472638651729 / 5000000000000000 : ℚ))
        (U := (-(14873235281136487034493 / 5000000000000000000000 : ℚ)))
        (U' := (2455444226363512965507 / 5000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (9538727758657 / 128000000000000 : ℚ))
      (s := (122513122924097 / 2500000000000000 : ℚ))
      (q := (8170472638651729 / 160000000000000000 : ℚ))
      (U := (-(14873235281136487034493 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_122_5 :
    Uω (aρ 5) (bρ 5) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(6803594680306818344917 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5330134507460841 / 160000000000000000 : ℝ) ≤
      (-(6803594680306818344917 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5330134507460841 / 160000000000000000 : ℚ))
        (r' := (5330134507460841 / 5000000000000000 : ℚ))
        (U := (-(6803594680306818344917 / 2000000000000000000000 : ℚ)))
        (U' := (127877122693181655083 / 2000000000000000000000 : ℚ))
        5 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (9538727758657 / 128000000000000 : ℚ))
      (s := (253200144632527 / 10000000000000000 : ℚ))
      (q := (5330134507460841 / 160000000000000000 : ℚ))
      (U := (-(6803594680306818344917 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_122_6 :
    Uω (aρ 6) (bρ 6) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_122_7 :
    Uω (aρ 7) (bρ 7) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_122_8 :
    Uω (aρ 8) (bρ 8) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_122_9 :
    Uω (aρ 9) (bρ 9) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_122_10 :
    Uω (aρ 10) (bρ 10) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_122_11 :
    Uω (aρ 11) (bρ 11) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_122_12 :
    Uω (aρ 12) (bρ 12) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_122_13 :
    Uω (aρ 13) (bρ 13) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_122_14 :
    Uω (aρ 14) (bρ 14) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_122_15 :
    Uω (aρ 15) (bρ 15) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_122_16 :
    Uω (aρ 16) (bρ 16) (9538727758657 / 128000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_122 :
    Uρ (9538727758657 / 128000000000000 : ℝ) ≤
      (-(6241937591781720172913 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_122_1 U_122_2 U_122_3 U_122_4 U_122_5 U_122_6 U_122_7 U_122_8 U_122_9 U_122_10
    U_122_11 U_122_12 U_122_13 U_122_14 U_122_15 U_122_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_123_1 :
    Uω (aρ 1) (bρ 1) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(5367379005824790420369 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5464852496684989 / 80000000000000000 : ℝ) ≤
      (-(5367379005824790420369 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5464852496684989 / 80000000000000000 : ℚ))
        (r' := (5464852496684989 / 5000000000000000 : ℚ))
        (U := (-(5367379005824790420369 / 2000000000000000000000 : ℚ)))
        (U' := (177798436575209579631 / 2000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4786178853489 / 64000000000000 : ℚ))
      (s := (682869896398591 / 10000000000000000 : ℚ))
      (q := (5464852496684989 / 80000000000000000 : ℚ))
      (U := (-(5367379005824790420369 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_123_2 :
    Uω (aρ 2) (bρ 2) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(27211935407585621453431 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5263694164444461 / 80000000000000000 : ℝ) ≤
      (-(27211935407585621453431 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5263694164444461 / 80000000000000000 : ℚ))
        (r' := (5263694164444461 / 5000000000000000 : ℚ))
        (U := (-(27211935407585621453431 / 10000000000000000000000 : ℚ)))
        (U' := (513951804414378546569 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4786178853489 / 64000000000000 : ℚ))
      (s := (656349325848459 / 10000000000000000 : ℚ))
      (q := (5263694164444461 / 80000000000000000 : ℚ))
      (U := (-(27211935407585621453431 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_123_3 :
    Uω (aρ 3) (bρ 3) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(14016684503152133467349 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4848598687282497 / 80000000000000000 : ℝ) ≤
      (-(14016684503152133467349 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4848598687282497 / 80000000000000000 : ℚ))
        (r' := (4848598687282497 / 2500000000000000 : ℚ))
        (U := (-(14016684503152133467349 / 5000000000000000000000 : ℚ)))
        (U' := (3311995004347866532651 / 5000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4786178853489 / 64000000000000 : ℚ))
      (s := (9374555670437 / 156250000000000 : ℚ))
      (q := (4848598687282497 / 80000000000000000 : ℚ))
      (U := (-(14016684503152133467349 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_123_4 :
    Uω (aρ 4) (bρ 4) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(29693012286484085391417 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (821426753229409 / 16000000000000000 : ℝ) ≤
      (-(29693012286484085391417 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (821426753229409 / 16000000000000000 : ℚ))
        (r' := (821426753229409 / 500000000000000 : ℚ))
        (U := (-(29693012286484085391417 / 10000000000000000000000 : ℚ)))
        (U' := (4964346728515914608583 / 10000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4786178853489 / 64000000000000 : ℚ))
      (s := (98579902737821 / 2000000000000000 : ℚ))
      (q := (821426753229409 / 16000000000000000 : ℚ))
      (U := (-(29693012286484085391417 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_123_5 :
    Uω (aρ 5) (bρ 5) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(16957536789013437420659 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2692632327572469 / 80000000000000000 : ℝ) ≤
      (-(16957536789013437420659 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2692632327572469 / 80000000000000000 : ℚ))
        (r' := (2692632327572469 / 2500000000000000 : ℚ))
        (U := (-(16957536789013437420659 / 5000000000000000000000 : ℚ)))
        (U' := (371142718486562579341 / 5000000000000000000000 : ℚ))
        5 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4786178853489 / 64000000000000 : ℚ))
      (s := (257464073380461 / 10000000000000000 : ℚ))
      (q := (2692632327572469 / 80000000000000000 : ℚ))
      (U := (-(16957536789013437420659 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_123_6 :
    Uω (aρ 6) (bρ 6) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_123_7 :
    Uω (aρ 7) (bρ 7) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_123_8 :
    Uω (aρ 8) (bρ 8) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_123_9 :
    Uω (aρ 9) (bρ 9) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_123_10 :
    Uω (aρ 10) (bρ 10) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_123_11 :
    Uω (aρ 11) (bρ 11) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_123_12 :
    Uω (aρ 12) (bρ 12) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_123_13 :
    Uω (aρ 13) (bρ 13) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_123_14 :
    Uω (aρ 14) (bρ 14) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_123_15 :
    Uω (aρ 15) (bρ 15) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_123_16 :
    Uω (aρ 16) (bρ 16) (4786178853489 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_123 :
    Uρ (4786178853489 / 64000000000000 : ℝ) ≤
      (-(311925788326356217817 / 125000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_123_1 U_123_2 U_123_3 U_123_4 U_123_5 U_123_6 U_123_7 U_123_8 U_123_9 U_123_10
    U_123_11 U_123_12 U_123_13 U_123_14 U_123_15 U_123_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
