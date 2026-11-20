/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U48) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_580_1 :
    Uω (aρ 1) (bρ 1) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(4005405391022337117569 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53596624766068143 / 80000000000000000 : ℝ) ≤
      (-(4005405391022337117569 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53596624766068143 / 80000000000000000 : ℚ))
        (r' := (53596624766068143 / 40000000000000000 : ℚ))
        (U := (-(4005405391022337117569 / 10000000000000000000000 : ℚ)))
        (U' := (2926066411977662882431 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (6699553964704067 / 10000000000000000 : ℚ))
      (q := (53596624766068143 / 80000000000000000 : ℚ))
      (U := (-(4005405391022337117569 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_2 :
    Uω (aρ 2) (bρ 2) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(2020574381616309005321 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53405394319890923 / 80000000000000000 : ℝ) ≤
      (-(2020574381616309005321 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53405394319890923 / 80000000000000000 : ℚ))
        (r' := (53405394319890923 / 40000000000000000 : ℚ))
        (U := (-(2020574381616309005321 / 5000000000000000000000 : ℚ)))
        (U' := (1445161519883690994679 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (3337757682834881 / 5000000000000000 : ℚ))
      (q := (53405394319890923 / 80000000000000000 : ℚ))
      (U := (-(2020574381616309005321 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_3 :
    Uω (aρ 3) (bρ 3) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(4113002484966424445947 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53023032038383907 / 80000000000000000 : ℝ) ≤
      (-(4113002484966424445947 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53023032038383907 / 80000000000000000 : ℚ))
        (r' := (53023032038383907 / 40000000000000000 : ℚ))
        (U := (-(4113002484966424445947 / 10000000000000000000000 : ℚ)))
        (U' := (2818469318033575554053 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (25887972272043 / 39062500000000 : ℚ))
      (q := (53023032038383907 / 80000000000000000 : ℚ))
      (U := (-(4113002484966424445947 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_4 :
    Uω (aρ 4) (bρ 4) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(1058358803653668769017 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (52388291041572979 / 80000000000000000 : ℝ) ≤
      (-(1058358803653668769017 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (52388291041572979 / 80000000000000000 : ℚ))
        (r' := (52388291041572979 / 40000000000000000 : ℚ))
        (U := (-(1058358803653668769017 / 2500000000000000000000 : ℚ)))
        (U' := (674509147096331230983 / 2500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (1636732458376319 / 2500000000000000 : ℚ))
      (q := (52388291041572979 / 80000000000000000 : ℚ))
      (U := (-(1058358803653668769017 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_5 :
    Uω (aρ 5) (bρ 5) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(220975577212004283547 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10284496504502127 / 16000000000000000 : ℝ) ≤
      (-(220975577212004283547 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10284496504502127 / 16000000000000000 : ℚ))
        (r' := (10284496504502127 / 8000000000000000 : ℚ))
        (U := (-(220975577212004283547 / 500000000000000000000 : ℚ)))
        (U' := (125598012937995716453 / 500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (642366762307469 / 1000000000000000 : ℚ))
      (q := (10284496504502127 / 16000000000000000 : ℚ))
      (U := (-(220975577212004283547 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_6 :
    Uω (aρ 6) (bρ 6) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(4692195289343839263543 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (50039220376910659 / 80000000000000000 : ℝ) ≤
      (-(4692195289343839263543 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (50039220376910659 / 80000000000000000 : ℚ))
        (r' := (50039220376910659 / 40000000000000000 : ℚ))
        (U := (-(4692195289343839263543 / 10000000000000000000000 : ℚ)))
        (U' := (2239276513656160736457 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (780636557726837 / 1250000000000000 : ℚ))
      (q := (50039220376910659 / 80000000000000000 : ℚ))
      (U := (-(4692195289343839263543 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_7 :
    Uω (aρ 7) (bρ 7) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(5075794398165442137843 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48156069995982091 / 80000000000000000 : ℝ) ≤
      (-(5075794398165442137843 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48156069995982091 / 80000000000000000 : ℚ))
        (r' := (48156069995982091 / 40000000000000000 : ℚ))
        (U := (-(5075794398165442137843 / 10000000000000000000000 : ℚ)))
        (U' := (1855677404834557862157 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (2998983123671277 / 5000000000000000 : ℚ))
      (q := (48156069995982091 / 80000000000000000 : ℚ))
      (U := (-(5075794398165442137843 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_8 :
    Uω (aρ 8) (bρ 8) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(1399444218052103159183 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9141377038259751 / 16000000000000000 : ℝ) ≤
      (-(1399444218052103159183 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9141377038259751 / 16000000000000000 : ℚ))
        (r' := (9141377038259751 / 8000000000000000 : ℚ))
        (U := (-(1399444218052103159183 / 2500000000000000000000 : ℚ)))
        (U' := (333423732697896840817 / 2500000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (141730292437793 / 250000000000000 : ℚ))
      (q := (9141377038259751 / 16000000000000000 : ℚ))
      (U := (-(1399444218052103159183 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_9 :
    Uω (aρ 9) (bρ 9) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(6289329057577266237567 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (42652834387923127 / 80000000000000000 : ℝ) ≤
      (-(6289329057577266237567 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (42652834387923127 / 80000000000000000 : ℚ))
        (r' := (42652834387923127 / 40000000000000000 : ℚ))
        (U := (-(6289329057577266237567 / 10000000000000000000000 : ℚ)))
        (U' := (642142745422733762433 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (5246664625027813 / 10000000000000000 : ℚ))
      (q := (42652834387923127 / 80000000000000000 : ℚ))
      (U := (-(6289329057577266237567 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_10 :
    Uω (aρ 10) (bρ 10) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(7187502901981604046617 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (38988874802318187 / 80000000000000000 : ℝ) ≤
      (-(7187502901981604046617 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (38988874802318187 / 80000000000000000 : ℚ))
        (r' := (38988874802318187 / 20000000000000000 : ℚ))
        (U := (-(7187502901981604046617 / 10000000000000000000000 : ℚ)))
        (U' := (6675440704018395953383 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (2359616881060789 / 5000000000000000 : ℚ))
      (q := (38988874802318187 / 80000000000000000 : ℚ))
      (U := (-(7187502901981604046617 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_11 :
    Uω (aρ 11) (bρ 11) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(8341281510819861628441 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (34740233532064187 / 80000000000000000 : ℝ) ≤
      (-(8341281510819861628441 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (34740233532064187 / 80000000000000000 : ℚ))
        (r' := (34740233532064187 / 20000000000000000 : ℚ))
        (U := (-(8341281510819861628441 / 10000000000000000000000 : ℚ)))
        (U' := (5521662095180138371559 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (2037775035381539 / 5000000000000000 : ℚ))
      (q := (34740233532064187 / 80000000000000000 : ℚ))
      (U := (-(8341281510819861628441 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_12 :
    Uω (aρ 12) (bρ 12) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(4914793623665919405137 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29936183804283567 / 80000000000000000 : ℝ) ≤
      (-(4914793623665919405137 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (29936183804283567 / 80000000000000000 : ℚ))
        (r' := (29936183804283567 / 20000000000000000 : ℚ))
        (U := (-(4914793623665919405137 / 5000000000000000000000 : ℚ)))
        (U' := (2016678179334080594863 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (3298237735502923 / 10000000000000000 : ℚ))
      (q := (29936183804283567 / 80000000000000000 : ℚ))
      (U := (-(4914793623665919405137 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_13 :
    Uω (aρ 13) (bρ 13) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(11831206847900431713959 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (980228201742283 / 3200000000000000 : ℝ) ≤
      (-(11831206847900431713959 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (980228201742283 / 3200000000000000 : ℚ))
        (r' := (980228201742283 / 800000000000000 : ℚ))
        (U := (-(11831206847900431713959 / 10000000000000000000000 : ℚ)))
        (U' := (2031736758099568286041 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (23399997869163 / 100000000000000 : ℚ))
      (q := (980228201742283 / 3200000000000000 : ℚ))
      (U := (-(11831206847900431713959 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_14 :
    Uω (aρ 14) (bρ 14) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(7628136779712544570147 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17398765891887423 / 80000000000000000 : ℝ) ≤
      (-(7628136779712544570147 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17398765891887423 / 80000000000000000 : ℚ))
        (r' := (17398765891887423 / 10000000000000000 : ℚ))
        (U := (-(7628136779712544570147 / 5000000000000000000000 : ℚ)))
        (U' := (2769070924787455429853 / 5000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (43290236447347 / 64000000000000 : ℚ))
      (s := (907192284043887 / 10000000000000000 : ℚ))
      (q := (17398765891887423 / 80000000000000000 : ℚ))
      (U := (-(7628136779712544570147 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_580_15 :
    Uω (aρ 15) (bρ 15) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_580_16 :
    Uω (aρ 16) (bρ 16) (43290236447347 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_580 :
    Uρ (43290236447347 / 64000000000000 : ℝ) ≤
      (-(837778362582075301389 / 1250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_580_1 U_580_2 U_580_3 U_580_4 U_580_5 U_580_6 U_580_7 U_580_8 U_580_9 U_580_10
    U_580_11 U_580_12 U_580_13 U_580_14 U_580_15 U_580_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_581_1 :
    Uω (aρ 1) (bρ 1) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(3993303889330489471621 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3353845249473793 / 5000000000000000 : ℝ) ≤
      (-(3993303889330489471621 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3353845249473793 / 5000000000000000 : ℚ))
        (r' := (3353845249473793 / 2500000000000000 : ℚ))
        (U := (-(3993303889330489471621 / 10000000000000000000000 : ℚ)))
        (U' := (2938167913669510528379 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (838458299634709 / 1250000000000000 : ℚ))
      (q := (3353845249473793 / 5000000000000000 : ℚ))
      (U := (-(3993303889330489471621 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_2 :
    Uω (aρ 2) (bρ 2) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(4029003710659338433683 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3341893428444077 / 5000000000000000 : ℝ) ≤
      (-(4029003710659338433683 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3341893428444077 / 5000000000000000 : ℚ))
        (r' := (3341893428444077 / 2500000000000000 : ℚ))
        (U := (-(4029003710659338433683 / 10000000000000000000000 : ℚ)))
        (U' := (2902468092340661566317 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (835453515683601 / 1250000000000000 : ℚ))
      (q := (3341893428444077 / 5000000000000000 : ℚ))
      (U := (-(4029003710659338433683 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_3 :
    Uω (aρ 3) (bρ 3) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(4100769167401937979183 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13271984122260781 / 20000000000000000 : ℝ) ≤
      (-(4100769167401937979183 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13271984122260781 / 20000000000000000 : ℚ))
        (r' := (13271984122260781 / 10000000000000000 : ℚ))
        (U := (-(4100769167401937979183 / 10000000000000000000000 : ℚ)))
        (U' := (2830702635598062020817 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (6635434640303281 / 10000000000000000 : ℚ))
      (q := (13271984122260781 / 20000000000000000 : ℚ))
      (U := (-(4100769167401937979183 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_4 :
    Uω (aρ 4) (bρ 4) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(4221051777138668487973 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13113301484853793 / 20000000000000000 : ℝ) ≤
      (-(4221051777138668487973 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13113301484853793 / 20000000000000000 : ℚ))
        (r' := (13113301484853793 / 10000000000000000 : ℚ))
        (U := (-(4221051777138668487973 / 10000000000000000000000 : ℚ)))
        (U' := (2710420025861331512027 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (6555046183961293 / 10000000000000000 : ℚ))
      (q := (13113301484853793 / 20000000000000000 : ℚ))
      (U := (-(4221051777138668487973 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_5 :
    Uω (aρ 5) (bρ 5) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(4406890640283341706941 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3217963957236223 / 5000000000000000 : ℝ) ≤
      (-(4406890640283341706941 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3217963957236223 / 5000000000000000 : ℚ))
        (r' := (3217963957236223 / 2500000000000000 : ℚ))
        (U := (-(4406890640283341706941 / 10000000000000000000000 : ℚ)))
        (U' := (2524581162716658293059 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (25124181435107 / 39062500000000 : ℚ))
      (q := (3217963957236223 / 5000000000000000 : ℚ))
      (U := (-(4406890640283341706941 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_6 :
    Uω (aρ 6) (bρ 6) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(292450859203226838757 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (782878455982433 / 1250000000000000 : ℝ) ≤
      (-(292450859203226838757 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (782878455982433 / 1250000000000000 : ℚ))
        (r' := (782878455982433 / 625000000000000 : ℚ))
        (U := (-(292450859203226838757 / 625000000000000000000 : ℚ)))
        (U' := (140766128484273161243 / 625000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (1563307572325357 / 2500000000000000 : ℚ))
      (q := (782878455982433 / 1250000000000000 : ℚ))
      (U := (-(292450859203226838757 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_7 :
    Uω (aρ 7) (bρ 7) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(2531139197092148791153 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1506912555172117 / 2500000000000000 : ℝ) ≤
      (-(2531139197092148791153 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1506912555172117 / 2500000000000000 : ℚ))
        (r' := (1506912555172117 / 1250000000000000 : ℚ))
        (U := (-(2531139197092148791153 / 5000000000000000000000 : ℚ)))
        (U' := (934596704407851208847 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (1501534203929859 / 2500000000000000 : ℚ))
      (q := (1506912555172117 / 2500000000000000 : ℚ))
      (U := (-(2531139197092148791153 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_8 :
    Uω (aρ 8) (bρ 8) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(5583477732194065256547 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5721536107007471 / 10000000000000000 : ℝ) ≤
      (-(5583477732194065256547 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5721536107007471 / 10000000000000000 : ℚ))
        (r' := (5721536107007471 / 5000000000000000 : ℚ))
        (U := (-(5583477732194065256547 / 10000000000000000000000 : ℚ)))
        (U' := (1347994070805934743453 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (2838725119848721 / 5000000000000000 : ℚ))
      (q := (5721536107007471 / 10000000000000000 : ℚ))
      (U := (-(5583477732194065256547 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_9 :
    Uω (aρ 9) (bρ 9) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(1568469855154944946347 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2669923899943569 / 5000000000000000 : ℝ) ≤
      (-(1568469855154944946347 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2669923899943569 / 5000000000000000 : ℚ))
        (r' := (2669923899943569 / 2500000000000000 : ℚ))
        (U := (-(1568469855154944946347 / 2500000000000000000000 : ℚ)))
        (U' := (164398095595055053653 / 2500000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (656879906727097 / 1250000000000000 : ℚ))
      (q := (2669923899943569 / 5000000000000000 : ℚ))
      (U := (-(1568469855154944946347 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_10 :
    Uω (aρ 10) (bρ 10) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(7170328599460265511283 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4881986626059351 / 10000000000000000 : ℝ) ≤
      (-(7170328599460265511283 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4881986626059351 / 10000000000000000 : ℚ))
        (r' := (4881986626059351 / 2500000000000000 : ℚ))
        (U := (-(7170328599460265511283 / 10000000000000000000000 : ℚ)))
        (U' := (6692615006539734488717 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (2363937969828101 / 5000000000000000 : ℚ))
      (q := (4881986626059351 / 10000000000000000 : ℚ))
      (U := (-(7170328599460265511283 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_11 :
    Uω (aρ 11) (bρ 11) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(8321398900107086323937 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1087792965586551 / 2500000000000000 : ℝ) ≤
      (-(8321398900107086323937 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1087792965586551 / 2500000000000000 : ℚ))
        (r' := (1087792965586551 / 625000000000000 : ℚ))
        (U := (-(8321398900107086323937 / 10000000000000000000000 : ℚ)))
        (U' := (5541544705892913676063 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (1021180759608727 / 2500000000000000 : ℚ))
      (q := (1087792965586551 / 2500000000000000 : ℚ))
      (U := (-(8321398900107086323937 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_12 :
    Uω (aρ 12) (bρ 12) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(39220117818480693483 / 40000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (937805962756639 / 2500000000000000 : ℝ) ≤
      (-(39220117818480693483 / 40000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (937805962756639 / 2500000000000000 : ℚ))
        (r' := (937805962756639 / 625000000000000 : ℚ))
        (U := (-(39220117818480693483 / 40000000000000000000 : ℚ)))
        (U' := (16231656605519306517 / 40000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (827131778120153 / 2500000000000000 : ℚ))
      (q := (937805962756639 / 2500000000000000 : ℚ))
      (U := (-(39220117818480693483 / 40000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_13 :
    Uω (aρ 13) (bρ 13) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(11796635347326533752359 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1229528577838203 / 4000000000000000 : ℝ) ≤
      (-(11796635347326533752359 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1229528577838203 / 4000000000000000 : ℚ))
        (r' := (1229528577838203 / 1000000000000000 : ℚ))
        (U := (-(11796635347326533752359 / 10000000000000000000000 : ℚ)))
        (U' := (2066308258673466247641 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (470620808242703 / 2000000000000000 : ℚ))
      (q := (1229528577838203 / 4000000000000000 : ℚ))
      (U := (-(11796635347326533752359 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_14 :
    Uω (aρ 14) (bρ 14) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(1516831959140549096717 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (219405873684427 / 1000000000000000 : ℝ) ≤
      (-(1516831959140549096717 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (219405873684427 / 1000000000000000 : ℚ))
        (r' := (219405873684427 / 125000000000000 : ℚ))
        (U := (-(1516831959140549096717 / 1000000000000000000000 : ℚ)))
        (U' := (562609581759450903283 / 1000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (2708884727561 / 4000000000000 : ℚ))
      (s := (23437647768901 / 250000000000000 : ℚ))
      (q := (219405873684427 / 1000000000000000 : ℚ))
      (U := (-(1516831959140549096717 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_581_15 :
    Uω (aρ 15) (bρ 15) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_581_16 :
    Uω (aρ 16) (bρ 16) (2708884727561 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_581 :
    Uρ (2708884727561 / 4000000000000 : ℝ) ≤
      (-(41775748645483768217 / 62500000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_581_1 U_581_2 U_581_3 U_581_4 U_581_5 U_581_6 U_581_7 U_581_8 U_581_9 U_581_10
    U_581_11 U_581_12 U_581_13 U_581_14 U_581_15 U_581_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_582_1 :
    Uω (aρ 1) (bρ 1) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(497652126834867869363 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53726423216529177 / 80000000000000000 : ℝ) ≤
      (-(497652126834867869363 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53726423216529177 / 80000000000000000 : ℚ))
        (r' := (53726423216529177 / 40000000000000000 : ℚ))
        (U := (-(497652126834867869363 / 1250000000000000000000 : ℚ)))
        (U' := (368781848540132130637 / 1250000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (6715778829310263 / 10000000000000000 : ℚ))
      (q := (53726423216529177 / 80000000000000000 : ℚ))
      (U := (-(497652126834867869363 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_2 :
    Uω (aρ 2) (bρ 2) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(4016873391124482683507 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53535195386577869 / 80000000000000000 : ℝ) ≤
      (-(4016873391124482683507 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53535195386577869 / 80000000000000000 : ℚ))
        (r' := (53535195386577869 / 40000000000000000 : ℚ))
        (U := (-(4016873391124482683507 / 10000000000000000000000 : ℚ)))
        (U' := (2914598411875517316493 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (1672935221083109 / 2500000000000000 : ℚ))
      (q := (53535195386577869 / 80000000000000000 : ℚ))
      (U := (-(4016873391124482683507 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_3 :
    Uω (aρ 3) (bρ 3) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(4088550799468137633081 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53152840926370277 / 80000000000000000 : ℝ) ≤
      (-(4088550799468137633081 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53152840926370277 / 80000000000000000 : ℚ))
        (r' := (53152840926370277 / 40000000000000000 : ℚ))
        (U := (-(4088550799468137633081 / 10000000000000000000000 : ℚ)))
        (U' := (2842921003531862366919 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (3321774187815269 / 5000000000000000 : ℚ))
      (q := (53152840926370277 / 80000000000000000 : ℚ))
      (U := (-(4088550799468137633081 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_4 :
    Uω (aρ 4) (bρ 4) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(4208683663139425892631 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (52518120797927097 / 80000000000000000 : ℝ) ≤
      (-(4208683663139425892631 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (52518120797927097 / 80000000000000000 : ℚ))
        (r' := (52518120797927097 / 40000000000000000 : ℚ))
        (U := (-(4208683663139425892631 / 10000000000000000000000 : ℚ)))
        (U' := (2722788139860574107369 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (6563162524584743 / 10000000000000000 : ℚ))
      (q := (52518120797927097 / 80000000000000000 : ℚ))
      (U := (-(4208683663139425892631 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_5 :
    Uω (aρ 5) (bρ 5) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(549285708176747111411 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10310472800733289 / 16000000000000000 : ℝ) ≤
      (-(549285708176747111411 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10310472800733289 / 16000000000000000 : ℚ))
        (r' := (10310472800733289 / 8000000000000000 : ℚ))
        (U := (-(549285708176747111411 / 1250000000000000000000 : ℚ)))
        (U' := (317148267198252888589 / 1250000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (321995662267729 / 500000000000000 : ℚ))
      (q := (10310472800733289 / 16000000000000000 : ℚ))
      (U := (-(549285708176747111411 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_6 :
    Uω (aρ 6) (bρ 6) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(466624908802661578893 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (50169221724601889 / 80000000000000000 : ℝ) ≤
      (-(466624908802661578893 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (50169221724601889 / 80000000000000000 : ℚ))
        (r' := (50169221724601889 / 40000000000000000 : ℚ))
        (U := (-(466624908802661578893 / 1000000000000000000000 : ℚ)))
        (U' := (226522271497338421107 / 1000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (6261368050728441 / 10000000000000000 : ℚ))
      (q := (50169221724601889 / 80000000000000000 : ℚ))
      (U := (-(466624908802661578893 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_7 :
    Uω (aρ 7) (bρ 7) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(631097595537542197029 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48286332904819101 / 80000000000000000 : ℝ) ≤
      (-(631097595537542197029 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48286332904819101 / 80000000000000000 : ℚ))
        (r' := (48286332904819101 / 40000000000000000 : ℚ))
        (U := (-(631097595537542197029 / 1250000000000000000000 : ℚ)))
        (U' := (235336379837457802971 / 1250000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (751788403317843 / 1250000000000000 : ℚ))
      (q := (48286332904819101 / 80000000000000000 : ℚ))
      (U := (-(631097595537542197029 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_8 :
    Uω (aρ 8) (bρ 8) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(1392299831538579844629 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (45837691069481813 / 80000000000000000 : ℝ) ≤
      (-(1392299831538579844629 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (45837691069481813 / 80000000000000000 : ℚ))
        (r' := (45837691069481813 / 40000000000000000 : ℚ))
        (U := (-(1392299831538579844629 / 2500000000000000000000 : ℚ)))
        (U' := (340568119211420155371 / 2500000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (2842844209524211 / 5000000000000000 : ℚ))
      (q := (45837691069481813 / 80000000000000000 : ℚ))
      (U := (-(1392299831538579844629 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_9 :
    Uω (aρ 9) (bρ 9) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(6258454383988677137099 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8556945424869233 / 16000000000000000 : ℝ) ≤
      (-(6258454383988677137099 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8556945424869233 / 16000000000000000 : ℚ))
        (r' := (8556945424869233 / 8000000000000000 : ℚ))
        (U := (-(6258454383988677137099 / 10000000000000000000000 : ℚ)))
        (U' := (673017419011322862901 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (526341306112451 / 1000000000000000 : ℚ))
      (q := (8556945424869233 / 16000000000000000 : ℚ))
      (U := (-(6258454383988677137099 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_10 :
    Uω (aρ 10) (bρ 10) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(447074103633723834573 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7824580743660861 / 16000000000000000 : ℝ) ≤
      (-(447074103633723834573 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7824580743660861 / 16000000000000000 : ℚ))
        (r' := (7824580743660861 / 4000000000000000 : ℚ))
        (U := (-(447074103633723834573 / 625000000000000000000 : ℚ)))
        (U' := (419359871741276165427 / 625000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (947303248621809 / 2000000000000000 : ℚ))
      (q := (7824580743660861 / 16000000000000000 : ℚ))
      (U := (-(447074103633723834573 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_11 :
    Uω (aρ 11) (bρ 11) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(518847554900022932309 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6975699670642717 / 16000000000000000 : ℝ) ≤
      (-(518847554900022932309 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6975699670642717 / 16000000000000000 : ℚ))
        (r' := (6975699670642717 / 4000000000000000 : ℚ))
        (U := (-(518847554900022932309 / 625000000000000000000 : ℚ)))
        (U' := (347586420474977067691 / 625000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (818778305608273 / 2000000000000000 : ℚ))
      (q := (6975699670642717 / 16000000000000000 : ℚ))
      (U := (-(518847554900022932309 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_12 :
    Uω (aρ 12) (bρ 12) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(9780547872498677856713 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30083349528978241 / 80000000000000000 : ℝ) ≤
      (-(9780547872498677856713 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30083349528978241 / 80000000000000000 : ℚ))
        (r' := (30083349528978241 / 20000000000000000 : ℚ))
        (U := (-(9780547872498677856713 / 10000000000000000000000 : ℚ)))
        (U' := (4082395733501322143287 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (3318804418667529 / 10000000000000000 : ℚ))
      (q := (30083349528978241 / 80000000000000000 : ℚ))
      (U := (-(9780547872498677856713 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_13 :
    Uω (aρ 13) (bρ 13) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(5881127756237673751163 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24675259029316617 / 80000000000000000 : ℝ) ≤
      (-(5881127756237673751163 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24675259029316617 / 80000000000000000 : ℚ))
        (r' := (24675259029316617 / 20000000000000000 : ℚ))
        (U := (-(5881127756237673751163 / 5000000000000000000000 : ℚ)))
        (U' := (1050344046762326248837 / 5000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (2366163535347123 / 10000000000000000 : ℚ))
      (q := (24675259029316617 / 80000000000000000 : ℚ))
      (U := (-(5881127756237673751163 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_14 :
    Uω (aρ 14) (bρ 14) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(3770781227787045933889 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17702646404448193 / 80000000000000000 : ℝ) ≤
      (-(3770781227787045933889 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17702646404448193 / 80000000000000000 : ℚ))
        (r' := (17702646404448193 / 10000000000000000 : ℚ))
        (U := (-(3770781227787045933889 / 2500000000000000000000 : ℚ)))
        (U' := (1427822624462954066111 / 2500000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (8678814966921 / 12800000000000 : ℚ))
      (s := (966937664175017 / 10000000000000000 : ℚ))
      (q := (17702646404448193 / 80000000000000000 : ℚ))
      (U := (-(3770781227787045933889 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_582_15 :
    Uω (aρ 15) (bρ 15) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_582_16 :
    Uω (aρ 16) (bρ 16) (8678814966921 / 12800000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_582 :
    Uρ (8678814966921 / 12800000000000 : ℝ) ≤
      (-(1333233638414966829353 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_582_1 U_582_2 U_582_3 U_582_4 U_582_5 U_582_6 U_582_7 U_582_8 U_582_9 U_582_10
    U_582_11 U_582_12 U_582_13 U_582_14 U_582_15 U_582_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_583_1 :
    Uω (aρ 1) (bρ 1) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(1984572365875415154351 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26895661220457821 / 40000000000000000 : ℝ) ≤
      (-(1984572365875415154351 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26895661220457821 / 40000000000000000 : ℚ))
        (r' := (26895661220457821 / 20000000000000000 : ℚ))
        (U := (-(1984572365875415154351 / 5000000000000000000000 : ℚ)))
        (U' := (1481163535624584845649 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (1680972815350587 / 2500000000000000 : ℚ))
      (q := (26895661220457821 / 40000000000000000 : ℚ))
      (U := (-(1984572365875415154351 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_2 :
    Uω (aρ 2) (bρ 2) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(4004757768924670619983 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5360009591432243 / 8000000000000000 : ℝ) ≤
      (-(4004757768924670619983 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5360009591432243 / 8000000000000000 : ℚ))
        (r' := (5360009591432243 / 4000000000000000 : ℚ))
        (U := (-(4004757768924670619983 / 10000000000000000000000 : ℚ)))
        (U' := (2926714034075329380017 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (1339970728452809 / 2000000000000000 : ℚ))
      (q := (5360009591432243 / 8000000000000000 : ℚ))
      (U := (-(4004757768924670619983 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_3 :
    Uω (aρ 3) (bρ 3) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(815269468933069742969 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1064354907008283 / 1600000000000000 : ℝ) ≤
      (-(815269468933069742969 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1064354907008283 / 1600000000000000 : ℚ))
        (r' := (1064354907008283 / 800000000000000 : ℚ))
        (U := (-(815269468933069742969 / 2000000000000000000000 : ℚ)))
        (U' := (571024891666930257031 / 2000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (266066484305479 / 400000000000000 : ℚ))
      (q := (1064354907008283 / 1600000000000000 : ℚ))
      (U := (-(815269468933069742969 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_4 :
    Uω (aρ 4) (bρ 4) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(2098165417361143833627 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26291517808627243 / 40000000000000000 : ℝ) ≤
      (-(2098165417361143833627 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26291517808627243 / 40000000000000000 : ℚ))
        (r' := (26291517808627243 / 20000000000000000 : ℚ))
        (U := (-(2098165417361143833627 / 5000000000000000000000 : ℚ)))
        (U' := (1367570484138856166373 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (6571278855412059 / 10000000000000000 : ℚ))
      (q := (26291517808627243 / 40000000000000000 : ℚ))
      (U := (-(2098165417361143833627 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_5 :
    Uω (aρ 5) (bρ 5) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(4381696579422479512909 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25808652293284761 / 40000000000000000 : ℝ) ≤
      (-(4381696579422479512909 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25808652293284761 / 40000000000000000 : ℚ))
        (r' := (25808652293284761 / 20000000000000000 : ℚ))
        (U := (-(4381696579422479512909 / 10000000000000000000000 : ℚ)))
        (U' := (2549775223577520487091 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (3224018008537909 / 5000000000000000 : ℚ))
      (q := (25808652293284761 / 40000000000000000 : ℚ))
      (U := (-(4381696579422479512909 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_6 :
    Uω (aρ 6) (bρ 6) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(4653301267676273408001 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25117111001559067 / 40000000000000000 : ℝ) ≤
      (-(4653301267676273408001 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25117111001559067 / 40000000000000000 : ℚ))
        (r' := (25117111001559067 / 20000000000000000 : ℚ))
        (U := (-(4653301267676273408001 / 10000000000000000000000 : ℚ)))
        (U' := (2278170535323726591999 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (6269505746352971 / 10000000000000000 : ℚ))
      (q := (25117111001559067 / 40000000000000000 : ℚ))
      (U := (-(4653301267676273408001 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_7 :
    Uω (aρ 7) (bρ 7) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(1258825364568131694757 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4835146341648111 / 8000000000000000 : ℝ) ≤
      (-(1258825364568131694757 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4835146341648111 / 8000000000000000 : ℚ))
        (r' := (4835146341648111 / 4000000000000000 : ℚ))
        (U := (-(1258825364568131694757 / 2500000000000000000000 : ℚ)))
        (U' := (474042586181868305243 / 2500000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (1204495496090743 / 2000000000000000 : ℚ))
      (q := (4835146341648111 / 8000000000000000 : ℚ))
      (U := (-(1258825364568131694757 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_8 :
    Uω (aρ 8) (bρ 8) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(1388735398284956359487 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22951545918932221 / 40000000000000000 : ℝ) ≤
      (-(1388735398284956359487 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (22951545918932221 / 40000000000000000 : ℚ))
        (r' := (22951545918932221 / 20000000000000000 : ℚ))
        (U := (-(1388735398284956359487 / 2500000000000000000000 : ℚ)))
        (U' := (344132552465043640513 / 2500000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (1423481559284887 / 2500000000000000 : ℚ))
      (q := (22951545918932221 / 40000000000000000 : ℚ))
      (U := (-(1388735398284956359487 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_9 :
    Uω (aρ 9) (bρ 9) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(6243053867070716944753 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21425334289664297 / 40000000000000000 : ℝ) ≤
      (-(6243053867070716944753 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21425334289664297 / 40000000000000000 : ℚ))
        (r' := (21425334289664297 / 20000000000000000 : ℚ))
        (U := (-(6243053867070716944753 / 10000000000000000000000 : ℚ)))
        (U' := (688417935929283055247 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (2635893025432793 / 5000000000000000 : ℚ))
      (q := (21425334289664297 / 40000000000000000 : ℚ))
      (U := (-(6243053867070716944753 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_10 :
    Uω (aρ 10) (bρ 10) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(7136073956947920528813 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19594953486378081 / 40000000000000000 : ℝ) ≤
      (-(7136073956947920528813 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19594953486378081 / 40000000000000000 : ℚ))
        (r' := (19594953486378081 / 10000000000000000 : ℚ))
        (U := (-(7136073956947920528813 / 10000000000000000000000 : ℚ)))
        (U' := (6726869649052079471187 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (2372577341358739 / 5000000000000000 : ℚ))
      (q := (19594953486378081 / 40000000000000000 : ℚ))
      (U := (-(7136073956947920528813 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_11 :
    Uω (aρ 11) (bρ 11) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(8281767224600949070467 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17473802007736831 / 40000000000000000 : ℝ) ≤
      (-(8281767224600949070467 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17473802007736831 / 40000000000000000 : ℚ))
        (r' := (17473802007736831 / 10000000000000000 : ℚ))
        (U := (-(8281767224600949070467 / 10000000000000000000000 : ℚ)))
        (U' := (5581176381399050929533 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (4103055569601853 / 10000000000000000 : ℚ))
      (q := (17473802007736831 / 40000000000000000 : ℚ))
      (U := (-(8281767224600949070467 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_12 :
    Uω (aρ 12) (bρ 12) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(9756141941200541419451 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3015686041375169 / 8000000000000000 : ℝ) ≤
      (-(9756141941200541419451 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3015686041375169 / 8000000000000000 : ℚ))
        (r' := (3015686041375169 / 2000000000000000 : ℚ))
        (U := (-(9756141941200541419451 / 10000000000000000000000 : ℚ)))
        (U' := (4106801664799458580549 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (83226744146409 / 250000000000000 : ℚ))
      (q := (3015686041375169 / 8000000000000000 : ℚ))
      (U := (-(9756141941200541419451 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_13 :
    Uω (aρ 13) (bρ 13) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(586403229508580354881 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2475977040951843 / 8000000000000000 : ℝ) ≤
      (-(586403229508580354881 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2475977040951843 / 8000000000000000 : ℚ))
        (r' := (2475977040951843 / 2000000000000000 : ℚ))
        (U := (-(586403229508580354881 / 500000000000000000000 : ℚ)))
        (U' := (106743950791419645119 / 500000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (475835801278609 / 2000000000000000 : ℚ))
      (q := (2475977040951843 / 8000000000000000 : ℚ))
      (U := (-(586403229508580354881 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_14 :
    Uω (aρ 14) (bρ 14) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(3000090141854125438813 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8924804140715513 / 40000000000000000 : ℝ) ≤
      (-(3000090141854125438813 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8924804140715513 / 40000000000000000 : ℚ))
        (r' := (8924804140715513 / 5000000000000000 : ℚ))
        (U := (-(3000090141854125438813 / 2000000000000000000000 : ℚ)))
        (U' := (1158792939945874561187 / 2000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (21722997014117 / 32000000000000 : ℚ))
      (s := (497782879708097 / 5000000000000000 : ℚ))
      (q := (8924804140715513 / 40000000000000000 : ℚ))
      (U := (-(3000090141854125438813 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_583_15 :
    Uω (aρ 15) (bρ 15) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_583_16 :
    Uω (aρ 16) (bρ 16) (21722997014117 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_583 :
    Uρ (21722997014117 / 32000000000000 : ℝ) ≤
      (-(3324180630720396764653 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_583_1 U_583_2 U_583_3 U_583_4 U_583_5 U_583_6 U_583_7 U_583_8 U_583_9 U_583_10
    U_583_11 U_583_12 U_583_13 U_583_14 U_583_15 U_583_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_584_1 :
    Uω (aρ 1) (bρ 1) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(3957087005357036086949 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53856221664742123 / 80000000000000000 : ℝ) ≤
      (-(3957087005357036086949 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53856221664742123 / 80000000000000000 : ℚ))
        (r' := (53856221664742123 / 40000000000000000 : ℚ))
        (U := (-(3957087005357036086949 / 10000000000000000000000 : ℚ)))
        (U' := (2974384797642963913051 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (6732003693354437 / 10000000000000000 : ℚ))
      (q := (53856221664742123 / 80000000000000000 : ℚ))
      (U := (-(3957087005357036086949 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_2 :
    Uω (aρ 2) (bρ 2) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(1996328404243077264093 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53664996438352443 / 80000000000000000 : ℝ) ≤
      (-(1996328404243077264093 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53664996438352443 / 80000000000000000 : ℚ))
        (r' := (53664996438352443 / 40000000000000000 : ℚ))
        (U := (-(1996328404243077264093 / 5000000000000000000000 : ℚ)))
        (U' := (1469407497256922735907 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (6707966399267017 / 10000000000000000 : ℚ))
      (q := (53664996438352443 / 80000000000000000 : ℚ))
      (U := (-(1996328404243077264093 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_3 :
    Uω (aρ 3) (bρ 3) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(4064158766627427001413 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53282649761223291 / 80000000000000000 : ℝ) ≤
      (-(4064158766627427001413 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53282649761223291 / 80000000000000000 : ℚ))
        (r' := (53282649761223291 / 40000000000000000 : ℚ))
        (U := (-(4064158766627427001413 / 10000000000000000000000 : ℚ)))
        (U' := (2867313036372572998587 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (6659775836334729 / 10000000000000000 : ℚ))
      (q := (53282649761223291 / 80000000000000000 : ℚ))
      (U := (-(4064158766627427001413 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_4 :
    Uω (aρ 4) (bρ 4) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(167359730165322291151 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10529590079508471 / 16000000000000000 : ℝ) ≤
      (-(167359730165322291151 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10529590079508471 / 16000000000000000 : ℚ))
        (r' := (10529590079508471 / 8000000000000000 : ℚ))
        (U := (-(167359730165322291151 / 400000000000000000000 : ℚ)))
        (U' := (109899141954677708849 / 400000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (1315879035295899 / 2000000000000000 : ℚ))
      (q := (10529590079508471 / 16000000000000000 : ℚ))
      (U := (-(167359730165322291151 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_5 :
    Uω (aρ 5) (bρ 5) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(4369123342251587632137 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (51682245064885059 / 80000000000000000 : ℝ) ≤
      (-(4369123342251587632137 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (51682245064885059 / 80000000000000000 : ℚ))
        (r' := (51682245064885059 / 40000000000000000 : ℚ))
        (U := (-(4369123342251587632137 / 10000000000000000000000 : ℚ)))
        (U' := (2562348460748412367863 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (6456158762650171 / 10000000000000000 : ℚ))
      (q := (51682245064885059 / 80000000000000000 : ℚ))
      (U := (-(4369123342251587632137 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_6 :
    Uω (aρ 6) (bρ 6) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(1160092560595083378649 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10059844403889607 / 16000000000000000 : ℝ) ≤
      (-(1160092560595083378649 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10059844403889607 / 16000000000000000 : ℚ))
        (r' := (10059844403889607 / 8000000000000000 : ℚ))
        (U := (-(1160092560595083378649 / 2500000000000000000000 : ℚ)))
        (U' := (572775390154916621351 / 2500000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (1255528675286183 / 2000000000000000 : ℚ))
      (q := (10059844403889607 / 16000000000000000 : ℚ))
      (U := (-(1160092560595083378649 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_7 :
    Uω (aρ 7) (bρ 7) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(5021840426067032372317 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48416593303044763 / 80000000000000000 : ℝ) ≤
      (-(5021840426067032372317 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48416593303044763 / 80000000000000000 : ℚ))
        (r' := (48416593303044763 / 40000000000000000 : ℚ))
        (U := (-(5021840426067032372317 / 10000000000000000000000 : ℚ)))
        (U' := (1909631376932967627683 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (6030647578090097 / 10000000000000000 : ℚ))
      (q := (48416593303044763 / 80000000000000000 : ℚ))
      (U := (-(5021840426067032372317 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_8 :
    Uω (aρ 8) (bρ 8) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(2770352236236726762283 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (45968491167470523 / 80000000000000000 : ℝ) ≤
      (-(2770352236236726762283 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (45968491167470523 / 80000000000000000 : ℚ))
        (r' := (45968491167470523 / 40000000000000000 : ℚ))
        (U := (-(2770352236236726762283 / 5000000000000000000000 : ℚ)))
        (U' := (695383665263273237717 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (5702163695536537 / 10000000000000000 : ℚ))
      (q := (45968491167470523 / 80000000000000000 : ℚ))
      (U := (-(2770352236236726762283 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_9 :
    Uω (aρ 9) (bρ 9) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(6227677789659275289543 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (42916606779601831 / 80000000000000000 : ℝ) ≤
      (-(6227677789659275289543 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (42916606779601831 / 80000000000000000 : ℚ))
        (r' := (42916606779601831 / 40000000000000000 : ℚ))
        (U := (-(6227677789659275289543 / 10000000000000000000000 : ℚ)))
        (U' := (703794013340724710457 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (1320039556732341 / 2500000000000000 : ℚ))
      (q := (42916606779601831 / 80000000000000000 : ℚ))
      (U := (-(6227677789659275289543 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_10 :
    Uω (aρ 10) (bρ 10) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(7118993375547906127047 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (39256902812473411 / 80000000000000000 : ℝ) ≤
      (-(7118993375547906127047 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (39256902812473411 / 80000000000000000 : ℚ))
        (r' := (39256902812473411 / 20000000000000000 : ℚ))
        (U := (-(7118993375547906127047 / 10000000000000000000000 : ℚ)))
        (U' := (6743950230452093872953 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (4753791268642259 / 10000000000000000 : ℚ))
      (q := (39256902812473411 / 80000000000000000 : ℚ))
      (U := (-(7118993375547906127047 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_11 :
    Uω (aρ 11) (bρ 11) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(1652403543875702179933 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (35016692004499127 / 80000000000000000 : ℝ) ≤
      (-(1652403543875702179933 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35016692004499127 / 80000000000000000 : ℚ))
        (r' := (35016692004499127 / 20000000000000000 : ℚ))
        (U := (-(1652403543875702179933 / 2000000000000000000000 : ℚ)))
        (U' := (1120185177324297820067 / 2000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (514026899106711 / 1250000000000000 : ℚ))
      (q := (35016692004499127 / 80000000000000000 : ℚ))
      (U := (-(1652403543875702179933 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_12 :
    Uω (aρ 12) (bρ 12) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(9731811107760359174813 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30230323903687811 / 80000000000000000 : ℝ) ≤
      (-(9731811107760359174813 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30230323903687811 / 80000000000000000 : ℚ))
        (r' := (30230323903687811 / 20000000000000000 : ℚ))
        (U := (-(9731811107760359174813 / 10000000000000000000000 : ℚ)))
        (U' := (4131132498239640825187 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (3339323264335859 / 10000000000000000 : ℚ))
      (q := (30230323903687811 / 80000000000000000 : ℚ))
      (U := (-(9731811107760359174813 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_13 :
    Uω (aρ 13) (bρ 13) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(11694059893297898993841 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4968821714335203 / 16000000000000000 : ℝ) ≤
      (-(11694059893297898993841 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4968821714335203 / 16000000000000000 : ℚ))
        (r' := (4968821714335203 / 4000000000000000 : ℚ))
        (U := (-(11694059893297898993841 / 10000000000000000000000 : ℚ)))
        (U' := (2168883712702101006159 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (239215117292791 / 1000000000000000 : ℚ))
      (q := (4968821714335203 / 16000000000000000 : ℚ))
      (U := (-(11694059893297898993841 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_14 :
    Uω (aρ 14) (bρ 14) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(14920090891057678189429 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3598725058625411 / 16000000000000000 : ℝ) ≤
      (-(14920090891057678189429 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3598725058625411 / 16000000000000000 : ℚ))
        (r' := (3598725058625411 / 2000000000000000 : ℚ))
        (U := (-(14920090891057678189429 / 10000000000000000000000 : ℚ)))
        (U' := (5874324517942321810571 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (43497913221863 / 64000000000000 : ℚ))
      (s := (102345763833567 / 1000000000000000 : ℚ))
      (q := (3598725058625411 / 16000000000000000 : ℚ))
      (U := (-(14920090891057678189429 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_584_15 :
    Uω (aρ 15) (bρ 15) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_584_16 :
    Uω (aρ 16) (bρ 16) (43497913221863 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_584 :
    Uρ (43497913221863 / 64000000000000 : ℝ) ≤
      (-(663068958368421010261 / 1000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_584_1 U_584_2 U_584_3 U_584_4 U_584_5 U_584_6 U_584_7 U_584_8 U_584_9 U_584_10
    U_584_11 U_584_12 U_584_13 U_584_14 U_584_15 U_584_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_585_1 :
    Uω (aρ 1) (bρ 1) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(986260950108896607393 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (674014011100133 / 1000000000000000 : ℝ) ≤
      (-(986260950108896607393 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (674014011100133 / 1000000000000000 : ℚ))
        (r' := (674014011100133 / 500000000000000 : ℚ))
        (U := (-(986260950108896607393 / 2500000000000000000000 : ℚ)))
        (U' := (746607000641103392607 / 2500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (1348023225033407 / 2000000000000000 : ℚ))
      (q := (674014011100133 / 1000000000000000 : ℚ))
      (U := (-(986260950108896607393 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_2 :
    Uω (aρ 2) (bρ 2) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(995142618591047904077 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13432474239670343 / 20000000000000000 : ℝ) ≤
      (-(995142618591047904077 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13432474239670343 / 20000000000000000 : ℚ))
        (r' := (13432474239670343 / 10000000000000000 : ℚ))
        (U := (-(995142618591047904077 / 2500000000000000000000 : ℚ)))
        (U' := (737725332158952095923 / 2500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (3358039577672359 / 5000000000000000 : ℚ))
      (q := (13432474239670343 / 20000000000000000 : ℚ))
      (U := (-(995142618591047904077 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_3 :
    Uω (aρ 3) (bρ 3) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(4051985029121106850783 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2667377707942301 / 4000000000000000 : ℝ) ≤
      (-(4051985029121106850783 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2667377707942301 / 4000000000000000 : ℚ))
        (r' := (2667377707942301 / 2000000000000000 : ℚ))
        (U := (-(4051985029121106850783 / 10000000000000000000000 : ℚ)))
        (U' := (2879486773878893149217 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (166697239043397 / 250000000000000 : ℚ))
      (q := (2667377707942301 / 4000000000000000 : ℚ))
      (U := (-(4051985029121106850783 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_4 :
    Uω (aρ 4) (bρ 4) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(1042917720939327110799 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13178216284733751 / 20000000000000000 : ℝ) ≤
      (-(1042917720939327110799 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13178216284733751 / 20000000000000000 : ℚ))
        (r' := (13178216284733751 / 10000000000000000 : ℚ))
        (U := (-(1042917720939327110799 / 2500000000000000000000 : ℚ)))
        (U' := (689950229810672889201 / 2500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (3293755743911563 / 5000000000000000 : ℚ))
      (q := (13178216284733751 / 20000000000000000 : ℚ))
      (U := (-(1042917720939327110799 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_5 :
    Uω (aρ 5) (bρ 5) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(4356565913995524418331 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3234199089937957 / 5000000000000000 : ℝ) ≤
      (-(4356565913995524418331 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3234199089937957 / 5000000000000000 : ℚ))
        (r' := (3234199089937957 / 2500000000000000 : ℚ))
        (U := (-(4356565913995524418331 / 10000000000000000000000 : ℚ)))
        (U' := (2574905889004475581669 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (6464281482176203 / 10000000000000000 : ℚ))
      (q := (3234199089937957 / 5000000000000000 : ℚ))
      (U := (-(4356565913995524418331 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_6 :
    Uω (aρ 6) (bρ 6) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(4627455968489878491293 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1259105544365247 / 2000000000000000 : ℝ) ≤
      (-(4627455968489878491293 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1259105544365247 / 2000000000000000 : ℚ))
        (r' := (1259105544365247 / 1000000000000000 : ℚ))
        (U := (-(4627455968489878491293 / 10000000000000000000000 : ℚ)))
        (U' := (2304015834510121508707 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (1257156188243369 / 2000000000000000 : ℚ))
      (q := (1259105544365247 / 2000000000000000 : ℚ))
      (U := (-(4627455968489878491293 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_7 :
    Uω (aρ 7) (bρ 7) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(500839761785607599 / 1000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12120430641761801 / 20000000000000000 : ℝ) ≤
      (-(500839761785607599 / 1000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12120430641761801 / 20000000000000000 : ℚ))
        (r' := (12120430641761801 / 10000000000000000 : ℚ))
        (U := (-(500839761785607599 / 1000000000000000000 : ℚ)))
        (U' := (192307418514392401 / 1000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (188713047502693 / 312500000000000 : ℚ))
      (q := (12120430641761801 / 20000000000000000 : ℚ))
      (U := (-(500839761785607599 / 1000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_8 :
    Uω (aρ 8) (bρ 8) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(2763243951874325661233 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11508472266131629 / 20000000000000000 : ℝ) ≤
      (-(2763243951874325661233 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11508472266131629 / 20000000000000000 : ℚ))
        (r' := (11508472266131629 / 10000000000000000 : ℚ))
        (U := (-(2763243951874325661233 / 5000000000000000000000 : ℚ)))
        (U' := (702491949625674338767 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (1427600198949001 / 2500000000000000 : ℚ))
      (q := (11508472266131629 / 20000000000000000 : ℚ))
      (U := (-(2763243951874325661233 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_9 :
    Uω (aρ 9) (bρ 9) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(6212326071951551424699 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10745635435155821 / 20000000000000000 : ℝ) ≤
      (-(6212326071951551424699 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10745635435155821 / 20000000000000000 : ℚ))
        (r' := (10745635435155821 / 10000000000000000 : ℚ))
        (U := (-(6212326071951551424699 / 10000000000000000000000 : ℚ)))
        (U' := (719145731048448575301 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (1322132398295049 / 2500000000000000 : ℚ))
      (q := (10745635435155821 / 20000000000000000 : ℚ))
      (U := (-(6212326071951551424699 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_10 :
    Uω (aρ 10) (bρ 10) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(443871487145641250981 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9830972819448893 / 20000000000000000 : ℝ) ≤
      (-(443871487145641250981 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9830972819448893 / 20000000000000000 : ℚ))
        (r' := (9830972819448893 / 5000000000000000 : ℚ))
        (U := (-(443871487145641250981 / 625000000000000000000 : ℚ)))
        (U' := (422562488229358749019 / 625000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (1190606502742067 / 2500000000000000 : ℚ))
      (q := (9830972819448893 / 20000000000000000 : ℚ))
      (U := (-(443871487145641250981 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_11 :
    Uω (aρ 11) (bρ 11) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(257572254535980578843 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4385720304765587 / 10000000000000000 : ℝ) ≤
      (-(257572254535980578843 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4385720304765587 / 10000000000000000 : ℚ))
        (r' := (4385720304765587 / 2500000000000000 : ℚ))
        (U := (-(257572254535980578843 / 312500000000000000000 : ℚ)))
        (U' := (175644733151519421157 / 312500000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (4121370427255549 / 10000000000000000 : ℚ))
      (q := (4385720304765587 / 10000000000000000 : ℚ))
      (U := (-(257572254535980578843 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_12 :
    Uω (aρ 12) (bρ 12) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(9707554825897988957459 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1515187021701689 / 4000000000000000 : ℝ) ≤
      (-(9707554825897988957459 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1515187021701689 / 4000000000000000 : ℚ))
        (r' := (1515187021701689 / 1000000000000000 : ℚ))
        (U := (-(9707554825897988957459 / 10000000000000000000000 : ℚ)))
        (U' := (4155388780102011042541 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (167478251145891 / 500000000000000 : ℚ))
      (q := (1515187021701689 / 4000000000000000 : ℚ))
      (U := (-(9707554825897988957459 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_13 :
    Uω (aρ 13) (bρ 13) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(11660238798583253649693 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6232069079655727 / 20000000000000000 : ℝ) ≤
      (-(11660238798583253649693 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6232069079655727 / 20000000000000000 : ℚ))
        (r' := (6232069079655727 / 5000000000000000 : ℚ))
        (U := (-(11660238798583253649693 / 10000000000000000000000 : ℚ)))
        (U' := (2202704807416746350307 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (1202540367830051 / 5000000000000000 : ℚ))
      (q := (6232069079655727 / 20000000000000000 : ℚ))
      (U := (-(11660238798583253649693 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_14 :
    Uω (aρ 14) (bρ 14) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(14841866121726024649593 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4533732993874791 / 20000000000000000 : ℝ) ≤
      (-(14841866121726024649593 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4533732993874791 / 20000000000000000 : ℚ))
        (r' := (4533732993874791 / 2500000000000000 : ℚ))
        (U := (-(14841866121726024649593 / 10000000000000000000000 : ℚ)))
        (U' := (5952549287273975350407 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (10887458103873 / 16000000000000 : ℚ))
      (s := (525335967462083 / 5000000000000000 : ℚ))
      (q := (4533732993874791 / 20000000000000000 : ℚ))
      (U := (-(14841866121726024649593 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_585_15 :
    Uω (aρ 15) (bρ 15) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_585_16 :
    Uω (aρ 16) (bρ 16) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_585 :
    Uρ (10887458103873 / 16000000000000 : ℝ) ≤
      (-(6613144944372741958823 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_585_1 U_585_2 U_585_3 U_585_4 U_585_5 U_585_6 U_585_7 U_585_8 U_585_9 U_585_10
    U_585_11 U_585_12 U_585_13 U_585_14 U_585_15 U_585_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_586_1 :
    Uω (aρ 1) (bρ 1) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(1966507541025517927749 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53986020110723201 / 80000000000000000 : ℝ) ≤
      (-(1966507541025517927749 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53986020110723201 / 80000000000000000 : ℚ))
        (r' := (53986020110723201 / 40000000000000000 : ℚ))
        (U := (-(1966507541025517927749 / 5000000000000000000000 : ℚ)))
        (U' := (1499228360474482072251 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (1687057139210161 / 2500000000000000 : ℚ))
      (q := (53986020110723201 / 80000000000000000 : ℚ))
      (U := (-(1966507541025517927749 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_2 :
    Uω (aρ 2) (bρ 2) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(158739949249696931061 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10758959495064521 / 16000000000000000 : ℝ) ≤
      (-(158739949249696931061 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10758959495064521 / 16000000000000000 : ℚ))
        (r' := (10758959495064521 / 8000000000000000 : ℚ))
        (U := (-(158739949249696931061 / 400000000000000000000 : ℚ)))
        (U' := (118518922870303068939 / 400000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (1344838382100099 / 2000000000000000 : ℚ))
      (q := (10758959495064521 / 16000000000000000 : ℚ))
      (U := (-(158739949249696931061 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_3 :
    Uω (aρ 3) (bρ 3) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(4039826096045358521497 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53412458543330409 / 80000000000000000 : ℝ) ≤
      (-(4039826096045358521497 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53412458543330409 / 80000000000000000 : ℚ))
        (r' := (53412458543330409 / 40000000000000000 : ℚ))
        (U := (-(4039826096045358521497 / 10000000000000000000000 : ℚ)))
        (U' := (2891645706954641478503 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (3338001641926223 / 5000000000000000 : ℚ))
      (q := (53412458543330409 / 80000000000000000 : ℚ))
      (U := (-(4039826096045358521497 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_4 :
    Uω (aρ 4) (bρ 4) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(1039840921529924137879 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (52777779841576017 / 80000000000000000 : ℝ) ≤
      (-(1039840921529924137879 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (52777779841576017 / 80000000000000000 : ℚ))
        (r' := (52777779841576017 / 40000000000000000 : ℚ))
        (U := (-(1039840921529924137879 / 2500000000000000000000 : ℚ)))
        (U' := (693027029220075862121 / 2500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (103056684210607 / 156250000000000 : ℚ))
      (q := (52777779841576017 / 80000000000000000 : ℚ))
      (U := (-(1039840921529924137879 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_5 :
    Uω (aρ 5) (bρ 5) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(4344024254899230569613 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10362425141865713 / 16000000000000000 : ℝ) ≤
      (-(4344024254899230569613 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10362425141865713 / 16000000000000000 : ℚ))
        (r' := (10362425141865713 / 8000000000000000 : ℚ))
        (U := (-(4344024254899230569613 / 10000000000000000000000 : ℚ)))
        (U' := (2587447548100769430387 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (1294480835150397 / 2000000000000000 : ℚ))
      (q := (10362425141865713 / 16000000000000000 : ℚ))
      (U := (-(4344024254899230569613 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_6 :
    Uω (aρ 6) (bρ 6) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(4614558402526447368687 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (50429221269616689 / 80000000000000000 : ℝ) ≤
      (-(4614558402526447368687 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (50429221269616689 / 80000000000000000 : ℚ))
        (r' := (50429221269616689 / 40000000000000000 : ℚ))
        (U := (-(4614558402526447368687 / 10000000000000000000000 : ℚ)))
        (U' := (2316913400473552631313 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (393369902560251 / 625000000000000 : ℚ))
      (q := (50429221269616689 / 80000000000000000 : ℚ))
      (U := (-(4614558402526447368687 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_7 :
    Uω (aρ 7) (bρ 7) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(998994596803359351861 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48546851211011821 / 80000000000000000 : ℝ) ≤
      (-(998994596803359351861 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48546851211011821 / 80000000000000000 : ℚ))
        (r' := (48546851211011821 / 40000000000000000 : ℚ))
        (U := (-(998994596803359351861 / 2000000000000000000000 : ℚ)))
        (U' := (387299763796640648139 / 2000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (6046987307072799 / 10000000000000000 : ℚ))
      (q := (48546851211011821 / 80000000000000000 : ℚ))
      (U := (-(998994596803359351861 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_8 :
    Uω (aρ 8) (bρ 8) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(2756145913413908321303 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46099285535222737 / 80000000000000000 : ℝ) ≤
      (-(2756145913413908321303 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46099285535222737 / 80000000000000000 : ℚ))
        (r' := (46099285535222737 / 40000000000000000 : ℚ))
        (U := (-(2756145913413908321303 / 5000000000000000000000 : ℚ)))
        (U' := (709589988086091678697 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (714829692433191 / 1250000000000000 : ℚ))
      (q := (46099285535222737 / 80000000000000000 : ℚ))
      (U := (-(2756145913413908321303 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_9 :
    Uω (aρ 9) (bρ 9) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(774624829318223816123 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8609694695550233 / 16000000000000000 : ℝ) ≤
      (-(774624829318223816123 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8609694695550233 / 16000000000000000 : ℚ))
        (r' := (8609694695550233 / 8000000000000000 : ℚ))
        (U := (-(774624829318223816123 / 1250000000000000000000 : ℚ)))
        (U' := (91809146056776183877 / 1250000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (1059380030691527 / 2000000000000000 : ℚ))
      (q := (8609694695550233 / 16000000000000000 : ℚ))
      (U := (-(774624829318223816123 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_10 :
    Uω (aρ 10) (bρ 10) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(3542462547203858067021 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (39390872408761549 / 80000000000000000 : ℝ) ≤
      (-(3542462547203858067021 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (39390872408761549 / 80000000000000000 : ℚ))
        (r' := (39390872408761549 / 20000000000000000 : ℚ))
        (U := (-(3542462547203858067021 / 5000000000000000000000 : ℚ)))
        (U' := (3389009255796141932979 / 5000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (4771058919705231 / 10000000000000000 : ℚ))
      (q := (39390872408761549 / 80000000000000000 : ℚ))
      (U := (-(3542462547203858067021 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_11 :
    Uω (aρ 11) (bρ 11) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(8222650286067020655741 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (35154815433084153 / 80000000000000000 : ℝ) ≤
      (-(8222650286067020655741 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35154815433084153 / 80000000000000000 : ℚ))
        (r' := (35154815433084153 / 20000000000000000 : ℚ))
        (U := (-(8222650286067020655741 / 10000000000000000000000 : ℚ)))
        (U' := (5640293319932979344259 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (2065260650995441 / 5000000000000000 : ℚ))
      (q := (35154815433084153 / 80000000000000000 : ℚ))
      (U := (-(8222650286067020655741 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_12 :
    Uω (aρ 12) (bρ 12) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(591026156976621987 / 610351562500000000 : ℝ)) := by
  have hlg :
    Real.log (30377110434234341 / 80000000000000000 : ℝ) ≤
      (-(591026156976621987 / 610351562500000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30377110434234341 / 80000000000000000 : ℚ))
        (r' := (30377110434234341 / 20000000000000000 : ℚ))
        (U := (-(591026156976621987 / 610351562500000000 : ℚ)))
        (U' := (510201544201052901 / 1220703125000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (3359795148963429 / 10000000000000000 : ℚ))
      (q := (30377110434234341 / 80000000000000000 : ℚ))
      (U := (-(591026156976621987 / 610351562500000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_13 :
    Uω (aρ 13) (bρ 13) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(11626598744486248832609 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25012276384134889 / 80000000000000000 : ℝ) ≤
      (-(11626598744486248832609 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25012276384134889 / 80000000000000000 : ℚ))
        (r' := (25012276384134889 / 20000000000000000 : ℚ))
        (U := (-(11626598744486248832609 / 10000000000000000000000 : ℚ)))
        (U' := (2236344861513751167391 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (1208984189016783 / 5000000000000000 : ℚ))
      (q := (25012276384134889 / 80000000000000000 : ℚ))
      (U := (-(11626598744486248832609 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_14 :
    Uω (aρ 14) (bρ 14) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(7382809598534463882491 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18273733742646113 / 80000000000000000 : ℝ) ≤
      (-(7382809598534463882491 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18273733742646113 / 80000000000000000 : ℚ))
        (r' := (18273733742646113 / 10000000000000000 : ℚ))
        (U := (-(7382809598534463882491 / 5000000000000000000000 : ℚ)))
        (U' := (3014398105965536117509 / 5000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (43601751609121 / 64000000000000 : ℚ))
      (s := (269315000676593 / 2500000000000000 : ℚ))
      (q := (18273733742646113 / 80000000000000000 : ℚ))
      (U := (-(7382809598534463882491 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_586_15 :
    Uω (aρ 15) (bρ 15) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_586_16 :
    Uω (aρ 16) (bρ 16) (43601751609121 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_586 :
    Uρ (43601751609121 / 64000000000000 : ℝ) ≤
      (-(329786005827769626429 / 500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_586_1 U_586_2 U_586_3 U_586_4 U_586_5 U_586_6 U_586_7 U_586_8 U_586_9 U_586_10
    U_586_11 U_586_12 U_586_13 U_586_14 U_586_15 U_586_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_587_1 :
    Uω (aρ 1) (bρ 1) (174614683211 / 256000000000 : ℝ) ≤
      (-(1960500407696928441209 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27025459666440907 / 40000000000000000 : ℝ) ≤
      (-(1960500407696928441209 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27025459666440907 / 40000000000000000 : ℚ))
        (r' := (27025459666440907 / 20000000000000000 : ℚ))
        (U := (-(1960500407696928441209 / 5000000000000000000000 : ℚ)))
        (U' := (1505235493803071558791 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (174614683211 / 256000000000 : ℚ))
      (s := (3378170494187883 / 5000000000000000 : ℚ))
      (q := (27025459666440907 / 40000000000000000 : ℚ))
      (U := (-(1960500407696928441209 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_2 :
    Uω (aρ 2) (bρ 2) (174614683211 / 256000000000 : ℝ) ≤
      (-(3956441543932251401597 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26929848994144739 / 40000000000000000 : ℝ) ≤
      (-(3956441543932251401597 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26929848994144739 / 40000000000000000 : ℚ))
        (r' := (26929848994144739 / 20000000000000000 : ℚ))
        (U := (-(3956441543932251401597 / 10000000000000000000000 : ℚ)))
        (U' := (2975030259067748598403 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (174614683211 / 256000000000 : ℚ))
      (s := (3366152332368841 / 5000000000000000 : ℚ))
      (q := (26929848994144739 / 40000000000000000 : ℚ))
      (U := (-(3956441543932251401597 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_3 :
    Uω (aρ 3) (bρ 3) (174614683211 / 256000000000 : ℝ) ≤
      (-(2013840965715370581603 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26738681457362153 / 40000000000000000 : ℝ) ≤
      (-(2013840965715370581603 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26738681457362153 / 40000000000000000 : ℚ))
        (r' := (26738681457362153 / 20000000000000000 : ℚ))
        (U := (-(2013840965715370581603 / 5000000000000000000000 : ℚ)))
        (U' := (1451894935784629418397 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (174614683211 / 256000000000 : ℚ))
      (s := (6684117002696389 / 10000000000000000 : ℚ))
      (q := (26738681457362153 / 40000000000000000 : ℚ))
      (U := (-(2013840965715370581603 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_4 :
    Uω (aρ 4) (bρ 4) (174614683211 / 256000000000 : ℝ) ≤
      (-(4147071623883270545931 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26421347252804141 / 40000000000000000 : ℝ) ≤
      (-(4147071623883270545931 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26421347252804141 / 40000000000000000 : ℚ))
        (r' := (26421347252804141 / 20000000000000000 : ℚ))
        (U := (-(4147071623883270545931 / 10000000000000000000000 : ℚ)))
        (U' := (2784400179116729454069 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (174614683211 / 256000000000 : ℚ))
      (s := (6603744081482383 / 10000000000000000 : ℚ))
      (q := (26421347252804141 / 40000000000000000 : ℚ))
      (U := (-(4147071623883270545931 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_5 :
    Uω (aρ 5) (bρ 5) (174614683211 / 256000000000 : ℝ) ≤
      (-(866299665071521699251 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25938532938119563 / 40000000000000000 : ℝ) ≤
      (-(866299665071521699251 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25938532938119563 / 40000000000000000 : ℚ))
        (r' := (25938532938119563 / 20000000000000000 : ℚ))
        (U := (-(866299665071521699251 / 2000000000000000000000 : ℚ)))
        (U' := (519994695528478300749 / 2000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (174614683211 / 256000000000 : ℚ))
      (s := (3240263421737547 / 5000000000000000 : ℚ))
      (q := (25938532938119563 / 40000000000000000 : ℚ))
      (U := (-(866299665071521699251 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_6 :
    Uω (aρ 6) (bρ 6) (174614683211 / 256000000000 : ℝ) ≤
      (-(4601677501181152033433 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25247110252738111 / 40000000000000000 : ℝ) ≤
      (-(4601677501181152033433 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25247110252738111 / 40000000000000000 : ℚ))
        (r' := (25247110252738111 / 20000000000000000 : ℚ))
        (U := (-(4601677501181152033433 / 10000000000000000000000 : ℚ)))
        (U' := (2329794301818847966567 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (174614683211 / 256000000000 : ℚ))
      (s := (393878492245273 / 625000000000000 : ℚ))
      (q := (25247110252738111 / 40000000000000000 : ℚ))
      (U := (-(4601677501181152033433 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_7 :
    Uω (aρ 7) (bρ 7) (174614683211 / 256000000000 : ℝ) ≤
      (-(1245391618782531133827 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24305989618724163 / 40000000000000000 : ℝ) ≤
      (-(1245391618782531133827 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24305989618724163 / 40000000000000000 : ℚ))
        (r' := (24305989618724163 / 20000000000000000 : ℚ))
        (U := (-(1245391618782531133827 / 2500000000000000000000 : ℚ)))
        (U' := (487476331967468866173 / 2500000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (174614683211 / 256000000000 : ℚ))
      (s := (3027578469838697 / 5000000000000000 : ℚ))
      (q := (24305989618724163 / 40000000000000000 : ℚ))
      (U := (-(1245391618782531133827 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_8 :
    Uω (aρ 8) (bρ 8) (174614683211 / 256000000000 : ℝ) ≤
      (-(2749058090920340042383 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4616468058571363 / 8000000000000000 : ℝ) ≤
      (-(2749058090920340042383 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4616468058571363 / 8000000000000000 : ℚ))
        (r' := (4616468058571363 / 4000000000000000 : ℚ))
        (U := (-(2749058090920340042383 / 5000000000000000000000 : ℚ)))
        (U' := (716677810579659957617 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (174614683211 / 256000000000 : ℚ))
      (s := (143171848202093 / 250000000000000 : ℚ))
      (q := (4616468058571363 / 8000000000000000 : ℚ))
      (U := (-(2749058090920340042383 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_9 :
    Uω (aρ 9) (bρ 9) (174614683211 / 256000000000 : ℝ) ≤
      (-(6181695398438540011231 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21557201003122639 / 40000000000000000 : ℝ) ≤
      (-(6181695398438540011231 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21557201003122639 / 40000000000000000 : ℚ))
        (r' := (21557201003122639 / 20000000000000000 : ℚ))
        (U := (-(6181695398438540011231 / 10000000000000000000000 : ℚ)))
        (U' := (749776404561459988769 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (174614683211 / 256000000000 : ℚ))
      (s := (663158738947079 / 1250000000000000 : ℚ))
      (q := (21557201003122639 / 40000000000000000 : ℚ))
      (U := (-(6181695398438540011231 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_10 :
    Uω (aρ 10) (bρ 10) (174614683211 / 256000000000 : ℝ) ≤
      (-(7067937157608990501517 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19728923122556263 / 40000000000000000 : ℝ) ≤
      (-(7067937157608990501517 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19728923122556263 / 40000000000000000 : ℚ))
        (r' := (19728923122556263 / 10000000000000000 : ℚ))
        (U := (-(7067937157608990501517 / 10000000000000000000000 : ℚ)))
        (U' := (6795006448391009498483 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (174614683211 / 256000000000 : ℚ))
      (s := (1194922501197111 / 2500000000000000 : ℚ))
      (q := (19728923122556263 / 40000000000000000 : ℚ))
      (U := (-(7067937157608990501517 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_11 :
    Uω (aρ 11) (bρ 11) (174614683211 / 256000000000 : ℝ) ≤
      (-(1640606385596563904279 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17611925552511887 / 40000000000000000 : ℝ) ≤
      (-(1640606385596563904279 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17611925552511887 / 40000000000000000 : ℚ))
        (r' := (17611925552511887 / 10000000000000000 : ℚ))
        (U := (-(1640606385596563904279 / 2000000000000000000000 : ℚ)))
        (U' := (1131982335603436095721 / 2000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (174614683211 / 256000000000 : ℚ))
      (s := (517458480746407 / 1250000000000000 : ℚ))
      (q := (17611925552511887 / 40000000000000000 : ℚ))
      (U := (-(1640606385596563904279 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_12 :
    Uω (aρ 12) (bρ 12) (174614683211 / 256000000000 : ℝ) ≤
      (-(965926376453343920951 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15225217164017443 / 40000000000000000 : ℝ) ≤
      (-(965926376453343920951 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (15225217164017443 / 40000000000000000 : ℚ))
        (r' := (15225217164017443 / 10000000000000000 : ℚ))
        (U := (-(965926376453343920951 / 1000000000000000000000 : ℚ)))
        (U' := (420367984146656079049 / 1000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (174614683211 / 256000000000 : ℚ))
      (s := (1685006874204517 / 5000000000000000 : ℚ))
      (q := (15225217164017443 / 40000000000000000 : ℚ))
      (U := (-(965926376453343920951 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_13 :
    Uω (aρ 13) (bρ 13) (174614683211 / 256000000000 : ℝ) ≤
      (-(724571076822981242243 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12548055717620997 / 40000000000000000 : ℝ) ≤
      (-(724571076822981242243 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12548055717620997 / 40000000000000000 : ℚ))
        (r' := (12548055717620997 / 10000000000000000 : ℚ))
        (U := (-(724571076822981242243 / 625000000000000000000 : ℚ)))
        (U' := (141862898552018757757 / 625000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (174614683211 / 256000000000 : ℚ))
      (s := (2430814766805811 / 10000000000000000 : ℚ))
      (q := (12548055717620997 / 40000000000000000 : ℚ))
      (U := (-(724571076822981242243 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_14 :
    Uω (aρ 14) (bρ 14) (174614683211 / 256000000000 : ℝ) ≤
      (-(7345605697896120243709 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9205105849546417 / 40000000000000000 : ℝ) ≤
      (-(7345605697896120243709 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9205105849546417 / 40000000000000000 : ℚ))
        (r' := (9205105849546417 / 5000000000000000 : ℚ))
        (U := (-(7345605697896120243709 / 5000000000000000000000 : ℚ)))
        (U' := (3051602006603879756291 / 5000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (174614683211 / 256000000000 : ℚ))
      (s := (1103267117813521 / 10000000000000000 : ℚ))
      (q := (9205105849546417 / 40000000000000000 : ℚ))
      (U := (-(7345605697896120243709 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_587_15 :
    Uω (aρ 15) (bρ 15) (174614683211 / 256000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_587_16 :
    Uω (aρ 16) (bρ 16) (174614683211 / 256000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_587 :
    Uρ (174614683211 / 256000000000 : ℝ) ≤
      (-(1644602174649657013571 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_587_1 U_587_2 U_587_3 U_587_4 U_587_5 U_587_6 U_587_7 U_587_8 U_587_9 U_587_10
    U_587_11 U_587_12 U_587_13 U_587_14 U_587_15 U_587_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_588_1 :
    Uω (aρ 1) (bρ 1) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(39090009657798394581 / 100000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54115818554488467 / 80000000000000000 : ℝ) ≤
      (-(39090009657798394581 / 100000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54115818554488467 / 80000000000000000 : ℚ))
        (r' := (54115818554488467 / 40000000000000000 : ℚ))
        (U := (-(39090009657798394581 / 100000000000000000000 : ℚ)))
        (U' := (30224708372201605419 / 100000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (3382226709886449 / 5000000000000000 : ℚ))
      (q := (54115818554488467 / 80000000000000000 : ℚ))
      (U := (-(39090009657798394581 / 100000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_2 :
    Uω (aρ 2) (bρ 2) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(394439887737222588027 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53924598497595259 / 80000000000000000 : ℝ) ≤
      (-(394439887737222588027 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53924598497595259 / 80000000000000000 : ℚ))
        (r' := (53924598497595259 / 40000000000000000 : ℚ))
        (U := (-(394439887737222588027 / 1000000000000000000000 : ℚ)))
        (U' := (298707292562777411973 / 1000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (1685104354514899 / 2500000000000000 : ℚ))
      (q := (53924598497595259 / 80000000000000000 : ℚ))
      (U := (-(394439887737222588027 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_3 :
    Uω (aρ 3) (bρ 3) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(4015552499438766461231 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53542267273075323 / 80000000000000000 : ℝ) ≤
      (-(4015552499438766461231 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53542267273075323 / 80000000000000000 : ℚ))
        (r' := (53542267273075323 / 40000000000000000 : ℚ))
        (U := (-(4015552499438766461231 / 10000000000000000000000 : ℚ)))
        (U' := (2915919303561233538769 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (1673057679569903 / 2500000000000000 : ℚ))
      (q := (53542267273075323 / 80000000000000000 : ℚ))
      (U := (-(4015552499438766461231 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_4 :
    Uω (aρ 4) (bρ 4) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(413479465984879583207 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2116304365246959 / 3200000000000000 : ℝ) ≤
      (-(413479465984879583207 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2116304365246959 / 3200000000000000 : ℚ))
        (r' := (2116304365246959 / 1600000000000000 : ℚ))
        (U := (-(413479465984879583207 / 1000000000000000000000 : ℚ)))
        (U' := (279667714315120416793 / 1000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (264474414554771 / 400000000000000 : ℚ))
      (q := (2116304365246959 / 3200000000000000 : ℚ))
      (U := (-(413479465984879583207 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_5 :
    Uω (aρ 5) (bρ 5) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(539873510739345538629 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (51942005940127359 / 80000000000000000 : ℝ) ≤
      (-(539873510739345538629 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (51942005940127359 / 80000000000000000 : ℚ))
        (r' := (51942005940127359 / 40000000000000000 : ℚ))
        (U := (-(539873510739345538629 / 1250000000000000000000 : ℚ)))
        (U' := (326560464635654461371 / 1250000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (6488649485442621 / 10000000000000000 : ℚ))
      (q := (51942005940127359 / 80000000000000000 : ℚ))
      (U := (-(539873510739345538629 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_6 :
    Uω (aρ 6) (bρ 6) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(573601652664223193247 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10111843896638211 / 16000000000000000 : ℝ) ≤
      (-(573601652664223193247 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10111843896638211 / 16000000000000000 : ℚ))
        (r' := (10111843896638211 / 8000000000000000 : ℚ))
        (U := (-(573601652664223193247 / 1250000000000000000000 : ℚ)))
        (U' := (292832322710776806753 / 1250000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (1262038649269709 / 2000000000000000 : ℚ))
      (q := (10111843896638211 / 16000000000000000 : ℚ))
      (U := (-(573601652664223193247 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_7 :
    Uω (aρ 7) (bρ 7) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(4968178041979655025511 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48677106648852863 / 80000000000000000 : ℝ) ≤
      (-(4968178041979655025511 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48677106648852863 / 80000000000000000 : ℚ))
        (r' := (48677106648852863 / 40000000000000000 : ℚ))
        (U := (-(4968178041979655025511 / 10000000000000000000000 : ℚ)))
        (U' := (1963293761020344974489 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (6063326418523997 / 10000000000000000 : ℚ))
      (q := (48677106648852863 / 80000000000000000 : ℚ))
      (U := (-(4968178041979655025511 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_8 :
    Uω (aρ 8) (bρ 8) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(2741980454591354062683 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46230074222117999 / 80000000000000000 : ℝ) ≤
      (-(2741980454591354062683 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46230074222117999 / 80000000000000000 : ℚ))
        (r' := (46230074222117999 / 40000000000000000 : ℚ))
        (U := (-(2741980454591354062683 / 5000000000000000000000 : ℚ)))
        (U' := (723755446908645937317 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (5735109963180281 / 10000000000000000 : ℚ))
      (q := (46230074222117999 / 80000000000000000 : ℚ))
      (U := (-(2741980454591354062683 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_9 :
    Uω (aρ 9) (bρ 9) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(6166416285021924208357 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43180327341267823 / 80000000000000000 : ℝ) ≤
      (-(6166416285021924208357 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43180327341267823 / 80000000000000000 : ℚ))
        (r' := (43180327341267823 / 40000000000000000 : ℚ))
        (U := (-(6166416285021924208357 / 10000000000000000000000 : ℚ)))
        (U' := (765055517978075791643 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (5313638871327737 / 10000000000000000 : ℚ))
      (q := (43180327341267823 / 80000000000000000 : ℚ))
      (U := (-(6166416285021924208357 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_10 :
    Uω (aρ 10) (bρ 10) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(7050979866472832607387 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (39524812826294763 / 80000000000000000 : ℝ) ≤
      (-(7050979866472832607387 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (39524812826294763 / 80000000000000000 : ℚ))
        (r' := (39524812826294763 / 20000000000000000 : ℚ))
        (U := (-(7050979866472832607387 / 10000000000000000000000 : ℚ)))
        (U' := (6811963739527167392613 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (299269954754967 / 625000000000000 : ℚ))
      (q := (39524812826294763 / 80000000000000000 : ℚ))
      (U := (-(7050979866472832607387 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_11 :
    Uω (aρ 11) (bρ 11) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(8183456858447127867951 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (35292869568515511 / 80000000000000000 : ℝ) ≤
      (-(8183456858447127867951 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35292869568515511 / 80000000000000000 : ℚ))
        (r' := (35292869568515511 / 20000000000000000 : ℚ))
        (U := (-(8183456858447127867951 / 10000000000000000000000 : ℚ)))
        (U' := (5679486747552872132049 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (4148810087839659 / 10000000000000000 : ℚ))
      (q := (35292869568515511 / 80000000000000000 : ℚ))
      (U := (-(8183456858447127867951 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_12 :
    Uω (aρ 12) (bρ 12) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(1204403490610925670401 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30523712533582199 / 80000000000000000 : ℝ) ≤
      (-(1204403490610925670401 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30523712533582199 / 80000000000000000 : ℚ))
        (r' := (30523712533582199 / 20000000000000000 : ℚ))
        (U := (-(1204403490610925670401 / 1250000000000000000000 : ℚ)))
        (U' := (528464460139074329599 / 1250000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (3380220925791331 / 10000000000000000 : ℚ))
      (q := (30523712533582199 / 80000000000000000 : ℚ))
      (U := (-(1204403490610925670401 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_13 :
    Uω (aρ 13) (bρ 13) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(11559851808548369618159 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25179784074442571 / 80000000000000000 : ℝ) ≤
      (-(11559851808548369618159 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25179784074442571 / 80000000000000000 : ℚ))
        (r' := (25179784074442571 / 20000000000000000 : ℚ))
        (U := (-(11559851808548369618159 / 10000000000000000000000 : ℚ)))
        (U' := (2303091797451630381841 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (152726284537589 / 625000000000000 : ℚ))
      (q := (25179784074442571 / 80000000000000000 : ℚ))
      (U := (-(11559851808548369618159 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_14 :
    Uω (aρ 14) (bρ 14) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(1461851957046835182271 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18544526476265923 / 80000000000000000 : ℝ) ≤
      (-(1461851957046835182271 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18544526476265923 / 80000000000000000 : ℚ))
        (r' := (18544526476265923 / 10000000000000000 : ℚ))
        (U := (-(1461851957046835182271 / 1000000000000000000000 : ℚ)))
        (U' := (617589583853164817729 / 1000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (43705589996379 / 64000000000000 : ℚ))
      (s := (564366719051131 / 5000000000000000 : ℚ))
      (q := (18544526476265923 / 80000000000000000 : ℚ))
      (U := (-(1461851957046835182271 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_588_15 :
    Uω (aρ 15) (bρ 15) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_588_16 :
    Uω (aρ 16) (bρ 16) (43705589996379 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_588 :
    Uρ (43705589996379 / 64000000000000 : ℝ) ≤
      (-(6561204984838086247927 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_588_1 U_588_2 U_588_3 U_588_4 U_588_5 U_588_6 U_588_7 U_588_8 U_588_9 U_588_10
    U_588_11 U_588_12 U_588_13 U_588_14 U_588_15 U_588_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_589_1 :
    Uω (aρ 1) (bρ 1) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(1948507749324743187031 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13545179443886287 / 20000000000000000 : ℝ) ≤
      (-(1948507749324743187031 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13545179443886287 / 20000000000000000 : ℚ))
        (r' := (13545179443886287 / 10000000000000000 : ℚ))
        (U := (-(1948507749324743187031 / 5000000000000000000000 : ℚ)))
        (U' := (1517228152175256812969 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (6772565851032537 / 10000000000000000 : ℚ))
      (q := (13545179443886287 / 20000000000000000 : ℚ))
      (U := (-(1948507749324743187031 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_2 :
    Uω (aρ 2) (bρ 2) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(245773168539214552107 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13497374750813287 / 20000000000000000 : ℝ) ≤
      (-(245773168539214552107 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13497374750813287 / 20000000000000000 : ℚ))
        (r' := (13497374750813287 / 10000000000000000 : ℚ))
        (U := (-(245773168539214552107 / 625000000000000000000 : ℚ)))
        (U' := (187443819148285447893 / 625000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (6748530170469537 / 10000000000000000 : ℚ))
      (q := (13497374750813287 / 20000000000000000 : ℚ))
      (U := (-(245773168539214552107 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_3 :
    Uω (aρ 3) (bρ 3) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(2001718882180630828503 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (418806028268991 / 625000000000000 : ℝ) ≤
      (-(2001718882180630828503 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (418806028268991 / 625000000000000 : ℚ))
        (r' := (418806028268991 / 312500000000000 : ℚ))
        (U := (-(2001718882180630828503 / 5000000000000000000000 : ℚ)))
        (U' := (1464017019319369171497 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (3350172215306981 / 5000000000000000 : ℚ))
      (q := (418806028268991 / 625000000000000 : ℚ))
      (U := (-(2001718882180630828503 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_4 :
    Uω (aρ 4) (bρ 4) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(824506551390814758131 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6621565464801823 / 10000000000000000 : ℝ) ≤
      (-(824506551390814758131 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6621565464801823 / 10000000000000000 : ℚ))
        (r' := (6621565464801823 / 5000000000000000 : ℚ))
        (U := (-(824506551390814758131 / 2000000000000000000000 : ℚ)))
        (U' := (561787809209185241869 / 2000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (413748539792181 / 625000000000000 : ℚ))
      (q := (6621565464801823 / 10000000000000000 : ℚ))
      (U := (-(824506551390814758131 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_5 :
    Uω (aρ 5) (bρ 5) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(4306493497263263020103 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6500868237672459 / 10000000000000000 : ℝ) ≤
      (-(4306493497263263020103 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6500868237672459 / 10000000000000000 : ℚ))
        (r' := (6500868237672459 / 5000000000000000 : ℚ))
        (U := (-(4306493497263263020103 / 10000000000000000000000 : ℚ)))
        (U' := (2624978305736736979897 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (50756032044931 / 78125000000000 : ℚ))
      (q := (6500868237672459 / 10000000000000000 : ℚ))
      (U := (-(4306493497263263020103 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_6 :
    Uω (aρ 6) (bρ 6) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(4575965519951952109527 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3164013637734911 / 5000000000000000 : ℝ) ≤
      (-(4575965519951952109527 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3164013637734911 / 5000000000000000 : ℚ))
        (r' := (3164013637734911 / 2500000000000000 : ℚ))
        (U := (-(4575965519951952109527 / 10000000000000000000000 : ℚ)))
        (U' := (2355506283048047890473 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (3159165276242947 / 5000000000000000 : ℚ))
      (q := (3164013637734911 / 5000000000000000 : ℚ))
      (U := (-(4575965519951952109527 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_7 :
    Uω (aρ 7) (bρ 7) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(1238701908887633955801 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (487422334477081 / 800000000000000 : ℝ) ≤
      (-(1238701908887633955801 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (487422334477081 / 800000000000000 : ℚ))
        (r' := (487422334477081 / 400000000000000 : ℚ))
        (U := (-(1238701908887633955801 / 2500000000000000000000 : ℚ)))
        (U' := (494166041862366044199 / 2500000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (242859829769331 / 400000000000000 : ℚ))
      (q := (487422334477081 / 800000000000000 : ℚ))
      (U := (-(1238701908887633955801 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_8 :
    Uω (aρ 8) (bρ 8) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(5469825949513502250433 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2893466653157457 / 5000000000000000 : ℝ) ≤
      (-(5469825949513502250433 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2893466653157457 / 5000000000000000 : ℚ))
        (r' := (2893466653157457 / 2500000000000000 : ℚ))
        (U := (-(5469825949513502250433 / 10000000000000000000000 : ℚ)))
        (U' := (1461645853486497749567 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (2871672823138039 / 5000000000000000 : ℚ))
      (q := (2893466653157457 / 5000000000000000 : ℚ))
      (U := (-(5469825949513502250433 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_9 :
    Uω (aρ 9) (bρ 9) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(6151161216080942852501 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1351445296808881 / 2500000000000000 : ℝ) ≤
      (-(6151161216080942852501 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1351445296808881 / 2500000000000000 : ℚ))
        (r' := (1351445296808881 / 1250000000000000 : ℚ))
        (U := (-(6151161216080942852501 / 10000000000000000000000 : ℚ)))
        (U' := (780310586919057147499 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (2661003518238649 / 5000000000000000 : ℚ))
      (q := (1351445296808881 / 2500000000000000 : ℚ))
      (U := (-(6151161216080942852501 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_10 :
    Uω (aρ 10) (bρ 10) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(7034053104242121893583 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1237242880983201 / 2500000000000000 : ℝ) ≤
      (-(7034053104242121893583 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1237242880983201 / 2500000000000000 : ℚ))
        (r' := (1237242880983201 / 625000000000000 : ℚ))
        (U := (-(7034053104242121893583 / 10000000000000000000000 : ℚ)))
        (U' := (6828890501757878106417 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (2398473371683429 / 5000000000000000 : ℚ))
      (q := (1237242880983201 / 2500000000000000 : ℚ))
      (U := (-(7034053104242121893583 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_11 :
    Uω (aρ 11) (bρ 11) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(4081962433340292229409 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1768093546853501 / 4000000000000000 : ℝ) ≤
      (-(4081962433340292229409 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1768093546853501 / 4000000000000000 : ℚ))
        (r' := (1768093546853501 / 1000000000000000 : ℚ))
        (U := (-(4081962433340292229409 / 5000000000000000000000 : ℚ)))
        (U' := (2849509369659707770591 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (831589611194751 / 2000000000000000 : ℚ))
      (q := (1768093546853501 / 4000000000000000 : ℚ))
      (U := (-(4081962433340292229409 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_12 :
    Uω (aρ 12) (bρ 12) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(1201408064539557201607 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1912309091470187 / 5000000000000000 : ℝ) ≤
      (-(1201408064539557201607 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1912309091470187 / 5000000000000000 : ℚ))
        (r' := (1912309091470187 / 1250000000000000 : ℚ))
        (U := (-(1201408064539557201607 / 1250000000000000000000 : ℚ)))
        (U' := (531459886210442798393 / 1250000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (1695208392135999 / 5000000000000000 : ℚ))
      (q := (1912309091470187 / 5000000000000000 : ℚ))
      (U := (-(1201408064539557201607 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_13 :
    Uω (aρ 13) (bρ 13) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(11526740094447365904059 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (789478026307013 / 2500000000000000 : ℝ) ≤
      (-(11526740094447365904059 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (789478026307013 / 2500000000000000 : ℚ))
        (r' := (789478026307013 / 625000000000000 : ℚ))
        (U := (-(11526740094447365904059 / 10000000000000000000000 : ℚ)))
        (U' := (2336203511552634095941 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (1228193185221177 / 5000000000000000 : ℚ))
      (q := (789478026307013 / 2500000000000000 : ℚ))
      (U := (-(11526740094447365904059 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_14 :
    Uω (aρ 14) (bρ 14) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(1818429225264942628537 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (583650666392007 / 2500000000000000 : ℝ) ≤
      (-(1818429225264942628537 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (583650666392007 / 2500000000000000 : ℚ))
        (r' := (583650666392007 / 312500000000000 : ℚ))
        (U := (-(1818429225264942628537 / 1250000000000000000000 : ℚ)))
        (U' := (780872700860057371463 / 1250000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (5469688648751 / 8000000000000 : ℚ))
      (s := (576847388083653 / 5000000000000000 : ℚ))
      (q := (583650666392007 / 2500000000000000 : ℚ))
      (U := (-(1818429225264942628537 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_589_15 :
    Uω (aρ 15) (bρ 15) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_589_16 :
    Uω (aρ 16) (bρ 16) (5469688648751 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_589 :
    Uρ (5469688648751 / 8000000000000 : ℝ) ≤
      (-(818012982659048695281 / 1250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_589_1 U_589_2 U_589_3 U_589_4 U_589_5 U_589_6 U_589_7 U_589_8 U_589_9 U_589_10
    U_589_11 U_589_12 U_589_13 U_589_14 U_589_15 U_589_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_590_1 :
    Uω (aρ 1) (bρ 1) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(1942522189783709894671 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2169824679842153 / 3200000000000000 : ℝ) ≤
      (-(1942522189783709894671 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2169824679842153 / 3200000000000000 : ℚ))
        (r' := (2169824679842153 / 1600000000000000 : ℚ))
        (U := (-(1942522189783709894671 / 5000000000000000000000 : ℚ)))
        (U' := (1523213711716290105329 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (271227131286207 / 400000000000000 : ℚ))
      (q := (2169824679842153 / 3200000000000000 : ℚ))
      (U := (-(1942522189783709894671 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_2 :
    Uω (aρ 2) (bρ 2) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(980089241722220861977 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54054399505276293 / 80000000000000000 : ℝ) ≤
      (-(980089241722220861977 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54054399505276293 / 80000000000000000 : ℚ))
        (r' := (54054399505276293 / 40000000000000000 : ℚ))
        (U := (-(980089241722220861977 / 2500000000000000000000 : ℚ)))
        (U' := (752778709027779138023 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (844580365246349 / 1250000000000000 : ℚ))
      (q := (54054399505276293 / 80000000000000000 : ℚ))
      (U := (-(980089241722220861977 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_3 :
    Uω (aρ 3) (bρ 3) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(1995668845309871194029 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2146883038033521 / 3200000000000000 : ℝ) ≤
      (-(1995668845309871194029 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2146883038033521 / 3200000000000000 : ℚ))
        (r' := (2146883038033521 / 1600000000000000 : ℚ))
        (U := (-(1995668845309871194029 / 5000000000000000000000 : ℚ)))
        (U' := (1470067056190128805971 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (268338325588449 / 400000000000000 : ℚ))
      (q := (2146883038033521 / 3200000000000000 : ℚ))
      (U := (-(1995668845309871194029 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_4 :
    Uω (aρ 4) (bρ 4) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(4110285878273273006483 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53037438267470893 / 80000000000000000 : ℝ) ≤
      (-(4110285878273273006483 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53037438267470893 / 80000000000000000 : ℚ))
        (r' := (53037438267470893 / 40000000000000000 : ℚ))
        (U := (-(4110285878273273006483 / 10000000000000000000000 : ℚ)))
        (U' := (2821185924726726993517 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (3314046449967221 / 5000000000000000 : ℚ))
      (q := (53037438267470893 / 80000000000000000 : ℚ))
      (U := (-(4110285878273273006483 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_5 :
    Uω (aρ 5) (bρ 5) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(4294014520243379947173 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (52071885760380549 / 80000000000000000 : ℝ) ≤
      (-(4294014520243379947173 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (52071885760380549 / 80000000000000000 : ℚ))
        (r' := (52071885760380549 / 40000000000000000 : ℚ))
        (U := (-(4294014520243379947173 / 10000000000000000000000 : ℚ)))
        (U' := (2637457282756620052827 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (813111836562107 / 1250000000000000 : ℚ))
      (q := (52071885760380549 / 80000000000000000 : ℚ))
      (U := (-(4294014520243379947173 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_6 :
    Uω (aρ 6) (bρ 6) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(912626870858038316583 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (50689216668171037 / 80000000000000000 : ℝ) ≤
      (-(912626870858038316583 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (50689216668171037 / 80000000000000000 : ℚ))
        (r' := (50689216668171037 / 40000000000000000 : ℚ))
        (U := (-(912626870858038316583 / 2000000000000000000000 : ℚ)))
        (U' := (473667489741961683417 / 2000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (3163233897292239 / 5000000000000000 : ℚ))
      (q := (50689216668171037 / 80000000000000000 : ℚ))
      (U := (-(912626870858038316583 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_7 :
    Uω (aρ 7) (bρ 7) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(4941455207028364076573 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48807359636483301 / 80000000000000000 : ℝ) ≤
      (-(4941455207028364076573 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48807359636483301 / 80000000000000000 : ℚ))
        (r' := (48807359636483301 / 40000000000000000 : ℚ))
        (U := (-(4941455207028364076573 / 10000000000000000000000 : ℚ)))
        (U' := (1990016595971635923427 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (379979057338909 / 625000000000000 : ℚ))
      (q := (48807359636483301 / 80000000000000000 : ℚ))
      (U := (-(4941455207028364076573 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_8 :
    Uω (aρ 8) (bρ 8) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(545571124375522783539 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46360857276965921 / 80000000000000000 : ℝ) ≤
      (-(545571124375522783539 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46360857276965921 / 80000000000000000 : ℚ))
        (r' := (46360857276965921 / 40000000000000000 : ℚ))
        (U := (-(545571124375522783539 / 1000000000000000000000 : ℚ)))
        (U' := (147576055924477216461 / 1000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (5751580978883199 / 10000000000000000 : ℚ))
      (q := (46360857276965921 / 80000000000000000 : ℚ))
      (U := (-(545571124375522783539 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_9 :
    Uω (aρ 9) (bρ 9) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(766991264223849596283 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43312168491063741 / 80000000000000000 : ℝ) ≤
      (-(766991264223849596283 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43312168491063741 / 80000000000000000 : ℚ))
        (r' := (43312168491063741 / 40000000000000000 : ℚ))
        (U := (-(766991264223849596283 / 1250000000000000000000 : ℚ)))
        (U' := (99442711151150403717 / 1250000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (2665187205383827 / 5000000000000000 : ℚ))
      (q := (43312168491063741 / 80000000000000000 : ℚ))
      (U := (-(766991264223849596283 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_10 :
    Uω (aρ 10) (bρ 10) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(3508578377429020554659 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7931744875896073 / 16000000000000000 : ℝ) ≤
      (-(3508578377429020554659 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7931744875896073 / 16000000000000000 : ℚ))
        (r' := (7931744875896073 / 4000000000000000 : ℚ))
        (U := (-(3508578377429020554659 / 5000000000000000000000 : ℚ)))
        (U' := (3422893425570979445341 / 5000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (480557241636681 / 1000000000000000 : ℚ))
      (q := (7931744875896073 / 16000000000000000 : ℚ))
      (U := (-(3508578377429020554659 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_11 :
    Uω (aρ 11) (bρ 11) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(8144435743557710104167 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (35430855323149441 / 80000000000000000 : ℝ) ≤
      (-(8144435743557710104167 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35430855323149441 / 80000000000000000 : ℚ))
        (r' := (35430855323149441 / 20000000000000000 : ℚ))
        (U := (-(8144435743557710104167 / 10000000000000000000000 : ℚ)))
        (U' := (5718507862442289895833 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (4167081778489079 / 10000000000000000 : ℚ))
      (q := (35430855323149441 / 80000000000000000 : ℚ))
      (U := (-(8144435743557710104167 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_12 :
    Uω (aρ 12) (bρ 12) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(2396843256077924959477 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6134026705020049 / 16000000000000000 : ℝ) ≤
      (-(2396843256077924959477 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6134026705020049 / 16000000000000000 : ℚ))
        (r' := (6134026705020049 / 4000000000000000 : ℚ))
        (U := (-(2396843256077924959477 / 2500000000000000000000 : ℚ)))
        (U' := (1068892645422075040523 / 2500000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (170030071283089 / 500000000000000 : ℚ))
      (q := (6134026705020049 / 16000000000000000 : ℚ))
      (U := (-(2396843256077924959477 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_13 :
    Uω (aρ 13) (bρ 13) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(5746899876398573163821 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25346652217097741 / 80000000000000000 : ℝ) ≤
      (-(5746899876398573163821 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25346652217097741 / 80000000000000000 : ℚ))
        (r' := (25346652217097741 / 20000000000000000 : ℚ))
        (U := (-(5746899876398573163821 / 5000000000000000000000 : ℚ)))
        (U' := (1184571926601426836179 / 5000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (1234556420128077 / 5000000000000000 : ℚ))
      (q := (25346652217097741 / 80000000000000000 : ℚ))
      (U := (-(5746899876398573163821 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_14 :
    Uω (aρ 14) (bρ 14) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(14477855490426510840571 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18807224630108041 / 80000000000000000 : ℝ) ≤
      (-(14477855490426510840571 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18807224630108041 / 80000000000000000 : ℚ))
        (r' := (18807224630108041 / 10000000000000000 : ℚ))
        (U := (-(14477855490426510840571 / 10000000000000000000000 : ℚ)))
        (U' := (6316559918573489159429 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (43809428383637 / 64000000000000 : ℚ))
      (s := (1178183228553729 / 10000000000000000 : ℚ))
      (q := (18807224630108041 / 80000000000000000 : ℚ))
      (U := (-(14477855490426510840571 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_590_15 :
    Uω (aρ 15) (bρ 15) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_590_16 :
    Uω (aρ 16) (bρ 16) (43809428383637 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_590 :
    Uρ (43809428383637 / 64000000000000 : ℝ) ≤
      (-(326355036030635433631 / 500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_590_1 U_590_2 U_590_3 U_590_4 U_590_5 U_590_6 U_590_7 U_590_8 U_590_9 U_590_10
    U_590_11 U_590_12 U_590_13 U_590_14 U_590_15 U_590_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_591_1 :
    Uω (aρ 1) (bρ 1) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(3873087574221783174133 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5431051621601647 / 8000000000000000 : ℝ) ≤
      (-(3873087574221783174133 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5431051621601647 / 8000000000000000 : ℚ))
        (r' := (5431051621601647 / 4000000000000000 : ℚ))
        (U := (-(3873087574221783174133 / 10000000000000000000000 : ℚ)))
        (U' := (3058384228778216825867 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (1357758142628261 / 2000000000000000 : ℚ))
      (q := (5431051621601647 / 8000000000000000 : ℚ))
      (U := (-(3873087574221783174133 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_2 :
    Uω (aρ 2) (bρ 2) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(3908357653472914841141 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27059650001838881 / 40000000000000000 : ℝ) ≤
      (-(3908357653472914841141 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27059650001838881 / 40000000000000000 : ℚ))
        (r' := (27059650001838881 / 20000000000000000 : ℚ))
        (U := (-(3908357653472914841141 / 10000000000000000000000 : ℚ)))
        (U' := (3023114149527085158859 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (1691188918141657 / 2500000000000000 : ℚ))
      (q := (27059650001838881 / 40000000000000000 : ℚ))
      (U := (-(3908357653472914841141 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_3 :
    Uω (aρ 3) (bρ 3) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(497406530345597454679 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26868490135171893 / 40000000000000000 : ℝ) ≤
      (-(497406530345597454679 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26868490135171893 / 40000000000000000 : ℚ))
        (r' := (26868490135171893 / 20000000000000000 : ℚ))
        (U := (-(497406530345597454679 / 1250000000000000000000 : ℚ)))
        (U' := (369027445029402545321 / 1250000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (3358285922791567 / 5000000000000000 : ℚ))
      (q := (26868490135171893 / 40000000000000000 : ℚ))
      (U := (-(497406530345597454679 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_4 :
    Uω (aρ 4) (bρ 4) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(512256748377032037619 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5310235277848301 / 8000000000000000 : ℝ) ≤
      (-(512256748377032037619 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5310235277848301 / 8000000000000000 : ℚ))
        (r' := (5310235277848301 / 4000000000000000 : ℚ))
        (U := (-(512256748377032037619 / 1250000000000000000000 : ℚ)))
        (U' := (354177226997967962381 / 1250000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (331810457684147 / 500000000000000 : ℚ))
      (q := (5310235277848301 / 8000000000000000 : ℚ))
      (U := (-(512256748377032037619 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_5 :
    Uω (aρ 5) (bρ 5) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(2140775557921181468381 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1042736510350251 / 1600000000000000 : ℝ) ≤
      (-(2140775557921181468381 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1042736510350251 / 1600000000000000 : ℚ))
        (r' := (1042736510350251 / 800000000000000 : ℚ))
        (U := (-(2140775557921181468381 / 5000000000000000000000 : ℚ)))
        (U' := (1324960343578818531619 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (260520690311013 / 400000000000000 : ℚ))
      (q := (1042736510350251 / 1600000000000000 : ℚ))
      (U := (-(2140775557921181468381 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_6 :
    Uω (aρ 6) (bρ 6) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(4550319681689112793929 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5075421487741559 / 8000000000000000 : ℝ) ≤
      (-(4550319681689112793929 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5075421487741559 / 8000000000000000 : ℚ))
        (r' := (5075421487741559 / 4000000000000000 : ℚ))
        (U := (-(4550319681689112793929 / 10000000000000000000000 : ℚ)))
        (U' := (2381152121310887206071 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (1266920994578217 / 2000000000000000 : ℚ))
      (q := (5075421487741559 / 8000000000000000 : ℚ))
      (U := (-(4550319681689112793929 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_7 :
    Uω (aρ 7) (bρ 7) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(4928120707798083417323 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24436242608817219 / 40000000000000000 : ℝ) ≤
      (-(4928120707798083417323 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24436242608817219 / 40000000000000000 : ℚ))
        (r' := (24436242608817219 / 20000000000000000 : ℚ))
        (U := (-(4928120707798083417323 / 10000000000000000000000 : ℚ)))
        (U' := (2003351095201916582677 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (6087833938705797 / 10000000000000000 : ℚ))
      (q := (24436242608817219 / 40000000000000000 : ℚ))
      (U := (-(4928120707798083417323 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_8 :
    Uω (aρ 8) (bρ 8) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(272080836654552202981 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4642624670747133 / 8000000000000000 : ℝ) ≤
      (-(272080836654552202981 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4642624670747133 / 8000000000000000 : ℚ))
        (r' := (4642624670747133 / 4000000000000000 : ℚ))
        (U := (-(272080836654552202981 / 500000000000000000000 : ℚ)))
        (U' := (74492753495447797019 / 500000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (287990798125251 / 500000000000000 : ℚ))
      (q := (4642624670747133 / 8000000000000000 : ℚ))
      (U := (-(272080836654552202981 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_9 :
    Uω (aρ 9) (bρ 9) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(6120722900714232247101 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21689042167840287 / 40000000000000000 : ℝ) ≤
      (-(6120722900714232247101 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21689042167840287 / 40000000000000000 : ℚ))
        (r' := (21689042167840287 / 20000000000000000 : ℚ))
        (U := (-(6120722900714232247101 / 10000000000000000000000 : ℚ)))
        (U' := (810748902285767752899 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (5338740997917331 / 10000000000000000 : ℚ))
      (q := (21689042167840287 / 40000000000000000 : ℚ))
      (U := (-(6120722900714232247101 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_10 :
    Uω (aρ 10) (bρ 10) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(7000290702954301500691 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3972566942892681 / 8000000000000000 : ℝ) ≤
      (-(7000290702954301500691 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3972566942892681 / 8000000000000000 : ℚ))
        (r' := (3972566942892681 / 2000000000000000 : ℚ))
        (U := (-(7000290702954301500691 / 10000000000000000000000 : ℚ)))
        (U' := (6862652903045698499309 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (481419630472389 / 1000000000000000 : ℚ))
      (q := (3972566942892681 / 8000000000000000 : ℚ))
      (U := (-(7000290702954301500691 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_11 :
    Uω (aρ 11) (bρ 11) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(2031247320397186581489 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17749911419090027 / 40000000000000000 : ℝ) ≤
      (-(2031247320397186581489 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17749911419090027 / 40000000000000000 : ℚ))
        (r' := (17749911419090027 / 10000000000000000 : ℚ))
        (U := (-(2031247320397186581489 / 2500000000000000000000 : ℚ)))
        (U' := (1434488581102813418511 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (4176211283242201 / 10000000000000000 : ℚ))
      (q := (17749911419090027 / 40000000000000000 : ℚ))
      (U := (-(2031247320397186581489 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_12 :
    Uω (aρ 12) (bρ 12) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(9563552940403943445557 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15371638560123711 / 40000000000000000 : ℝ) ≤
      (-(9563552940403943445557 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (15371638560123711 / 40000000000000000 : ℚ))
        (r' := (15371638560123711 / 10000000000000000 : ℚ))
        (U := (-(9563552940403943445557 / 10000000000000000000000 : ℚ)))
        (U' := (4299390665596056554443 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (3410774950444043 / 10000000000000000 : ℚ))
      (q := (15371638560123711 / 40000000000000000 : ℚ))
      (U := (-(9563552940403943445557 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_13 :
    Uω (aρ 13) (bρ 13) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(2865257125482834296423 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12714926310772163 / 40000000000000000 : ℝ) ≤
      (-(2865257125482834296423 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12714926310772163 / 40000000000000000 : ℚ))
        (r' := (12714926310772163 / 10000000000000000 : ℚ))
        (U := (-(2865257125482834296423 / 2500000000000000000000 : ℚ)))
        (U' := (600478776017165703577 / 2500000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (2481800567363269 / 10000000000000000 : ℚ))
      (q := (12714926310772163 / 40000000000000000 : ℚ))
      (U := (-(2865257125482834296423 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_14 :
    Uω (aρ 14) (bρ 14) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(225151496633754432083 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9467925991076191 / 40000000000000000 : ℝ) ≤
      (-(225151496633754432083 / 156250000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9467925991076191 / 40000000000000000 : ℚ))
        (r' := (9467925991076191 / 5000000000000000 : ℚ))
        (U := (-(225151496633754432083 / 156250000000000000000 : ℚ)))
        (U' := (99761244131870567917 / 156250000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (21930673788633 / 32000000000000 : ℚ))
      (s := (1202227692560283 / 10000000000000000 : ℚ))
      (q := (9467925991076191 / 40000000000000000 : ℚ))
      (U := (-(225151496633754432083 / 156250000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_591_15 :
    Uω (aρ 15) (bρ 15) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_591_16 :
    Uω (aρ 16) (bρ 16) (21930673788633 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_591 :
    Uρ (21930673788633 / 32000000000000 : ℝ) ≤
      (-(1302038278493546697749 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_591_1 U_591_2 U_591_3 U_591_4 U_591_5 U_591_6 U_591_7 U_591_8 U_591_9 U_591_10
    U_591_11 U_591_12 U_591_13 U_591_14 U_591_15 U_591_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
