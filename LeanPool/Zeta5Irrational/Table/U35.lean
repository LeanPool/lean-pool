/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U35) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_424_1 :
    Uω (aρ 1) (bρ 1) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(8069783430186067276137 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8924086147760843 / 20000000000000000 : ℝ) ≤
      (-(8069783430186067276137 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8924086147760843 / 20000000000000000 : ℚ))
        (r' := (8924086147760843 / 5000000000000000 : ℚ))
        (U := (-(8069783430186067276137 / 10000000000000000000000 : ℚ)))
        (U' := (5793160175813932723863 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1810630609509 / 4000000000000 : ℚ))
      (s := (4462006842073343 / 10000000000000000 : ℚ))
      (q := (8924086147760843 / 20000000000000000 : ℚ))
      (U := (-(8069783430186067276137 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_424_2 :
    Uω (aρ 2) (bρ 2) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(1624730430815369043297 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8876142483631273 / 20000000000000000 : ℝ) ≤
      (-(1624730430815369043297 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8876142483631273 / 20000000000000000 : ℚ))
        (r' := (8876142483631273 / 5000000000000000 : ℚ))
        (U := (-(1624730430815369043297 / 2000000000000000000000 : ℚ)))
        (U' := (1147858290384630956703 / 2000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1810630609509 / 4000000000000 : ℚ))
      (s := (4437832190453773 / 10000000000000000 : ℚ))
      (q := (8876142483631273 / 20000000000000000 : ℚ))
      (U := (-(1624730430815369043297 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_424_3 :
    Uω (aρ 3) (bρ 3) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(4116197784770404230469 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4390071594604641 / 10000000000000000 : ℝ) ≤
      (-(4116197784770404230469 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4390071594604641 / 10000000000000000 : ℚ))
        (r' := (4390071594604641 / 2500000000000000 : ℚ))
        (U := (-(4116197784770404230469 / 5000000000000000000000 : ℚ)))
        (U' := (2815274018229595769531 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1810630609509 / 4000000000000 : ℚ))
      (s := (2194614501190891 / 5000000000000000 : ℚ))
      (q := (4390071594604641 / 10000000000000000 : ℚ))
      (U := (-(4116197784770404230469 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_424_4 :
    Uω (aρ 4) (bρ 4) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(8416056233038239239309 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8620358298217587 / 20000000000000000 : ℝ) ≤
      (-(8416056233038239239309 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8620358298217587 / 20000000000000000 : ℚ))
        (r' := (8620358298217587 / 5000000000000000 : ℚ))
        (U := (-(8416056233038239239309 / 10000000000000000000000 : ℚ)))
        (U' := (5446887372961760760691 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1810630609509 / 4000000000000 : ℚ))
      (s := (4307738292455087 / 10000000000000000 : ℚ))
      (q := (8620358298217587 / 20000000000000000 : ℚ))
      (U := (-(8416056233038239239309 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_424_5 :
    Uω (aρ 5) (bρ 5) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(8703446256895322532487 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (837614384878577 / 2000000000000000 : ℝ) ≤
      (-(8703446256895322532487 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (837614384878577 / 2000000000000000 : ℚ))
        (r' := (837614384878577 / 500000000000000 : ℚ))
        (U := (-(8703446256895322532487 / 10000000000000000000000 : ℚ)))
        (U' := (5159497349104677467513 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1810630609509 / 4000000000000 : ℚ))
      (s := (418171376235827 / 1000000000000000 : ℚ))
      (q := (837614384878577 / 2000000000000000 : ℚ))
      (U := (-(8703446256895322532487 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_424_6 :
    Uω (aρ 6) (bρ 6) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(2283303540356153156021 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8023789823958269 / 20000000000000000 : ℝ) ≤
      (-(2283303540356153156021 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8023789823958269 / 20000000000000000 : ℚ))
        (r' := (8023789823958269 / 5000000000000000 : ℚ))
        (U := (-(2283303540356153156021 / 2500000000000000000000 : ℚ)))
        (U' := (1182432361143846843979 / 2500000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1810630609509 / 4000000000000 : ℚ))
      (s := (3996600112670769 / 10000000000000000 : ℚ))
      (q := (8023789823958269 / 20000000000000000 : ℚ))
      (U := (-(2283303540356153156021 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_424_7 :
    Uω (aρ 7) (bρ 7) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(2439356390886610766343 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (188456185376221 / 500000000000000 : ℝ) ≤
      (-(2439356390886610766343 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (188456185376221 / 500000000000000 : ℚ))
        (r' := (188456185376221 / 125000000000000 : ℚ))
        (U := (-(2439356390886610766343 / 2500000000000000000000 : ℚ)))
        (U' := (1026379510613389233657 / 2500000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (1810630609509 / 4000000000000 : ℚ))
      (s := (186735954226067 / 500000000000000 : ℚ))
      (q := (188456185376221 / 500000000000000 : ℚ))
      (U := (-(2439356390886610766343 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_424_8 :
    Uω (aρ 8) (bρ 8) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(10651370252152340611 / 10000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (344680621415669 / 1000000000000000 : ℝ) ≤
      (-(10651370252152340611 / 10000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (344680621415669 / 1000000000000000 : ℚ))
        (r' := (344680621415669 / 250000000000000 : ℚ))
        (U := (-(10651370252152340611 / 10000000000000000000 : ℚ)))
        (U' := (3211573353847659389 / 10000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (1810630609509 / 4000000000000 : ℚ))
      (s := (84340643728147 / 250000000000000 : ℚ))
      (q := (344680621415669 / 1000000000000000 : ℚ))
      (U := (-(10651370252152340611 / 10000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_424_9 :
    Uω (aρ 9) (bρ 9) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(1194174976479651820651 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6059075899093861 / 20000000000000000 : ℝ) ≤
      (-(1194174976479651820651 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6059075899093861 / 20000000000000000 : ℚ))
        (r' := (6059075899093861 / 5000000000000000 : ℚ))
        (U := (-(1194174976479651820651 / 1000000000000000000000 : ℚ)))
        (U' := (192119384120348179349 / 1000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (1810630609509 / 4000000000000 : ℚ))
      (s := (2880054848266361 / 10000000000000000 : ℚ))
      (q := (6059075899093861 / 20000000000000000 : ℚ))
      (U := (-(1194174976479651820651 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_424_10 :
    Uω (aρ 10) (bρ 10) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(13910766432101367482929 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2488072835094411 / 10000000000000000 : ℝ) ≤
      (-(13910766432101367482929 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2488072835094411 / 10000000000000000 : ℚ))
        (r' := (2488072835094411 / 1250000000000000 : ℚ))
        (U := (-(13910766432101367482929 / 10000000000000000000000 : ℚ)))
        (U' := (6883648976898632517071 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (1810630609509 / 4000000000000 : ℚ))
      (s := (1092841826428161 / 5000000000000000 : ℚ))
      (q := (2488072835094411 / 10000000000000000 : ℚ))
      (U := (-(13910766432101367482929 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_424_11 :
    Uω (aρ 11) (bρ 11) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(8909444894819806137933 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3366397878121701 / 20000000000000000 : ℝ) ≤
      (-(8909444894819806137933 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3366397878121701 / 20000000000000000 : ℚ))
        (r' := (3366397878121701 / 2500000000000000 : ℚ))
        (U := (-(8909444894819806137933 / 5000000000000000000000 : ℚ)))
        (U' := (1487762809680193862067 / 5000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (1810630609509 / 4000000000000 : ℚ))
      (s := (994412486994201 / 10000000000000000 : ℚ))
      (q := (3366397878121701 / 20000000000000000 : ℚ))
      (U := (-(8909444894819806137933 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_424_12 :
    Uω (aρ 12) (bρ 12) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_424_13 :
    Uω (aρ 13) (bρ 13) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_424_14 :
    Uω (aρ 14) (bρ 14) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_424_15 :
    Uω (aρ 15) (bρ 15) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_424_16 :
    Uω (aρ 16) (bρ 16) (1810630609509 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_424 :
    Uρ (1810630609509 / 4000000000000 : ℝ) ≤
      (-(11891711587405053258781 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_424_1 U_424_2 U_424_3 U_424_4 U_424_5 U_424_6 U_424_7 U_424_8 U_424_9 U_424_10
    U_424_11 U_424_12 U_424_13 U_424_14 U_424_15 U_424_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_425_1 :
    Uω (aρ 1) (bρ 1) (906639604631 / 2000000000000 : ℝ) ≤
      (-(4027477348275718747337 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (357493170156023 / 800000000000000 : ℝ) ≤
      (-(4027477348275718747337 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (357493170156023 / 800000000000000 : ℚ))
        (r' := (357493170156023 / 200000000000000 : ℚ))
        (U := (-(4027477348275718747337 / 5000000000000000000000 : ℚ)))
        (U' := (2903994454724281252663 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (906639604631 / 2000000000000 : ℚ))
      (s := (178745137953223 / 400000000000000 : ℚ))
      (q := (357493170156023 / 800000000000000 : ℚ))
      (U := (-(4027477348275718747337 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_425_2 :
    Uω (aρ 2) (bρ 2) (906639604631 / 2000000000000 : ℝ) ≤
      (-(4054371351793893970459 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1777877238938007 / 4000000000000000 : ℝ) ≤
      (-(4054371351793893970459 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1777877238938007 / 4000000000000000 : ℚ))
        (r' := (1777877238938007 / 1000000000000000 : ℚ))
        (U := (-(4054371351793893970459 / 5000000000000000000000 : ℚ)))
        (U' := (2877100451206106029541 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (906639604631 / 2000000000000 : ℚ))
      (s := (888890880426007 / 2000000000000000 : ℚ))
      (q := (1777877238938007 / 4000000000000000 : ℚ))
      (U := (-(4054371351793893970459 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_425_3 :
    Uω (aρ 3) (bρ 3) (906639604631 / 2000000000000 : ℝ) ≤
      (-(8217321149963825466591 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8793388726378293 / 20000000000000000 : ℝ) ≤
      (-(8217321149963825466591 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8793388726378293 / 20000000000000000 : ℚ))
        (r' := (8793388726378293 / 5000000000000000 : ℚ))
        (U := (-(8217321149963825466591 / 10000000000000000000000 : ℚ)))
        (U' := (5645622456036174533409 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (906639604631 / 2000000000000 : ℚ))
      (s := (4395853040168293 / 10000000000000000 : ℚ))
      (q := (8793388726378293 / 20000000000000000 : ℚ))
      (U := (-(8217321149963825466591 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_425_4 :
    Uω (aρ 4) (bρ 4) (906639604631 / 2000000000000 : ℝ) ≤
      (-(4200348437088783331463 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4316804394612983 / 10000000000000000 : ℝ) ≤
      (-(4200348437088783331463 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4316804394612983 / 10000000000000000 : ℚ))
        (r' := (4316804394612983 / 2500000000000000 : ℚ))
        (U := (-(4200348437088783331463 / 5000000000000000000000 : ℚ)))
        (U' := (2731123365911216668537 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (906639604631 / 2000000000000 : ℚ))
      (s := (2157183642040483 / 5000000000000000 : ℚ))
      (q := (4316804394612983 / 10000000000000000 : ℚ))
      (U := (-(4200348437088783331463 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_425_5 :
    Uω (aρ 5) (bρ 5) (906639604631 / 2000000000000 : ℝ) ≤
      (-(8687624402469212596989 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8389406951225531 / 20000000000000000 : ℝ) ≤
      (-(8687624402469212596989 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8389406951225531 / 20000000000000000 : ℚ))
        (r' := (8389406951225531 / 5000000000000000 : ℚ))
        (U := (-(8687624402469212596989 / 10000000000000000000000 : ℚ)))
        (U' := (5175319203530787403011 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (906639604631 / 2000000000000 : ℚ))
      (s := (4188355365415531 / 10000000000000000 : ℚ))
      (q := (8389406951225531 / 20000000000000000 : ℚ))
      (U := (-(8687624402469212596989 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_425_6 :
    Uω (aρ 6) (bρ 6) (906639604631 / 2000000000000 : ℝ) ≤
      (-(1139582518123484126347 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8037083418905043 / 20000000000000000 : ℝ) ≤
      (-(1139582518123484126347 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8037083418905043 / 20000000000000000 : ℚ))
        (r' := (8037083418905043 / 5000000000000000 : ℚ))
        (U := (-(1139582518123484126347 / 1250000000000000000000 : ℚ)))
        (U' := (593285432626515873653 / 1250000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (906639604631 / 2000000000000 : ℚ))
      (s := (4003272208235043 / 10000000000000000 : ℚ))
      (q := (8037083418905043 / 20000000000000000 : ℚ))
      (U := (-(1139582518123484126347 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_425_7 :
    Uω (aρ 7) (bρ 7) (906639604631 / 2000000000000 : ℝ) ≤
      (-(1947942394458633086619 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3775806095905767 / 10000000000000000 : ℝ) ≤
      (-(1947942394458633086619 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3775806095905767 / 10000000000000000 : ℚ))
        (r' := (3775806095905767 / 2500000000000000 : ℚ))
        (U := (-(1947942394458633086619 / 2000000000000000000000 : ℚ)))
        (U' := (824646326741366913381 / 2000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (906639604631 / 2000000000000 : ℚ))
      (s := (1870731180950767 / 5000000000000000 : ℚ))
      (q := (3775806095905767 / 10000000000000000 : ℚ))
      (U := (-(1947942394458633086619 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_425_8 :
    Uω (aρ 8) (bρ 8) (906639604631 / 2000000000000 : ℝ) ≤
      (-(10631763071366856419741 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6907142118447623 / 20000000000000000 : ℝ) ≤
      (-(10631763071366856419741 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6907142118447623 / 20000000000000000 : ℚ))
        (r' := (6907142118447623 / 5000000000000000 : ℚ))
        (U := (-(10631763071366856419741 / 10000000000000000000000 : ℚ)))
        (U' := (3231180534633143580259 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (906639604631 / 2000000000000 : ℚ))
      (s := (3380533939877623 / 10000000000000000 : ℚ))
      (q := (6907142118447623 / 20000000000000000 : ℚ))
      (U := (-(10631763071366856419741 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_425_9 :
    Uω (aρ 9) (bρ 9) (906639604631 / 2000000000000 : ℝ) ≤
      (-(11918788004198888387561 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23722674177189 / 78125000000000 : ℝ) ≤
      (-(11918788004198888387561 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23722674177189 / 78125000000000 : ℚ))
        (r' := (23722674177189 / 19531250000000 : ℚ))
        (U := (-(11918788004198888387561 / 10000000000000000000000 : ℚ)))
        (U' := (1944155601801111612439 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (906639604631 / 2000000000000 : ℚ))
      (s := (180460127446899 / 625000000000000 : ℚ))
      (q := (23722674177189 / 78125000000000 : ℚ))
      (U := (-(11918788004198888387561 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_425_10 :
    Uω (aρ 10) (bρ 10) (906639604631 / 2000000000000 : ℝ) ≤
      (-(3470132493185344546727 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2495607271404321 / 10000000000000000 : ℝ) ≤
      (-(3470132493185344546727 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2495607271404321 / 10000000000000000 : ℚ))
        (r' := (2495607271404321 / 1250000000000000 : ℚ))
        (U := (-(3470132493185344546727 / 2500000000000000000000 : ℚ)))
        (U' := (1728471359064655453273 / 2500000000000000000000 : ℚ))
        3 15 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (906639604631 / 2000000000000 : ℚ))
      (s := (1097065513046821 / 5000000000000000 : ℚ))
      (q := (2495607271404321 / 10000000000000000 : ℚ))
      (U := (-(3470132493185344546727 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_425_11 :
    Uω (aρ 11) (bρ 11) (906639604631 / 2000000000000 : ℝ) ≤
      (-(221910297290179888531 / 125000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3388711953436309 / 20000000000000000 : ℝ) ≤
      (-(221910297290179888531 / 125000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3388711953436309 / 20000000000000000 : ℚ))
        (r' := (3388711953436309 / 2500000000000000 : ℚ))
        (U := (-(221910297290179888531 / 125000000000000000000 : ℚ)))
        (U' := (38019895322320111469 / 125000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (906639604631 / 2000000000000 : ℚ))
      (s := (1010105062926309 / 10000000000000000 : ℚ))
      (q := (3388711953436309 / 20000000000000000 : ℚ))
      (U := (-(221910297290179888531 / 125000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_425_12 :
    Uω (aρ 12) (bρ 12) (906639604631 / 2000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_425_13 :
    Uω (aρ 13) (bρ 13) (906639604631 / 2000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_425_14 :
    Uω (aρ 14) (bρ 14) (906639604631 / 2000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_425_15 :
    Uω (aρ 15) (bρ 15) (906639604631 / 2000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_425_16 :
    Uω (aρ 16) (bρ 16) (906639604631 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_425 :
    Uρ (906639604631 / 2000000000000 : ℝ) ≤
      (-(11874116246818642659339 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_425_1 U_425_2 U_425_3 U_425_4 U_425_5 U_425_6 U_425_7 U_425_8 U_425_9 U_425_10
    U_425_11 U_425_12 U_425_13 U_425_14 U_425_15 U_425_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_426_1 :
    Uω (aρ 1) (bρ 1) (363185561803 / 800000000000 : ℝ) ≤
      (-(1608029583970223099703 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1790114471944513 / 4000000000000000 : ℝ) ≤
      (-(1608029583970223099703 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1790114471944513 / 4000000000000000 : ℚ))
        (r' := (1790114471944513 / 1000000000000000 : ℚ))
        (U := (-(1608029583970223099703 / 2000000000000000000000 : ℚ)))
        (U' := (1164559137229776900297 / 2000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (363185561803 / 800000000000 : ℚ))
      (s := (895050011054013 / 2000000000000000 : ℚ))
      (q := (1790114471944513 / 4000000000000000 : ℚ))
      (U := (-(1608029583970223099703 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_426_2 :
    Uω (aρ 2) (bρ 2) (363185561803 / 800000000000 : ℝ) ≤
      (-(252932982861302534687 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8902629903629441 / 20000000000000000 : ℝ) ≤
      (-(252932982861302534687 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8902629903629441 / 20000000000000000 : ℚ))
        (r' := (8902629903629441 / 5000000000000000 : ℚ))
        (U := (-(252932982861302534687 / 312500000000000000000 : ℚ)))
        (U' := (180284004826197465313 / 312500000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (363185561803 / 800000000000 : ℚ))
      (s := (4451076611686941 / 10000000000000000 : ℚ))
      (q := (8902629903629441 / 20000000000000000 : ℚ))
      (U := (-(252932982861302534687 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_426_3 :
    Uω (aρ 3) (bρ 3) (363185561803 / 800000000000 : ℝ) ≤
      (-(4101134714336247887123 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (220165856397753 / 500000000000000 : ℝ) ≤
      (-(4101134714336247887123 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (220165856397753 / 500000000000000 : ℚ))
        (r' := (220165856397753 / 125000000000000 : ℚ))
        (U := (-(4101134714336247887123 / 5000000000000000000000 : ℚ)))
        (U' := (2830337088663752112877 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (363185561803 / 800000000000 : ℚ))
      (s := (220123853515881 / 500000000000000 : ℚ))
      (q := (220165856397753 / 500000000000000 : ℚ))
      (U := (-(4101134714336247887123 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_426_4 :
    Uω (aρ 4) (bρ 4) (363185561803 / 800000000000 : ℝ) ≤
      (-(8385361096703903811737 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (864685925725911 / 2000000000000000 : ℝ) ≤
      (-(8385361096703903811737 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (864685925725911 / 2000000000000000 : ℚ))
        (r' := (864685925725911 / 500000000000000 : ℚ))
        (U := (-(8385361096703903811737 / 10000000000000000000000 : ℚ)))
        (U' := (5477582509296096188263 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (363185561803 / 800000000000 : ℚ))
      (s := (432099625273161 / 1000000000000000 : ℚ))
      (q := (864685925725911 / 2000000000000000 : ℚ))
      (U := (-(8385361096703903811737 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_426_5 :
    Uω (aρ 5) (bρ 5) (363185561803 / 800000000000 : ℝ) ≤
      (-(541989226078443513091 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1680533998020911 / 4000000000000000 : ℝ) ≤
      (-(541989226078443513091 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1680533998020911 / 4000000000000000 : ℚ))
        (r' := (1680533998020911 / 1000000000000000 : ℚ))
        (U := (-(541989226078443513091 / 625000000000000000000 : ℚ)))
        (U' := (324444749296556486909 / 625000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (363185561803 / 800000000000 : ℚ))
      (s := (838999380982411 / 2000000000000000 : ℚ))
      (q := (1680533998020911 / 4000000000000000 : ℚ))
      (U := (-(541989226078443513091 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_426_6 :
    Uω (aρ 6) (bρ 6) (363185561803 / 800000000000 : ℝ) ≤
      (-(2275033423792574258343 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8050376846117527 / 20000000000000000 : ℝ) ≤
      (-(2275033423792574258343 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8050376846117527 / 20000000000000000 : ℚ))
        (r' := (8050376846117527 / 5000000000000000 : ℚ))
        (U := (-(2275033423792574258343 / 2500000000000000000000 : ℚ)))
        (U' := (1190702477707425741657 / 2500000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (363185561803 / 800000000000 : ℚ))
      (s := (4009944136065027 / 10000000000000000 : ℚ))
      (q := (8050376846117527 / 20000000000000000 : ℚ))
      (U := (-(2275033423792574258343 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_426_7 :
    Uω (aρ 7) (bρ 7) (363185561803 / 800000000000 : ℝ) ≤
      (-(1215253784585170195443 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3782488267178449 / 10000000000000000 : ℝ) ≤
      (-(1215253784585170195443 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3782488267178449 / 10000000000000000 : ℚ))
        (r' := (3782488267178449 / 2500000000000000 : ℚ))
        (U := (-(1215253784585170195443 / 1250000000000000000000 : ℚ)))
        (U' := (517614166164829804557 / 1250000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (363185561803 / 800000000000 : ℚ))
      (s := (1874102602532199 / 5000000000000000 : ℚ))
      (q := (3782488267178449 / 10000000000000000 : ℚ))
      (U := (-(1215253784585170195443 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_426_8 :
    Uω (aρ 8) (bρ 8) (363185561803 / 800000000000 : ℝ) ≤
      (-(2122439182815299947461 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6920670663515501 / 20000000000000000 : ℝ) ≤
      (-(2122439182815299947461 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6920670663515501 / 20000000000000000 : ℚ))
        (r' := (6920670663515501 / 5000000000000000 : ℚ))
        (U := (-(2122439182815299947461 / 2000000000000000000000 : ℚ)))
        (U' := (650149538384700052539 / 2000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (363185561803 / 800000000000 : ℚ))
      (s := (3387440985563001 / 10000000000000000 : ℚ))
      (q := (6920670663515501 / 20000000000000000 : ℚ))
      (U := (-(2122439182815299947461 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_426_9 :
    Uω (aρ 9) (bρ 9) (363185561803 / 800000000000 : ℝ) ≤
      (-(2973971066903655038759 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1521732495046507 / 5000000000000000 : ℝ) ≤
      (-(2973971066903655038759 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1521732495046507 / 5000000000000000 : ℚ))
        (r' := (1521732495046507 / 1250000000000000 : ℚ))
        (U := (-(2973971066903655038759 / 2500000000000000000000 : ℚ)))
        (U' := (491764834596344961241 / 2500000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (363185561803 / 800000000000 : ℚ))
      (s := (361833241324191 / 1250000000000000 : ℚ))
      (q := (1521732495046507 / 5000000000000000 : ℚ))
      (U := (-(2973971066903655038759 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_426_10 :
    Uω (aρ 10) (bρ 10) (363185561803 / 800000000000 : ℝ) ≤
      (-(1731301202107627005709 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5006270923733017 / 20000000000000000 : ℝ) ≤
      (-(1731301202107627005709 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5006270923733017 / 20000000000000000 : ℚ))
        (r' := (5006270923733017 / 5000000000000000 : ℚ))
        (U := (-(1731301202107627005709 / 1250000000000000000000 : ℚ)))
        (U' := (1566748642372994291 / 1250000000000000000000 : ℚ))
        2 2 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (363185561803 / 800000000000 : ℚ))
      (s := (2202565907635517 / 10000000000000000 : ℚ))
      (q := (5006270923733017 / 20000000000000000 : ℚ))
      (U := (-(1731301202107627005709 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_426_11 :
    Uω (aρ 11) (bρ 11) (363185561803 / 800000000000 : ℝ) ≤
      (-(17687769941311851423913 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1705414343765671 / 10000000000000000 : ℝ) ≤
      (-(17687769941311851423913 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1705414343765671 / 10000000000000000 : ℚ))
        (r' := (1705414343765671 / 1250000000000000 : ℚ))
        (U := (-(17687769941311851423913 / 10000000000000000000000 : ℚ)))
        (U' := (3106645467688148576087 / 10000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (363185561803 / 800000000000 : ℚ))
      (s := (512800148819421 / 5000000000000000 : ℚ))
      (q := (1705414343765671 / 10000000000000000 : ℚ))
      (U := (-(17687769941311851423913 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_426_12 :
    Uω (aρ 12) (bρ 12) (363185561803 / 800000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_426_13 :
    Uω (aρ 13) (bρ 13) (363185561803 / 800000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_426_14 :
    Uω (aρ 14) (bρ 14) (363185561803 / 800000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_426_15 :
    Uω (aρ 15) (bρ 15) (363185561803 / 800000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_426_16 :
    Uω (aρ 16) (bρ 16) (363185561803 / 800000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_426 :
    Uρ (363185561803 / 800000000000 : ℝ) ≤
      (-(11856629194172474159109 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_426_1 U_426_2 U_426_3 U_426_4 U_426_5 U_426_6 U_426_7 U_426_8 U_426_9 U_426_10
    U_426_11 U_426_12 U_426_13 U_426_14 U_426_15 U_426_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_427_1 :
    Uω (aρ 1) (bρ 1) (28415256387 / 62500000000 : ℝ) ≤
      (-(2006340758789207906781 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8963815465228221 / 20000000000000000 : ℝ) ≤
      (-(2006340758789207906781 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8963815465228221 / 20000000000000000 : ℚ))
        (r' := (8963815465228221 / 5000000000000000 : ℚ))
        (U := (-(2006340758789207906781 / 2500000000000000000000 : ℚ)))
        (U' := (1459395142710792093219 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (28415256387 / 62500000000 : ℚ))
      (s := (4481871661393221 / 10000000000000000 : ℚ))
      (q := (8963815465228221 / 20000000000000000 : ℚ))
      (U := (-(2006340758789207906781 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_427_2 :
    Uω (aρ 2) (bρ 2) (28415256387 / 62500000000 : ℝ) ≤
      (-(1615798066397558523171 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8915873610458937 / 20000000000000000 : ℝ) ≤
      (-(1615798066397558523171 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8915873610458937 / 20000000000000000 : ℚ))
        (r' := (8915873610458937 / 5000000000000000 : ℚ))
        (U := (-(1615798066397558523171 / 2000000000000000000000 : ℚ)))
        (U' := (1156790654802441476829 / 2000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (28415256387 / 62500000000 : ℚ))
      (s := (4457698819133937 / 10000000000000000 : ℚ))
      (q := (8915873610458937 / 20000000000000000 : ℚ))
      (U := (-(1615798066397558523171 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_427_3 :
    Uω (aρ 3) (bρ 3) (28415256387 / 62500000000 : ℝ) ≤
      (-(818724033738776100043 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4409939888919593 / 10000000000000000 : ℝ) ≤
      (-(818724033738776100043 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4409939888919593 / 10000000000000000 : ℚ))
        (r' := (4409939888919593 / 2500000000000000 : ℚ))
        (U := (-(818724033738776100043 / 1000000000000000000000 : ℚ)))
        (U' := (567570326861223899957 / 1000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (28415256387 / 62500000000 : ℚ))
      (s := (2204550546432093 / 5000000000000000 : ℚ))
      (q := (4409939888919593 / 10000000000000000 : ℚ))
      (U := (-(818724033738776100043 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_427_4 :
    Uω (aρ 4) (bρ 4) (28415256387 / 62500000000 : ℝ) ≤
      (-(1046256103529695111109 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4330054851211299 / 10000000000000000 : ℝ) ≤
      (-(1046256103529695111109 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4330054851211299 / 10000000000000000 : ℚ))
        (r' := (4330054851211299 / 2500000000000000 : ℚ))
        (U := (-(1046256103529695111109 / 1250000000000000000000 : ℚ)))
        (U' := (686611847220304888891 / 1250000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (28415256387 / 62500000000 : ℚ))
      (s := (2163812599256299 / 5000000000000000 : ℚ))
      (q := (4330054851211299 / 10000000000000000 : ℚ))
      (U := (-(1046256103529695111109 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_427_5 :
    Uω (aρ 5) (bρ 5) (28415256387 / 62500000000 : ℝ) ≤
      (-(2164013955424430799831 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4207966482862127 / 10000000000000000 : ℝ) ≤
      (-(2164013955424430799831 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4207966482862127 / 10000000000000000 : ℚ))
        (r' := (4207966482862127 / 2500000000000000 : ℚ))
        (U := (-(2164013955424430799831 / 2500000000000000000000 : ℚ)))
        (U' := (1301721946075569200169 / 2500000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (28415256387 / 62500000000 : ℚ))
      (s := (2100819190574627 / 5000000000000000 : ℚ))
      (q := (4207966482862127 / 10000000000000000 : ℚ))
      (U := (-(2164013955424430799831 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_427_6 :
    Uω (aρ 6) (bρ 6) (28415256387 / 62500000000 : ℝ) ≤
      (-(9083634719625875003053 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4031835053215791 / 10000000000000000 : ℝ) ≤
      (-(9083634719625875003053 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4031835053215791 / 10000000000000000 : ℚ))
        (r' := (4031835053215791 / 2500000000000000 : ℚ))
        (U := (-(9083634719625875003053 / 10000000000000000000000 : ℚ)))
        (U' := (4779308886374124996947 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (28415256387 / 62500000000 : ℚ))
      (s := (2008307948498291 / 5000000000000000 : ℚ))
      (q := (4031835053215791 / 10000000000000000 : ℚ))
      (U := (-(9083634719625875003053 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_427_7 :
    Uω (aρ 7) (bρ 7) (28415256387 / 62500000000 : ℝ) ≤
      (-(4852190180007776394843 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1894585111256033 / 5000000000000000 : ℝ) ≤
      (-(4852190180007776394843 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1894585111256033 / 5000000000000000 : ℚ))
        (r' := (1894585111256033 / 1250000000000000 : ℚ))
        (U := (-(4852190180007776394843 / 5000000000000000000000 : ℚ)))
        (U' := (2079281622992223605157 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (28415256387 / 62500000000 : ℚ))
      (s := (938736904087283 / 2500000000000000 : ℚ))
      (q := (1894585111256033 / 5000000000000000 : ℚ))
      (U := (-(4852190180007776394843 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_427_8 :
    Uω (aρ 8) (bρ 8) (28415256387 / 62500000000 : ℝ) ≤
      (-(10592668610642755392833 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (693419807050719 / 2000000000000000 : ℝ) ≤
      (-(10592668610642755392833 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (693419807050719 / 2000000000000000 : ℚ))
        (r' := (693419807050719 / 500000000000000 : ℚ))
        (U := (-(10592668610642755392833 / 10000000000000000000000 : ℚ)))
        (U' := (3270274995357244607167 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (28415256387 / 62500000000 : ℚ))
      (s := (339434689317219 / 1000000000000000 : ℚ))
      (q := (693419807050719 / 2000000000000000 : ℚ))
      (U := (-(10592668610642755392833 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_427_9 :
    Uω (aρ 9) (bρ 9) (28415256387 / 62500000000 : ℝ) ≤
      (-(5936519118310741301741 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6100852096483651 / 20000000000000000 : ℝ) ≤
      (-(5936519118310741301741 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6100852096483651 / 20000000000000000 : ℚ))
        (r' := (6100852096483651 / 5000000000000000 : ℚ))
        (U := (-(5936519118310741301741 / 5000000000000000000000 : ℚ)))
        (U' := (994952684689258698259 / 5000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (28415256387 / 62500000000 : ℚ))
      (s := (2901966547508651 / 10000000000000000 : ℚ))
      (q := (6100852096483651 / 20000000000000000 : ℚ))
      (U := (-(5936519118310741301741 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_427_10 :
    Uω (aρ 10) (bρ 10) (28415256387 / 62500000000 : ℝ) ≤
      (-(3455101075548872166831 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5021314955928739 / 20000000000000000 : ℝ) ≤
      (-(3455101075548872166831 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5021314955928739 / 20000000000000000 : ℚ))
        (r' := (5021314955928739 / 5000000000000000 : ℚ))
        (U := (-(3455101075548872166831 / 2500000000000000000000 : ℚ)))
        (U' := (10634825951127833169 / 2500000000000000000000 : ℚ))
        2 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (28415256387 / 62500000000 : ℚ))
      (s := (2210988440448739 / 10000000000000000 : ℚ))
      (q := (5021314955928739 / 20000000000000000 : ℚ))
      (U := (-(3455101075548872166831 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_427_11 :
    Uω (aρ 11) (bρ 11) (28415256387 / 62500000000 : ℝ) ≤
      (-(8811842877035075998573 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3432756893474963 / 20000000000000000 : ℝ) ≤
      (-(8811842877035075998573 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3432756893474963 / 20000000000000000 : ℚ))
        (r' := (3432756893474963 / 2500000000000000 : ℚ))
        (U := (-(8811842877035075998573 / 5000000000000000000000 : ℚ)))
        (U' := (1585364827464924001427 / 5000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (28415256387 / 62500000000 : ℚ))
      (s := (1040907004199963 / 10000000000000000 : ℚ))
      (q := (3432756893474963 / 20000000000000000 : ℚ))
      (U := (-(8811842877035075998573 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_427_12 :
    Uω (aρ 12) (bρ 12) (28415256387 / 62500000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_427_13 :
    Uω (aρ 13) (bρ 13) (28415256387 / 62500000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_427_14 :
    Uω (aρ 14) (bρ 14) (28415256387 / 62500000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_427_15 :
    Uω (aρ 15) (bρ 15) (28415256387 / 62500000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_427_16 :
    Uω (aρ 16) (bρ 16) (28415256387 / 62500000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_427 :
    Uρ (28415256387 / 62500000000 : ℝ) ≤
      (-(11839246909114969195289 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_427_1 U_427_2 U_427_3 U_427_4 U_427_5 U_427_6 U_427_7 U_427_8 U_427_9 U_427_10
    U_427_11 U_427_12 U_427_13 U_427_14 U_427_15 U_427_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_428_1 :
    Uω (aρ 1) (bρ 1) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(8010599977827891867547 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8977058570418943 / 20000000000000000 : ℝ) ≤
      (-(8010599977827891867547 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8977058570418943 / 20000000000000000 : ℚ))
        (r' := (8977058570418943 / 5000000000000000 : ℚ))
        (U := (-(8010599977827891867547 / 10000000000000000000000 : ℚ)))
        (U' := (5852343628172108132453 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1821225008521 / 4000000000000 : ℚ))
      (s := (4488493267201443 / 10000000000000000 : ℚ))
      (q := (8977058570418943 / 20000000000000000 : ℚ))
      (U := (-(8010599977827891867547 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_428_2 :
    Uω (aρ 2) (bρ 2) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(1612829455829885220953 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1116139664398489 / 2500000000000000 : ℝ) ≤
      (-(1612829455829885220953 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1116139664398489 / 2500000000000000 : ℚ))
        (r' := (1116139664398489 / 625000000000000 : ℚ))
        (U := (-(1612829455829885220953 / 2000000000000000000000 : ℚ)))
        (U' := (1159759265370114779047 / 2000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1821225008521 / 4000000000000 : ℚ))
      (s := (1116080256120103 / 2500000000000000 : ℚ))
      (q := (1116139664398489 / 2500000000000000 : ℚ))
      (U := (-(1612829455829885220953 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_428_3 :
    Uω (aρ 3) (bρ 3) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(2043058452034576909719 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1104140661524963 / 2500000000000000 : ℝ) ≤
      (-(2043058452034576909719 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1104140661524963 / 2500000000000000 : ℚ))
        (r' := (1104140661524963 / 625000000000000 : ℚ))
        (U := (-(2043058452034576909719 / 2500000000000000000000 : ℚ)))
        (U' := (1422677449465423090281 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1821225008521 / 4000000000000 : ℚ))
      (s := (1103931276960551 / 2500000000000000 : ℚ))
      (q := (1104140661524963 / 2500000000000000 : ℚ))
      (U := (-(2043058452034576909719 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_428_4 :
    Uω (aρ 4) (bρ 4) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(4177379998365973504417 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8673360124821363 / 20000000000000000 : ℝ) ≤
      (-(4177379998365973504417 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8673360124821363 / 20000000000000000 : ℚ))
        (r' := (8673360124821363 / 5000000000000000 : ℚ))
        (U := (-(4177379998365973504417 / 5000000000000000000000 : ℚ)))
        (U' := (2754091804634026495583 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1821225008521 / 4000000000000 : ℚ))
      (s := (4334254121528863 / 10000000000000000 : ℚ))
      (q := (8673360124821363 / 20000000000000000 : ℚ))
      (U := (-(4177379998365973504417 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_428_5 :
    Uω (aρ 5) (bρ 5) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(8640308936621060834287 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8429195878384133 / 20000000000000000 : ℝ) ≤
      (-(8640308936621060834287 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8429195878384133 / 20000000000000000 : ℚ))
        (r' := (8429195878384133 / 5000000000000000 : ℚ))
        (U := (-(8640308936621060834287 / 10000000000000000000000 : ℚ)))
        (U' := (5222634669378939165713 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1821225008521 / 4000000000000 : ℚ))
      (s := (4208279794426633 / 10000000000000000 : ℚ))
      (q := (8429195878384133 / 20000000000000000 : ℚ))
      (U := (-(8640308936621060834287 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_428_6 :
    Uω (aρ 6) (bρ 6) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(9067163126475235429003 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1615392640135501 / 4000000000000000 : ℝ) ≤
      (-(9067163126475235429003 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1615392640135501 / 4000000000000000 : ℚ))
        (r' := (1615392640135501 / 1000000000000000 : ℚ))
        (U := (-(9067163126475235429003 / 10000000000000000000000 : ℚ)))
        (U' := (4795780479524764570997 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1821225008521 / 4000000000000 : ℚ))
      (s := (804657498372001 / 2000000000000000 : ℚ))
      (q := (1615392640135501 / 4000000000000000 : ℚ))
      (U := (-(9067163126475235429003 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_428_7 :
    Uω (aρ 7) (bρ 7) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(9686762106250244520731 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7591703926135517 / 20000000000000000 : ℝ) ≤
      (-(9686762106250244520731 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7591703926135517 / 20000000000000000 : ℚ))
        (r' := (7591703926135517 / 5000000000000000 : ℚ))
        (U := (-(9686762106250244520731 / 10000000000000000000000 : ℚ)))
        (U' := (4176181499749755479269 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (1821225008521 / 4000000000000 : ℚ))
      (s := (3761689598078017 / 10000000000000000 : ℚ))
      (q := (7591703926135517 / 20000000000000000 : ℚ))
      (U := (-(9686762106250244520731 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_428_8 :
    Uω (aρ 8) (bρ 8) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(10573180992541647374207 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27139548227949 / 78125000000000 : ℝ) ≤
      (-(10573180992541647374207 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27139548227949 / 78125000000000 : ℚ))
        (r' := (27139548227949 / 19531250000000 : ℚ))
        (U := (-(10573180992541647374207 / 10000000000000000000000 : ℚ)))
        (U' := (3289762613458352625793 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (1821225008521 / 4000000000000 : ℚ))
      (s := (850312917409361 / 2500000000000000 : ℚ))
      (q := (27139548227949 / 78125000000000 : ℚ))
      (U := (-(10573180992541647374207 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_428_9 :
    Uω (aρ 9) (bρ 9) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(11850249595588193161761 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1528692740726231 / 5000000000000000 : ℝ) ≤
      (-(11850249595588193161761 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1528692740726231 / 5000000000000000 : ℚ))
        (r' := (1528692740726231 / 1250000000000000 : ℚ))
        (U := (-(11850249595588193161761 / 10000000000000000000000 : ℚ)))
        (U' := (2012694010411806838239 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (1821225008521 / 4000000000000 : ℚ))
      (s := (90914497329607 / 312500000000000 : ℚ))
      (q := (1528692740726231 / 5000000000000000 : ℚ))
      (U := (-(11850249595588193161761 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_428_10 :
    Uω (aρ 10) (bρ 10) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(6895256495096437908121 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (251817338999233 / 1000000000000000 : ℝ) ≤
      (-(6895256495096437908121 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (251817338999233 / 1000000000000000 : ℚ))
        (r' := (251817338999233 / 250000000000000 : ℚ))
        (U := (-(6895256495096437908121 / 5000000000000000000000 : ℚ)))
        (U' := (36215307903562091879 / 5000000000000000000000 : ℚ))
        2 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (1821225008521 / 4000000000000 : ℚ))
      (s := (27742484564027 / 125000000000000 : ℚ))
      (q := (251817338999233 / 1000000000000000 : ℚ))
      (U := (-(6895256495096437908121 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_428_11 :
    Uω (aρ 11) (bρ 11) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(3512106326516641677623 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3454504769179323 / 20000000000000000 : ℝ) ≤
      (-(3512106326516641677623 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3454504769179323 / 20000000000000000 : ℚ))
        (r' := (3454504769179323 / 2500000000000000 : ℚ))
        (U := (-(3512106326516641677623 / 2000000000000000000000 : ℚ)))
        (U' := (646776755283358322377 / 2000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (1821225008521 / 4000000000000 : ℚ))
      (s := (1056033380521823 / 10000000000000000 : ℚ))
      (q := (3454504769179323 / 20000000000000000 : ℚ))
      (U := (-(3512106326516641677623 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_428_12 :
    Uω (aρ 12) (bρ 12) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_428_13 :
    Uω (aρ 13) (bρ 13) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_428_14 :
    Uω (aρ 14) (bρ 14) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_428_15 :
    Uω (aρ 15) (bρ 15) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_428_16 :
    Uω (aρ 16) (bρ 16) (1821225008521 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_428 :
    Uρ (1821225008521 / 4000000000000 : ℝ) ≤
      (-(2364393220857954377449 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_428_1 U_428_2 U_428_3 U_428_4 U_428_5 U_428_6 U_428_7 U_428_8 U_428_9 U_428_10
    U_428_11 U_428_12 U_428_13 U_428_14 U_428_15 U_428_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_429_1 :
    Uω (aρ 1) (bρ 1) (911936804137 / 2000000000000 : ℝ) ≤
      (-(7995858683509481005467 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2247575418824031 / 5000000000000000 : ℝ) ≤
      (-(7995858683509481005467 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2247575418824031 / 5000000000000000 : ℚ))
        (r' := (2247575418824031 / 1250000000000000 : ℚ))
        (U := (-(7995858683509481005467 / 10000000000000000000000 : ℚ)))
        (U' := (5867084922490518994533 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (911936804137 / 2000000000000 : ℚ))
      (s := (1123778718174031 / 2500000000000000 : ℚ))
      (q := (2247575418824031 / 5000000000000000 : ℚ))
      (U := (-(7995858683509481005467 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_429_2 :
    Uω (aρ 2) (bρ 2) (911936804137 / 2000000000000 : ℝ) ≤
      (-(251541444613192942879 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8942361017825701 / 20000000000000000 : ℝ) ≤
      (-(251541444613192942879 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8942361017825701 / 20000000000000000 : ℚ))
        (r' := (8942361017825701 / 5000000000000000 : ℚ))
        (U := (-(251541444613192942879 / 312500000000000000000 : ℚ)))
        (U' := (181675543074307057121 / 312500000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (911936804137 / 2000000000000 : ℚ))
      (s := (4470943227735701 / 10000000000000000 : ℚ))
      (q := (8942361017825701 / 20000000000000000 : ℚ))
      (U := (-(251541444613192942879 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_429_3 :
    Uω (aρ 3) (bρ 3) (911936804137 / 2000000000000 : ℝ) ≤
      (-(4078624886629356679157 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2211592699756421 / 5000000000000000 : ℝ) ≤
      (-(4078624886629356679157 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2211592699756421 / 5000000000000000 : ℚ))
        (r' := (2211592699756421 / 1250000000000000 : ℚ))
        (U := (-(4078624886629356679157 / 5000000000000000000000 : ℚ)))
        (U' := (2852846916370643320843 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (911936804137 / 2000000000000 : ℚ))
      (s := (1105587278821421 / 2500000000000000 : ℚ))
      (q := (2211592699756421 / 5000000000000000 : ℚ))
      (U := (-(4078624886629356679157 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_429_4 :
    Uω (aρ 4) (bρ 4) (911936804137 / 2000000000000 : ℝ) ≤
      (-(8339494530471527057847 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8686610524559697 / 20000000000000000 : ℝ) ≤
      (-(8339494530471527057847 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8686610524559697 / 20000000000000000 : ℚ))
        (r' := (8686610524559697 / 5000000000000000 : ℚ))
        (U := (-(8339494530471527057847 / 10000000000000000000000 : ℚ)))
        (U' := (5523449075528472942153 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (911936804137 / 2000000000000 : ℚ))
      (s := (4340883021884697 / 10000000000000000 : ℚ))
      (q := (8686610524559697 / 20000000000000000 : ℚ))
      (U := (-(8339494530471527057847 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_429_5 :
    Uω (aρ 5) (bρ 5) (911936804137 / 2000000000000 : ℝ) ≤
      (-(8624586883225874612507 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (844245872838181 / 2000000000000000 : ℝ) ≤
      (-(8624586883225874612507 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (844245872838181 / 2000000000000000 : ℚ))
        (r' := (844245872838181 / 500000000000000 : ℚ))
        (U := (-(8624586883225874612507 / 10000000000000000000000 : ℚ)))
        (U' := (5238356722774125387493 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (911936804137 / 2000000000000 : ℚ))
      (s := (421492114504181 / 1000000000000000 : ℚ))
      (q := (844245872838181 / 2000000000000000 : ℚ))
      (U := (-(8624586883225874612507 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_429_6 :
    Uω (aρ 6) (bρ 6) (911936804137 / 2000000000000 : ℝ) ≤
      (-(4525359412151244814811 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8090256129680071 / 20000000000000000 : ℝ) ≤
      (-(4525359412151244814811 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8090256129680071 / 20000000000000000 : ℚ))
        (r' := (8090256129680071 / 5000000000000000 : ℚ))
        (U := (-(4525359412151244814811 / 5000000000000000000000 : ℚ)))
        (U' := (2406112390848755185189 / 5000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (911936804137 / 2000000000000 : ℚ))
      (s := (4029958921480071 / 10000000000000000 : ℚ))
      (q := (8090256129680071 / 20000000000000000 : ℚ))
      (U := (-(4525359412151244814811 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_429_7 :
    Uω (aρ 7) (bρ 7) (911936804137 / 2000000000000 : ℝ) ≤
      (-(1933835079997006956291 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (950633372499571 / 2500000000000000 : ℝ) ≤
      (-(1933835079997006956291 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (950633372499571 / 2500000000000000 : ℚ))
        (r' := (950633372499571 / 625000000000000 : ℚ))
        (U := (-(1933835079997006956291 / 2000000000000000000000 : ℚ)))
        (U' := (838753641202993043709 / 2000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (911936804137 / 2000000000000 : ℚ))
      (s := (471053894069571 / 1250000000000000 : ℚ))
      (q := (950633372499571 / 2500000000000000 : ℚ))
      (U := (-(1933835079997006956291 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_429_8 :
    Uω (aρ 8) (bρ 8) (911936804137 / 2000000000000 : ℝ) ≤
      (-(5276866446176848011757 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6961249497933711 / 20000000000000000 : ℝ) ≤
      (-(5276866446176848011757 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6961249497933711 / 20000000000000000 : ℚ))
        (r' := (6961249497933711 / 5000000000000000 : ℚ))
        (U := (-(5276866446176848011757 / 5000000000000000000000 : ℚ)))
        (U' := (1654605356823151988243 / 5000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (911936804137 / 2000000000000 : ℚ))
      (s := (3408155321833711 / 10000000000000000 : ℚ))
      (q := (6961249497933711 / 20000000000000000 : ℚ))
      (U := (-(5276866446176848011757 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_429_9 :
    Uω (aρ 9) (bρ 9) (911936804137 / 2000000000000 : ℝ) ≤
      (-(5913759015820159389253 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1225737320768777 / 4000000000000000 : ℝ) ≤
      (-(5913759015820159389253 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1225737320768777 / 4000000000000000 : ℚ))
        (r' := (1225737320768777 / 1000000000000000 : ℚ))
        (U := (-(5913759015820159389253 / 5000000000000000000000 : ℚ)))
        (U' := (1017712787179840610747 / 5000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (911936804137 / 2000000000000 : ℚ))
      (s := (583311611220777 / 2000000000000000 : ℚ))
      (q := (1225737320768777 / 4000000000000000 : ℚ))
      (U := (-(5913759015820159389253 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_429_10 :
    Uω (aρ 10) (bρ 10) (911936804137 / 2000000000000 : ℝ) ≤
      (-(1720091831909998787893 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2525683267082197 / 10000000000000000 : ℝ) ≤
      (-(1720091831909998787893 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2525683267082197 / 10000000000000000 : ℚ))
        (r' := (2525683267082197 / 2500000000000000 : ℚ))
        (U := (-(1720091831909998787893 / 1250000000000000000000 : ℚ)))
        (U' := (12776118840001212107 / 1250000000000000000000 : ℚ))
        2 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (911936804137 / 2000000000000 : ℚ))
      (s := (1113898509959697 / 5000000000000000 : ℚ))
      (q := (2525683267082197 / 10000000000000000 : ℚ))
      (U := (-(1720091831909998787893 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_429_11 :
    Uω (aρ 11) (bρ 11) (911936804137 / 2000000000000 : ℝ) ≤
      (-(17498270634776701115959 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (434509994437601 / 2500000000000000 : ℝ) ≤
      (-(17498270634776701115959 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (434509994437601 / 2500000000000000 : ℚ))
        (r' := (434509994437601 / 312500000000000 : ℚ))
        (U := (-(17498270634776701115959 / 10000000000000000000000 : ℚ)))
        (U' := (3296144774223298884041 / 10000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (911936804137 / 2000000000000 : ℚ))
      (s := (133873383432601 / 1250000000000000 : ℚ))
      (q := (434509994437601 / 2500000000000000 : ℚ))
      (U := (-(17498270634776701115959 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_429_12 :
    Uω (aρ 12) (bρ 12) (911936804137 / 2000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_429_13 :
    Uω (aρ 13) (bρ 13) (911936804137 / 2000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_429_14 :
    Uω (aρ 14) (bρ 14) (911936804137 / 2000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_429_15 :
    Uω (aρ 15) (bρ 15) (911936804137 / 2000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_429_16 :
    Uω (aρ 16) (bρ 16) (911936804137 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_429 :
    Uρ (911936804137 / 2000000000000 : ℝ) ≤
      (-(11804783702785120325837 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_429_1 U_429_2 U_429_3 U_429_4 U_429_5 U_429_6 U_429_7 U_429_8 U_429_9 U_429_10
    U_429_11 U_429_12 U_429_13 U_429_14 U_429_15 U_429_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_430_1 :
    Uω (aρ 1) (bρ 1) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(3990569544065491910013 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4501772389930573 / 10000000000000000 : ℝ) ≤
      (-(3990569544065491910013 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4501772389930573 / 10000000000000000 : ℚ))
        (r' := (4501772389930573 / 2500000000000000 : ℚ))
        (U := (-(3990569544065491910013 / 5000000000000000000000 : ℚ)))
        (U' := (2940902258934508089987 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1826522208027 / 4000000000000 : ℚ))
      (s := (2250868238939323 / 5000000000000000 : ℚ))
      (q := (4501772389930573 / 10000000000000000 : ℚ))
      (U := (-(3990569544065491910013 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_430_2 :
    Uω (aρ 2) (bρ 2) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(1004315889034024038327 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8955604718381581 / 20000000000000000 : ℝ) ≤
      (-(1004315889034024038327 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8955604718381581 / 20000000000000000 : ℚ))
        (r' := (8955604718381581 / 5000000000000000 : ℚ))
        (U := (-(1004315889034024038327 / 1250000000000000000000 : ℚ)))
        (U' := (728552061715975961673 / 1250000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1826522208027 / 4000000000000 : ℚ))
      (s := (4477565428909081 / 10000000000000000 : ℚ))
      (q := (8955604718381581 / 20000000000000000 : ℚ))
      (U := (-(1004315889034024038327 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_430_3 :
    Uω (aρ 3) (bρ 3) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(8142288165387616772923 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2214904074587733 / 5000000000000000 : ℝ) ≤
      (-(8142288165387616772923 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2214904074587733 / 5000000000000000 : ℚ))
        (r' := (2214904074587733 / 1250000000000000 : ℚ))
        (U := (-(8142288165387616772923 / 10000000000000000000000 : ℚ)))
        (U' := (5720655440612383227077 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1826522208027 / 4000000000000 : ℚ))
      (s := (276810819701777 / 625000000000000 : ℚ))
      (q := (2214904074587733 / 5000000000000000 : ℚ))
      (U := (-(8142288165387616772923 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_430_4 :
    Uω (aρ 4) (bρ 4) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(4162126179034898229433 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4349930450870627 / 10000000000000000 : ℝ) ≤
      (-(4162126179034898229433 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4349930450870627 / 10000000000000000 : ℚ))
        (r' := (4349930450870627 / 2500000000000000 : ℚ))
        (U := (-(4162126179034898229433 / 5000000000000000000000 : ℚ)))
        (U' := (2769345623965101770567 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1826522208027 / 4000000000000 : ℚ))
      (s := (2173755949841877 / 5000000000000000 : ℚ))
      (q := (4349930450870627 / 10000000000000000 : ℚ))
      (U := (-(4162126179034898229433 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_430_5 :
    Uω (aρ 5) (bρ 5) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(2152222395771836180129 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4227860758006511 / 10000000000000000 : ℝ) ≤
      (-(2152222395771836180129 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4227860758006511 / 10000000000000000 : ℚ))
        (r' := (4227860758006511 / 2500000000000000 : ℚ))
        (U := (-(2152222395771836180129 / 2500000000000000000000 : ℚ)))
        (U' := (1313513505728163819871 / 2500000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1826522208027 / 4000000000000 : ℚ))
      (s := (2110781216645261 / 5000000000000000 : ℚ))
      (q := (4227860758006511 / 10000000000000000 : ℚ))
      (U := (-(2152222395771836180129 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_430_6 :
    Uω (aρ 6) (bρ 6) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(9034301722152087805031 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8103548894258587 / 20000000000000000 : ℝ) ≤
      (-(9034301722152087805031 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8103548894258587 / 20000000000000000 : ℚ))
        (r' := (8103548894258587 / 5000000000000000 : ℚ))
        (U := (-(9034301722152087805031 / 10000000000000000000000 : ℚ)))
        (U' := (4828641883847912194969 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1826522208027 / 4000000000000 : ℚ))
      (s := (4036630186676087 / 10000000000000000 : ℚ))
      (q := (8103548894258587 / 20000000000000000 : ℚ))
      (U := (-(9034301722152087805031 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_430_7 :
    Uω (aρ 7) (bρ 7) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(2412905031614942433679 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1523685921779237 / 4000000000000000 : ℝ) ≤
      (-(2412905031614942433679 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1523685921779237 / 4000000000000000 : ℚ))
        (r' := (1523685921779237 / 1000000000000000 : ℚ))
        (U := (-(2412905031614942433679 / 2500000000000000000000 : ℚ)))
        (U' := (1052830869885057566321 / 2500000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (1826522208027 / 4000000000000 : ℚ))
      (s := (755034456414737 / 2000000000000000 : ℚ))
      (q := (1523685921779237 / 4000000000000000 : ℚ))
      (U := (-(2412905031614942433679 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_430_8 :
    Uω (aρ 8) (bρ 8) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(2633581035938500616407 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6974773532061733 / 20000000000000000 : ℝ) ≤
      (-(2633581035938500616407 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6974773532061733 / 20000000000000000 : ℚ))
        (r' := (6974773532061733 / 5000000000000000 : ℚ))
        (U := (-(2633581035938500616407 / 2500000000000000000000 : ℚ)))
        (U' := (832154865561499383593 / 2500000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (1826522208027 / 4000000000000 : ℚ))
      (s := (3415057856579233 / 10000000000000000 : ℚ))
      (q := (6974773532061733 / 20000000000000000 : ℚ))
      (U := (-(2633581035938500616407 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_430_9 :
    Uω (aρ 9) (bρ 9) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(11804843234626741708411 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (191956220107513 / 625000000000000 : ℝ) ≤
      (-(11804843234626741708411 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (191956220107513 / 625000000000000 : ℚ))
        (r' := (191956220107513 / 156250000000000 : ℚ))
        (U := (-(11804843234626741708411 / 10000000000000000000000 : ℚ)))
        (U' := (2058100371373258291589 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (1826522208027 / 4000000000000 : ℚ))
      (s := (730962249079479 / 2500000000000000 : ℚ))
      (q := (191956220107513 / 625000000000000 : ℚ))
      (U := (-(11804843234626741708411 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_430_10 :
    Uω (aρ 10) (bρ 10) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(13731068287134637534901 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (101327487089151 / 400000000000000 : ℝ) ≤
      (-(13731068287134637534901 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (101327487089151 / 400000000000000 : ℚ))
        (r' := (101327487089151 / 100000000000000 : ℚ))
        (U := (-(13731068287134637534901 / 10000000000000000000000 : ℚ)))
        (U' := (131875318865362465099 / 10000000000000000000000 : ℚ))
        2 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (1826522208027 / 4000000000000 : ℚ))
      (s := (44723666816601 / 200000000000000 : ℚ))
      (q := (101327487089151 / 400000000000000 : ℚ))
      (U := (-(13731068287134637534901 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_430_11 :
    Uω (aρ 11) (bρ 11) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(17436868223522066249077 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3497489587483911 / 20000000000000000 : ℝ) ≤
      (-(17436868223522066249077 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3497489587483911 / 20000000000000000 : ℚ))
        (r' := (3497489587483911 / 2500000000000000 : ℚ))
        (U := (-(17436868223522066249077 / 10000000000000000000000 : ℚ)))
        (U' := (3357547185477933750923 / 10000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (1826522208027 / 4000000000000 : ℚ))
      (s := (1085775200061411 / 10000000000000000 : ℚ))
      (q := (3497489587483911 / 20000000000000000 : ℚ))
      (U := (-(17436868223522066249077 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_430_12 :
    Uω (aρ 12) (bρ 12) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_430_13 :
    Uω (aρ 13) (bρ 13) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_430_14 :
    Uω (aρ 14) (bρ 14) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_430_15 :
    Uω (aρ 15) (bρ 15) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_430_16 :
    Uω (aρ 16) (bρ 16) (1826522208027 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_430 :
    Uρ (1826522208027 / 4000000000000 : ℝ) ≤
      (-(5893848409619263390529 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_430_1 U_430_2 U_430_3 U_430_4 U_430_5 U_430_6 U_430_7 U_430_8 U_430_9 U_430_10
    U_430_11 U_430_12 U_430_13 U_430_14 U_430_15 U_430_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_431_1 :
    Uω (aρ 1) (bρ 1) (91458540389 / 200000000000 : ℝ) ≤
      (-(7966441127904307519531 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4508393942057693 / 10000000000000000 : ℝ) ≤
      (-(7966441127904307519531 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4508393942057693 / 10000000000000000 : ℚ))
        (r' := (4508393942057693 / 2500000000000000 : ℚ))
        (U := (-(7966441127904307519531 / 10000000000000000000000 : ℚ)))
        (U' := (5896502478095692480469 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (91458540389 / 200000000000 : ℚ))
      (s := (2254179041375193 / 5000000000000000 : ℚ))
      (q := (4508393942057693 / 10000000000000000 : ℚ))
      (U := (-(7966441127904307519531 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_431_2 :
    Uω (aρ 2) (bρ 2) (91458540389 / 200000000000 : ℝ) ≤
      (-(4009874934127237774067 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1121106052108097 / 2500000000000000 : ℝ) ≤
      (-(4009874934127237774067 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1121106052108097 / 2500000000000000 : ℚ))
        (r' := (1121106052108097 / 625000000000000 : ℚ))
        (U := (-(4009874934127237774067 / 5000000000000000000000 : ℚ)))
        (U' := (2921596868872762225933 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (91458540389 / 200000000000 : ℚ))
      (s := (280261726750611 / 625000000000000 : ℚ))
      (q := (1121106052108097 / 2500000000000000 : ℚ))
      (U := (-(4009874934127237774067 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_431_3 :
    Uω (aρ 3) (bρ 3) (91458540389 / 200000000000 : ℝ) ≤
      (-(4063674458732947917093 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8872861790209053 / 20000000000000000 : ℝ) ≤
      (-(4063674458732947917093 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8872861790209053 / 20000000000000000 : ℚ))
        (r' := (8872861790209053 / 5000000000000000 : ℚ))
        (U := (-(4063674458732947917093 / 5000000000000000000000 : ℚ)))
        (U' := (2867797344267052082907 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (91458540389 / 200000000000 : ℚ))
      (s := (4435597107704053 / 10000000000000000 : ℚ))
      (q := (8872861790209053 / 20000000000000000 : ℚ))
      (U := (-(4063674458732947917093 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_431_4 :
    Uω (aρ 4) (bρ 4) (91458540389 / 200000000000 : ℝ) ≤
      (-(1661806681693453128021 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4356555628234529 / 10000000000000000 : ℝ) ≤
      (-(1661806681693453128021 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4356555628234529 / 10000000000000000 : ℚ))
        (r' := (4356555628234529 / 2500000000000000 : ℚ))
        (U := (-(1661806681693453128021 / 2000000000000000000000 : ℚ)))
        (U' := (1110782039506546871979 / 2000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (91458540389 / 200000000000 : ℚ))
      (s := (2177070377514529 / 5000000000000000 : ℚ))
      (q := (4356555628234529 / 10000000000000000 : ℚ))
      (U := (-(1661806681693453128021 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_431_5 :
    Uω (aρ 5) (bρ 5) (91458540389 / 200000000000 : ℝ) ≤
      (-(8593216958152678828791 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (169379684831433 / 400000000000000 : ℝ) ≤
      (-(8593216958152678828791 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (169379684831433 / 400000000000000 : ℚ))
        (r' := (169379684831433 / 100000000000000 : ℚ))
        (U := (-(8593216958152678828791 / 10000000000000000000000 : ℚ)))
        (U' := (5269726647847321171209 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (91458540389 / 200000000000 : ℚ))
      (s := (84564073189333 / 200000000000000 : ℚ))
      (q := (169379684831433 / 400000000000000 : ℚ))
      (U := (-(8593216958152678828791 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_431_6 :
    Uω (aρ 6) (bρ 6) (91458540389 / 200000000000 : ℝ) ≤
      (-(9017911729525724670809 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8116841495226927 / 20000000000000000 : ℝ) ≤
      (-(9017911729525724670809 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8116841495226927 / 20000000000000000 : ℚ))
        (r' := (8116841495226927 / 5000000000000000 : ℚ))
        (U := (-(9017911729525724670809 / 10000000000000000000000 : ℚ)))
        (U' := (4845031876474275329191 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (91458540389 / 200000000000 : ℚ))
      (s := (4043301288261927 / 10000000000000000 : ℚ))
      (q := (8116841495226927 / 20000000000000000 : ℚ))
      (U := (-(9017911729525724670809 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_431_7 :
    Uω (aρ 7) (bρ 7) (91458540389 / 200000000000 : ℝ) ≤
      (-(38536384686198961727 / 40000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3815895907553403 / 10000000000000000 : ℝ) ≤
      (-(38536384686198961727 / 40000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3815895907553403 / 10000000000000000 : ℚ))
        (r' := (3815895907553403 / 2500000000000000 : ℚ))
        (U := (-(38536384686198961727 / 40000000000000000000 : ℚ)))
        (U' := (16915389737801038273 / 40000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (91458540389 / 200000000000 : ℚ))
      (s := (1890956494450903 / 5000000000000000 : ℚ))
      (q := (3815895907553403 / 10000000000000000 : ℚ))
      (U := (-(38536384686198961727 / 40000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_431_8 :
    Uω (aρ 8) (bρ 8) (91458540389 / 200000000000 : ℝ) ≤
      (-(10514954581502450073807 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (436768528468821 / 1250000000000000 : ℝ) ≤
      (-(10514954581502450073807 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (436768528468821 / 1250000000000000 : ℚ))
        (r' := (436768528468821 / 312500000000000 : ℚ))
        (U := (-(10514954581502450073807 / 10000000000000000000000 : ℚ)))
        (U' := (3347989024497549926193 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (91458540389 / 200000000000 : ℚ))
      (s := (427744910079517 / 1250000000000000 : ℚ))
      (q := (436768528468821 / 1250000000000000 : ℚ))
      (U := (-(10514954581502450073807 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_431_9 :
    Uω (aρ 9) (bρ 9) (91458540389 / 200000000000 : ℝ) ≤
      (-(5891112448543313736457 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1539127076395919 / 5000000000000000 : ℝ) ≤
      (-(5891112448543313736457 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1539127076395919 / 5000000000000000 : ℚ))
        (r' := (1539127076395919 / 1250000000000000 : ℚ))
        (U := (-(5891112448543313736457 / 5000000000000000000000 : ℚ)))
        (U' := (1040359354456686263543 / 5000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (91458540389 / 200000000000 : ℚ))
      (s := (732784189769669 / 2500000000000000 : ℚ))
      (q := (1539127076395919 / 5000000000000000 : ℚ))
      (U := (-(5891112448543313736457 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_431_10 :
    Uω (aρ 10) (bρ 10) (91458540389 / 200000000000 : ℝ) ≤
      (-(13701512890367255710259 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (635171296828693 / 2500000000000000 : ℝ) ≤
      (-(13701512890367255710259 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (635171296828693 / 2500000000000000 : ℚ))
        (r' := (635171296828693 / 625000000000000 : ℚ))
        (U := (-(13701512890367255710259 / 10000000000000000000000 : ℚ)))
        (U' := (161430715632744289741 / 10000000000000000000000 : ℚ))
        2 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (91458540389 / 200000000000 : ℚ))
      (s := (280569732702443 / 1250000000000000 : ℚ))
      (q := (635171296828693 / 2500000000000000 : ℚ))
      (U := (-(13701512890367255710259 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_431_11 :
    Uω (aρ 11) (bρ 11) (91458540389 / 200000000000 : ℝ) ≤
      (-(17376292052470984479999 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (109960635615987 / 625000000000000 : ℝ) ≤
      (-(17376292052470984479999 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (109960635615987 / 625000000000000 : ℚ))
        (r' := (109960635615987 / 78125000000000 : ℚ))
        (U := (-(17376292052470984479999 / 10000000000000000000000 : ℚ)))
        (U' := (3418123356529015520001 / 10000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (91458540389 / 200000000000 : ℚ))
      (s := (137550556613323 / 1250000000000000 : ℚ))
      (q := (109960635615987 / 625000000000000 : ℚ))
      (U := (-(17376292052470984479999 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_431_12 :
    Uω (aρ 12) (bρ 12) (91458540389 / 200000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_431_13 :
    Uω (aρ 13) (bρ 13) (91458540389 / 200000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_431_14 :
    Uω (aρ 14) (bρ 14) (91458540389 / 200000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_431_15 :
    Uω (aρ 15) (bρ 15) (91458540389 / 200000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_431_16 :
    Uω (aρ 16) (bρ 16) (91458540389 / 200000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_431 :
    Uρ (91458540389 / 200000000000 : ℝ) ≤
      (-(2942675685726804811747 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_431_1 U_431_2 U_431_3 U_431_4 U_431_5 U_431_6 U_431_7 U_431_8 U_431_9 U_431_10
    U_431_11 U_431_12 U_431_13 U_431_14 U_431_15 U_431_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_432_1 :
    Uω (aρ 1) (bρ 1) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(7951764739322229786499 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (903003098806021 / 2000000000000000 : ℝ) ≤
      (-(7951764739322229786499 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (903003098806021 / 2000000000000000 : ℚ))
        (r' := (903003098806021 / 500000000000000 : ℚ))
        (U := (-(7951764739322229786499 / 10000000000000000000000 : ℚ)))
        (U' := (5911178866677770213501 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1831819407533 / 4000000000000 : ℚ))
      (s := (451497968731271 / 1000000000000000 : ℚ))
      (q := (903003098806021 / 2000000000000000 : ℚ))
      (U := (-(7951764739322229786499 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_432_2 :
    Uω (aρ 2) (bρ 2) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(1000624303876394457959 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1796418422656891 / 4000000000000000 : ℝ) ≤
      (-(1000624303876394457959 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1796418422656891 / 4000000000000000 : ℚ))
        (r' := (1796418422656891 / 1000000000000000 : ℚ))
        (U := (-(1000624303876394457959 / 1250000000000000000000 : ℚ)))
        (U' := (732243646873605542041 / 1250000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1831819407533 / 4000000000000 : ℚ))
      (s := (898161965009391 / 2000000000000000 : ℚ))
      (q := (1796418422656891 / 4000000000000000 : ℚ))
      (U := (-(1000624303876394457959 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_432_3 :
    Uω (aρ 3) (bρ 3) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(31689187354433060421 / 39062500000000000000 : ℝ)) := by
  have hlg :
    Real.log (8886107274633451 / 20000000000000000 : ℝ) ≤
      (-(31689187354433060421 / 39062500000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8886107274633451 / 20000000000000000 : ℚ))
        (r' := (8886107274633451 / 5000000000000000 : ℚ))
        (U := (-(31689187354433060421 / 39062500000000000000 : ℚ)))
        (U' := (22462936106504439579 / 39062500000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1831819407533 / 4000000000000 : ℚ))
      (s := (4442221092745951 / 10000000000000000 : ℚ))
      (q := (8886107274633451 / 20000000000000000 : ℚ))
      (U := (-(31689187354433060421 / 39062500000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_432_4 :
    Uω (aρ 4) (bρ 4) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(8293837610929466732469 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1745272317769101 / 4000000000000000 : ℝ) ≤
      (-(8293837610929466732469 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1745272317769101 / 4000000000000000 : ℚ))
        (r' := (1745272317769101 / 1000000000000000 : ℚ))
        (U := (-(8293837610929466732469 / 10000000000000000000000 : ℚ)))
        (U' := (5569105995070533267531 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1831819407533 / 4000000000000 : ℚ))
      (s := (872153917604601 / 2000000000000000 : ℚ))
      (q := (1745272317769101 / 4000000000000000 : ℚ))
      (U := (-(8293837610929466732469 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_432_5 :
    Uω (aρ 5) (bρ 5) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(4288784465369381867481 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8482246905349727 / 20000000000000000 : ℝ) ≤
      (-(4288784465369381867481 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8482246905349727 / 20000000000000000 : ℚ))
        (r' := (8482246905349727 / 5000000000000000 : ℚ))
        (U := (-(4288784465369381867481 / 5000000000000000000000 : ℚ)))
        (U' := (2642687337630618132519 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1831819407533 / 4000000000000 : ℚ))
      (s := (4234844823862227 / 10000000000000000 : ℚ))
      (q := (8482246905349727 / 20000000000000000 : ℚ))
      (U := (-(4288784465369381867481 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_432_6 :
    Uω (aρ 6) (bρ 6) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(2250387189094811231179 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2032533483348397 / 5000000000000000 : ℝ) ≤
      (-(2250387189094811231179 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2032533483348397 / 5000000000000000 : ℚ))
        (r' := (2032533483348397 / 1250000000000000 : ℚ))
        (U := (-(2250387189094811231179 / 2500000000000000000000 : ℚ)))
        (U' := (1215348712405188768821 / 2500000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1831819407533 / 4000000000000 : ℚ))
      (s := (506246528380761 / 1250000000000000 : ℚ))
      (q := (2032533483348397 / 5000000000000000 : ℚ))
      (U := (-(2250387189094811231179 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_432_7 :
    Uω (aρ 7) (bρ 7) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(4808301710880464751429 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1529030720176911 / 4000000000000000 : ℝ) ≤
      (-(4808301710880464751429 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1529030720176911 / 4000000000000000 : ℚ))
        (r' := (1529030720176911 / 1000000000000000 : ℚ))
        (U := (-(4808301710880464751429 / 5000000000000000000000 : ℚ)))
        (U' := (2123170092119535248571 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (1831819407533 / 4000000000000 : ℚ))
      (s := (757730655059411 / 2000000000000000 : ℚ))
      (q := (1529030720176911 / 4000000000000000 : ℚ))
      (U := (-(4808301710880464751429 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_432_8 :
    Uω (aρ 8) (bρ 8) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(10495624041434001507059 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1750454568739631 / 5000000000000000 : ℝ) ≤
      (-(10495624041434001507059 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1750454568739631 / 5000000000000000 : ℚ))
        (r' := (1750454568739631 / 1250000000000000 : ℚ))
        (U := (-(10495624041434001507059 / 10000000000000000000000 : ℚ)))
        (U' := (3367319564565998492941 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (1831819407533 / 4000000000000 : ℚ))
      (s := (214303725044439 / 625000000000000 : ℚ))
      (q := (1750454568739631 / 5000000000000000 : ℚ))
      (U := (-(10495624041434001507059 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_432_9 :
    Uω (aρ 9) (bρ 9) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(2939915678554231113423 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6170414413915467 / 20000000000000000 : ℝ) ≤
      (-(2939915678554231113423 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6170414413915467 / 20000000000000000 : ℚ))
        (r' := (6170414413915467 / 5000000000000000 : ℚ))
        (U := (-(2939915678554231113423 / 2500000000000000000000 : ℚ)))
        (U' := (525820222945768886577 / 2500000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (1831819407533 / 4000000000000 : ℚ))
      (s := (2938421368027967 / 10000000000000000 : ℚ))
      (q := (6170414413915467 / 20000000000000000 : ℚ))
      (U := (-(2939915678554231113423 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_432_10 :
    Uω (aρ 10) (bρ 10) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(13672067484211088375381 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5096354726270043 / 20000000000000000 : ℝ) ≤
      (-(13672067484211088375381 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5096354726270043 / 20000000000000000 : ℚ))
        (r' := (5096354726270043 / 5000000000000000 : ℚ))
        (U := (-(13672067484211088375381 / 10000000000000000000000 : ℚ)))
        (U' := (190876121788911624619 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (1831819407533 / 4000000000000 : ℚ))
      (s := (2252920713877543 / 10000000000000000 : ℚ))
      (q := (5096354726270043 / 20000000000000000 : ℚ))
      (U := (-(13672067484211088375381 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_432_11 :
    Uω (aρ 11) (bρ 11) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(8658255887911272410519 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3539838466569181 / 20000000000000000 : ℝ) ≤
      (-(8658255887911272410519 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3539838466569181 / 20000000000000000 : ℚ))
        (r' := (3539838466569181 / 2500000000000000 : ℚ))
        (U := (-(8658255887911272410519 / 5000000000000000000000 : ℚ)))
        (U' := (1738951816588727589481 / 5000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (1831819407533 / 4000000000000 : ℚ))
      (s := (1114881080381681 / 10000000000000000 : ℚ))
      (q := (3539838466569181 / 20000000000000000 : ℚ))
      (U := (-(8658255887911272410519 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_432_12 :
    Uω (aρ 12) (bρ 12) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_432_13 :
    Uω (aρ 13) (bρ 13) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_432_14 :
    Uω (aρ 14) (bρ 14) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_432_15 :
    Uω (aρ 15) (bρ 15) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_432_16 :
    Uω (aρ 16) (bρ 16) (1831819407533 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_432 :
    Uρ (1831819407533 / 4000000000000 : ℝ) ≤
      (-(2938449730656911494861 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_432_1 U_432_2 U_432_3 U_432_4 U_432_5 U_432_6 U_432_7 U_432_8 U_432_9 U_432_10
    U_432_11 U_432_12 U_432_13 U_432_14 U_432_15 U_432_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_433_1 :
    Uω (aρ 1) (bρ 1) (917234003643 / 2000000000000 : ℝ) ≤
      (-(1587421971831349571987 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9043274091696977 / 20000000000000000 : ℝ) ≤
      (-(1587421971831349571987 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9043274091696977 / 20000000000000000 : ℚ))
        (r' := (9043274091696977 / 5000000000000000 : ℚ))
        (U := (-(1587421971831349571987 / 2000000000000000000000 : ℚ)))
        (U' := (1185166749368650428013 / 2000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (917234003643 / 2000000000000 : ℚ))
      (s := (4521601291566977 / 10000000000000000 : ℚ))
      (q := (9043274091696977 / 20000000000000000 : ℚ))
      (U := (-(1587421971831349571987 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_433_2 :
    Uω (aρ 2) (bρ 2) (917234003643 / 2000000000000 : ℝ) ≤
      (-(998782592033725802447 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4497667903824867 / 10000000000000000 : ℝ) ≤
      (-(998782592033725802447 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4497667903824867 / 10000000000000000 : ℚ))
        (r' := (4497667903824867 / 2500000000000000 : ℚ))
        (U := (-(998782592033725802447 / 1250000000000000000000 : ℚ)))
        (U' := (734085358716274197553 / 1250000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (917234003643 / 2000000000000 : ℚ))
      (s := (2248716010014867 / 5000000000000000 : ℚ))
      (q := (4497667903824867 / 10000000000000000 : ℚ))
      (U := (-(998782592033725802447 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_433_3 :
    Uω (aρ 3) (bρ 3) (917234003643 / 2000000000000 : ℝ) ≤
      (-(8097537234734476602597 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8899352751657329 / 20000000000000000 : ℝ) ≤
      (-(8097537234734476602597 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8899352751657329 / 20000000000000000 : ℚ))
        (r' := (8899352751657329 / 5000000000000000 : ℚ))
        (U := (-(8097537234734476602597 / 10000000000000000000000 : ℚ)))
        (U' := (5765406371265523397403 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (917234003643 / 2000000000000 : ℚ))
      (s := (4448845070387329 / 10000000000000000 : ℚ))
      (q := (8899352751657329 / 20000000000000000 : ℚ))
      (U := (-(8097537234734476602597 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_433_4 :
    Uω (aρ 4) (bρ 4) (917234003643 / 2000000000000 : ℝ) ≤
      (-(8278664895044969696437 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (873961189897237 / 2000000000000000 : ℝ) ≤
      (-(8278664895044969696437 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (873961189897237 / 2000000000000000 : ℚ))
        (r' := (873961189897237 / 500000000000000 : ℚ))
        (U := (-(8278664895044969696437 / 10000000000000000000000 : ℚ)))
        (U' := (5584278710955030303563 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (917234003643 / 2000000000000 : ℚ))
      (s := (436739839876737 / 1000000000000000 : ℚ))
      (q := (873961189897237 / 2000000000000000 : ℚ))
      (U := (-(8278664895044969696437 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_433_5 :
    Uω (aρ 5) (bρ 5) (917234003643 / 2000000000000 : ℝ) ≤
      (-(4280972711764913015427 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4247754753818727 / 10000000000000000 : ℝ) ≤
      (-(4280972711764913015427 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4247754753818727 / 10000000000000000 : ℚ))
        (r' := (4247754753818727 / 2500000000000000 : ℚ))
        (U := (-(4280972711764913015427 / 5000000000000000000000 : ℚ)))
        (U' := (2650499091235086984573 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (917234003643 / 2000000000000 : ℚ))
      (s := (2120742963383727 / 5000000000000000 : ℚ))
      (q := (4247754753818727 / 10000000000000000 : ℚ))
      (U := (-(4280972711764913015427 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_433_6 :
    Uω (aρ 6) (bρ 6) (917234003643 / 2000000000000 : ℝ) ≤
      (-(8985212713119600161899 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (325737048382469 / 800000000000000 : ℝ) ≤
      (-(8985212713119600161899 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (325737048382469 / 800000000000000 : ℚ))
        (r' := (325737048382469 / 200000000000000 : ℚ))
        (U := (-(8985212713119600161899 / 10000000000000000000000 : ℚ)))
        (U' := (4877730892880399838101 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (917234003643 / 2000000000000 : ℚ))
      (s := (162265720153269 / 400000000000000 : ℚ))
      (q := (325737048382469 / 800000000000000 : ℚ))
      (U := (-(8985212713119600161899 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_433_7 :
    Uω (aρ 7) (bρ 7) (917234003643 / 2000000000000 : ℝ) ≤
      (-(2399785441056326483251 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3829257484234693 / 10000000000000000 : ℝ) ≤
      (-(2399785441056326483251 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3829257484234693 / 10000000000000000 : ℚ))
        (r' := (3829257484234693 / 2500000000000000 : ℚ))
        (U := (-(2399785441056326483251 / 2500000000000000000000 : ℚ)))
        (U' := (1065950460443673516749 / 2500000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (917234003643 / 2000000000000 : ℚ))
      (s := (1897696571749693 / 5000000000000000 : ℚ))
      (q := (3829257484234693 / 10000000000000000 : ℚ))
      (U := (-(2399785441056326483251 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_433_8 :
    Uω (aρ 8) (bρ 8) (917234003643 / 2000000000000 : ℝ) ≤
      (-(1309541545056140365681 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3507669498542777 / 10000000000000000 : ℝ) ≤
      (-(1309541545056140365681 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3507669498542777 / 10000000000000000 : ℚ))
        (r' := (3507669498542777 / 2500000000000000 : ℚ))
        (U := (-(1309541545056140365681 / 1250000000000000000000 : ℚ)))
        (U' := (423326405693859634319 / 1250000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (917234003643 / 2000000000000 : ℚ))
      (s := (1717879411727777 / 5000000000000000 : ℚ))
      (q := (3507669498542777 / 10000000000000000 : ℚ))
      (U := (-(1309541545056140365681 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_433_9 :
    Uω (aρ 9) (bρ 9) (917234003643 / 2000000000000 : ℝ) ≤
      (-(11737156383840359370543 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (123686347836671 / 400000000000000 : ℝ) ≤
      (-(11737156383840359370543 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (123686347836671 / 400000000000000 : ℚ))
        (r' := (123686347836671 / 100000000000000 : ℚ))
        (U := (-(11737156383840359370543 / 10000000000000000000000 : ℚ)))
        (U' := (2125787222159640629457 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (917234003643 / 2000000000000 : ℚ))
      (s := (58914056931271 / 200000000000000 : ℚ))
      (q := (123686347836671 / 400000000000000 : ℚ))
      (U := (-(11737156383840359370543 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_433_10 :
    Uω (aρ 10) (bρ 10) (917234003643 / 2000000000000 : ℝ) ≤
      (-(6821365551110305732887 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2555663769420043 / 10000000000000000 : ℝ) ≤
      (-(6821365551110305732887 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2555663769420043 / 10000000000000000 : ℚ))
        (r' := (2555663769420043 / 2500000000000000 : ℚ))
        (U := (-(6821365551110305732887 / 5000000000000000000000 : ℚ)))
        (U' := (110106251889694267113 / 5000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (917234003643 / 2000000000000 : ℚ))
      (s := (1130636013532543 / 5000000000000000 : ℚ))
      (q := (2555663769420043 / 10000000000000000 : ℚ))
      (U := (-(6821365551110305732887 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_433_11 :
    Uω (aρ 11) (bρ 11) (917234003643 / 2000000000000 : ℝ) ≤
      (-(8628749439416123003623 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3560789838101703 / 20000000000000000 : ℝ) ≤
      (-(8628749439416123003623 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3560789838101703 / 20000000000000000 : ℚ))
        (r' := (3560789838101703 / 2500000000000000 : ℚ))
        (U := (-(8628749439416123003623 / 5000000000000000000000 : ℚ)))
        (U' := (1768458265083876996377 / 5000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (917234003643 / 2000000000000 : ℚ))
      (s := (1129210952531703 / 10000000000000000 : ℚ))
      (q := (3560789838101703 / 20000000000000000 : ℚ))
      (U := (-(8628749439416123003623 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_433_12 :
    Uω (aρ 12) (bρ 12) (917234003643 / 2000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_433_13 :
    Uω (aρ 13) (bρ 13) (917234003643 / 2000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_433_14 :
    Uω (aρ 14) (bρ 14) (917234003643 / 2000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_433_15 :
    Uω (aρ 15) (bρ 15) (917234003643 / 2000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_433_16 :
    Uω (aρ 16) (bρ 16) (917234003643 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_433 :
    Uρ (917234003643 / 2000000000000 : ℝ) ≤
      (-(2934245738353066200817 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_433_1 U_433_2 U_433_3 U_433_4 U_433_5 U_433_6 U_433_7 U_433_8 U_433_9 U_433_10
    U_433_11 U_433_12 U_433_13 U_433_14 U_433_15 U_433_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_434_1 :
    Uω (aρ 1) (bρ 1) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(3961238212228721508109 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (56603232468919 / 125000000000000 : ℝ) ≤
      (-(3961238212228721508109 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (56603232468919 / 125000000000000 : ℚ))
        (r' := (56603232468919 / 31250000000000 : ℚ))
        (U := (-(3961238212228721508109 / 5000000000000000000000 : ℚ)))
        (U' := (2970233590771278491891 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1837116607039 / 4000000000000 : ℚ))
      (s := (226411144775727 / 500000000000000 : ℚ))
      (q := (56603232468919 / 125000000000000 : ℚ))
      (U := (-(3961238212228721508109 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_434_2 :
    Uω (aρ 2) (bρ 2) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(7975548720041766875749 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9008579499969673 / 20000000000000000 : ℝ) ≤
      (-(7975548720041766875749 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9008579499969673 / 20000000000000000 : ℚ))
        (r' := (9008579499969673 / 5000000000000000 : ℚ))
        (U := (-(7975548720041766875749 / 10000000000000000000000 : ℚ)))
        (U' := (5887394885958233124251 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1837116607039 / 4000000000000 : ℚ))
      (s := (4504054212967173 / 10000000000000000 : ℚ))
      (q := (9008579499969673 / 20000000000000000 : ℚ))
      (U := (-(7975548720041766875749 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_434_3 :
    Uω (aρ 3) (bρ 3) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(4041332333650775896749 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1782519644262739 / 4000000000000000 : ℝ) ≤
      (-(4041332333650775896749 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1782519644262739 / 4000000000000000 : ℚ))
        (r' := (1782519644262739 / 1000000000000000 : ℚ))
        (U := (-(4041332333650775896749 / 5000000000000000000000 : ℚ)))
        (U' := (2890139469349224103251 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1837116607039 / 4000000000000 : ℚ))
      (s := (891093808132239 / 2000000000000000 : ℚ))
      (q := (1782519644262739 / 4000000000000000 : ℚ))
      (U := (-(4041332333650775896749 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_434_4 :
    Uω (aρ 4) (bρ 4) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(4131757595361709041687 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (875286218695081 / 2000000000000000 : ℝ) ≤
      (-(4131757595361709041687 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (875286218695081 / 2000000000000000 : ℚ))
        (r' := (875286218695081 / 500000000000000 : ℚ))
        (U := (-(4131757595361709041687 / 5000000000000000000000 : ℚ)))
        (U' := (2799714207638290958313 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1837116607039 / 4000000000000 : ℚ))
      (s := (437402718736331 / 1000000000000000 : ℚ))
      (q := (875286218695081 / 2000000000000000 : ℚ))
      (U := (-(4131757595361709041687 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_434_5 :
    Uω (aρ 5) (bρ 5) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(1709269271915022459983 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1701754409744643 / 4000000000000000 : ℝ) ≤
      (-(1709269271915022459983 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1701754409744643 / 4000000000000000 : ℚ))
        (r' := (1701754409744643 / 1000000000000000 : ℚ))
        (U := (-(1709269271915022459983 / 2000000000000000000000 : ℚ)))
        (U' := (1063319449284977540017 / 2000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1837116607039 / 4000000000000 : ℚ))
      (s := (849625393694143 / 2000000000000000 : ℚ))
      (q := (1701754409744643 / 4000000000000000 : ℚ))
      (U := (-(1709269271915022459983 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_434_6 :
    Uω (aρ 6) (bρ 6) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(8968903510601811328087 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4078359162264601 / 10000000000000000 : ℝ) ≤
      (-(8968903510601811328087 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4078359162264601 / 10000000000000000 : ℚ))
        (r' := (4078359162264601 / 2500000000000000 : ℚ))
        (U := (-(8968903510601811328087 / 10000000000000000000000 : ℚ)))
        (U' := (4894040095398188671913 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1837116607039 / 4000000000000 : ℚ))
      (s := (2031656809708351 / 5000000000000000 : ℚ))
      (q := (4078359162264601 / 10000000000000000 : ℚ))
      (U := (-(8968903510601811328087 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_434_7 :
    Uω (aρ 7) (bρ 7) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(4790855543348075876977 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1534375184017047 / 4000000000000000 : ℝ) ≤
      (-(4790855543348075876977 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1534375184017047 / 4000000000000000 : ℚ))
        (r' := (1534375184017047 / 1000000000000000 : ℚ))
        (U := (-(4790855543348075876977 / 5000000000000000000000 : ℚ)))
        (U' := (2140616259651924123023 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (1837116607039 / 4000000000000 : ℚ))
      (s := (760426519146547 / 2000000000000000 : ℚ))
      (q := (1534375184017047 / 4000000000000000 : ℚ))
      (U := (-(4790855543348075876977 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_434_8 :
    Uω (aρ 8) (bρ 8) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(10457079376504312439157 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7028858628479507 / 20000000000000000 : ℝ) ≤
      (-(10457079376504312439157 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7028858628479507 / 20000000000000000 : ℚ))
        (r' := (7028858628479507 / 5000000000000000 : ℚ))
        (U := (-(10457079376504312439157 / 10000000000000000000000 : ℚ)))
        (U' := (3405864229495687560843 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (1837116607039 / 4000000000000 : ℚ))
      (s := (3442656955467007 / 10000000000000000 : ℚ))
      (q := (7028858628479507 / 20000000000000000 : ℚ))
      (U := (-(10457079376504312439157 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_434_9 :
    Uω (aρ 9) (bρ 9) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(2928676401593483871823 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3099108631247451 / 10000000000000000 : ℝ) ≤
      (-(2928676401593483871823 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3099108631247451 / 10000000000000000 : ℚ))
        (r' := (3099108631247451 / 2500000000000000 : ℚ))
        (U := (-(2928676401593483871823 / 2500000000000000000000 : ℚ)))
        (U' := (537059499906516128177 / 2500000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (1837116607039 / 4000000000000 : ℚ))
      (s := (1476490608921201 / 5000000000000000 : ℚ))
      (q := (3099108631247451 / 10000000000000000 : ℚ))
      (U := (-(2928676401593483871823 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_434_10 :
    Uω (aρ 10) (bρ 10) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(13613502791977963723017 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5126288939717917 / 20000000000000000 : ℝ) ≤
      (-(13613502791977963723017 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5126288939717917 / 20000000000000000 : ℚ))
        (r' := (5126288939717917 / 5000000000000000 : ℚ))
        (U := (-(13613502791977963723017 / 10000000000000000000000 : ℚ)))
        (U' := (249440814022036276983 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (1837116607039 / 4000000000000 : ℚ))
      (s := (2269611928560417 / 10000000000000000 : ℚ))
      (q := (5126288939717917 / 20000000000000000 : ℚ))
      (U := (-(13613502791977963723017 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_434_11 :
    Uω (aρ 11) (bρ 11) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(3439845305272605237621 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1790799986019643 / 10000000000000000 : ℝ) ≤
      (-(3439845305272605237621 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1790799986019643 / 10000000000000000 : ℚ))
        (r' := (1790799986019643 / 1250000000000000 : ℚ))
        (U := (-(3439845305272605237621 / 2000000000000000000000 : ℚ)))
        (U' := (719037776527394762379 / 2000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (1837116607039 / 4000000000000 : ℚ))
      (s := (571699793543393 / 5000000000000000 : ℚ))
      (q := (1790799986019643 / 10000000000000000 : ℚ))
      (U := (-(3439845305272605237621 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_434_12 :
    Uω (aρ 12) (bρ 12) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_434_13 :
    Uω (aρ 13) (bρ 13) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_434_14 :
    Uω (aρ 14) (bρ 14) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_434_15 :
    Uω (aρ 15) (bρ 15) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_434_16 :
    Uω (aρ 16) (bρ 16) (1837116607039 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_434 :
    Uρ (1837116607039 / 4000000000000 : ℝ) ≤
      (-(1172025256447057801947 / 1000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_434_1 U_434_2 U_434_3 U_434_4 U_434_5 U_434_6 U_434_7 U_434_8 U_434_9 U_434_10
    U_434_11 U_434_12 U_434_13 U_434_14 U_434_15 U_434_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_435_1 :
    Uω (aρ 1) (bρ 1) (229970650849 / 500000000000 : ℝ) ≤
      (-(3953932186274931808203 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9069760298051741 / 20000000000000000 : ℝ) ≤
      (-(3953932186274931808203 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9069760298051741 / 20000000000000000 : ℚ))
        (r' := (9069760298051741 / 5000000000000000 : ℚ))
        (U := (-(3953932186274931808203 / 5000000000000000000000 : ℚ)))
        (U' := (2977539616725068191797 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (229970650849 / 500000000000 : ℚ))
      (s := (4534844499156741 / 10000000000000000 : ℚ))
      (q := (9069760298051741 / 20000000000000000 : ℚ))
      (U := (-(3953932186274931808203 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_435_2 :
    Uω (aρ 2) (bρ 2) (229970650849 / 500000000000 : ℝ) ≤
      (-(1592171663724093181691 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9021823190253283 / 20000000000000000 : ℝ) ≤
      (-(1592171663724093181691 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9021823190253283 / 20000000000000000 : ℚ))
        (r' := (9021823190253283 / 5000000000000000 : ℚ))
        (U := (-(1592171663724093181691 / 2000000000000000000000 : ℚ)))
        (U' := (1180417057475906818309 / 2000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (229970650849 / 500000000000 : ℚ))
      (s := (4510676403868283 / 10000000000000000 : ℚ))
      (q := (9021823190253283 / 20000000000000000 : ℚ))
      (U := (-(1592171663724093181691 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_435_3 :
    Uω (aρ 3) (bρ 3) (229970650849 / 500000000000 : ℝ) ≤
      (-(1008476774321000244151 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8925843683635361 / 20000000000000000 : ℝ) ≤
      (-(1008476774321000244151 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8925843683635361 / 20000000000000000 : ℚ))
        (r' := (8925843683635361 / 5000000000000000 : ℚ))
        (U := (-(1008476774321000244151 / 1250000000000000000000 : ℚ)))
        (U' := (724391176428999755849 / 1250000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (229970650849 / 500000000000 : ℚ))
      (s := (4462093003600361 / 10000000000000000 : ℚ))
      (q := (8925843683635361 / 20000000000000000 : ℚ))
      (U := (-(1008476774321000244151 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_435_4 :
    Uω (aρ 4) (bρ 4) (229970650849 / 500000000000 : ℝ) ≤
      (-(1031048553524197032573 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (876611245288137 / 2000000000000000 : ℝ) ≤
      (-(1031048553524197032573 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (876611245288137 / 2000000000000000 : ℚ))
        (r' := (876611245288137 / 500000000000000 : ℚ))
        (U := (-(1031048553524197032573 / 1250000000000000000000 : ℚ)))
        (U' := (701819397225802967427 / 1250000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (229970650849 / 500000000000 : ℚ))
      (s := (438065595391137 / 1000000000000000 : ℚ))
      (q := (876611245288137 / 2000000000000000 : ℚ))
      (U := (-(1031048553524197032573 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_435_5 :
    Uω (aρ 5) (bρ 5) (229970650849 / 500000000000 : ℝ) ≤
      (-(8530771662286591006543 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8522034528893589 / 20000000000000000 : ℝ) ≤
      (-(8530771662286591006543 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8522034528893589 / 20000000000000000 : ℚ))
        (r' := (8522034528893589 / 5000000000000000 : ℚ))
        (U := (-(8530771662286591006543 / 10000000000000000000000 : ℚ)))
        (U' := (5332171943713408993457 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (229970650849 / 500000000000 : ℚ))
      (s := (4254767949258589 / 10000000000000000 : ℚ))
      (q := (8522034528893589 / 20000000000000000 : ℚ))
      (U := (-(8530771662286591006543 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_435_6 :
    Uω (aρ 6) (bρ 6) (229970650849 / 500000000000 : ℝ) ≤
      (-(8952621060125969732773 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1021251284886079 / 2500000000000000 : ℝ) ≤
      (-(8952621060125969732773 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1021251284886079 / 2500000000000000 : ℚ))
        (r' := (1021251284886079 / 625000000000000 : ℚ))
        (U := (-(8952621060125969732773 / 10000000000000000000000 : ℚ)))
        (U' := (4910322545874030267227 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (229970650849 / 500000000000 : ℚ))
      (s := (127187002331051 / 312500000000000 : ℚ))
      (q := (1021251284886079 / 2500000000000000 : ℚ))
      (U := (-(8952621060125969732773 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_435_7 :
    Uω (aρ 7) (bρ 7) (229970650849 / 500000000000 : ℝ) ≤
      (-(9564311277543446347187 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24016363931063 / 62500000000000 : ℝ) ≤
      (-(9564311277543446347187 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24016363931063 / 62500000000000 : ℚ))
        (r' := (24016363931063 / 15625000000000 : ℚ))
        (U := (-(9564311277543446347187 / 10000000000000000000000 : ℚ)))
        (U' := (4298632328456553652813 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (229970650849 / 500000000000 : ℚ))
      (s := (95221790855129 / 250000000000000 : ℚ))
      (q := (24016363931063 / 62500000000000 : ℚ))
      (U := (-(9564311277543446347187 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_435_8 :
    Uω (aρ 8) (bρ 8) (229970650849 / 500000000000 : ℝ) ≤
      (-(10437864928602727238181 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3521188587841929 / 10000000000000000 : ℝ) ≤
      (-(10437864928602727238181 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3521188587841929 / 10000000000000000 : ℚ))
        (r' := (3521188587841929 / 2500000000000000 : ℚ))
        (U := (-(10437864928602727238181 / 10000000000000000000000 : ℚ)))
        (U' := (3425078677397272761819 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (229970650849 / 500000000000 : ℚ))
      (s := (1724777001644429 / 5000000000000000 : ℚ))
      (q := (3521188587841929 / 10000000000000000 : ℚ))
      (U := (-(10437864928602727238181 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_435_9 :
    Uω (aρ 9) (bρ 9) (229970650849 / 500000000000 : ℝ) ≤
      (-(11692310084797909684141 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1553028512204731 / 5000000000000000 : ℝ) ≤
      (-(11692310084797909684141 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1553028512204731 / 5000000000000000 : ℚ))
        (r' := (1553028512204731 / 1250000000000000 : ℚ))
        (U := (-(11692310084797909684141 / 10000000000000000000000 : ℚ)))
        (U' := (2170633521202090315859 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (229970650849 / 500000000000 : ℚ))
      (s := (740064126195981 / 2500000000000000 : ℚ))
      (q := (1553028512204731 / 5000000000000000 : ℚ))
      (U := (-(11692310084797909684141 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_435_10 :
    Uω (aρ 10) (bρ 10) (229970650849 / 500000000000 : ℝ) ≤
      (-(13584381614807102870191 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2570619527121791 / 10000000000000000 : ℝ) ≤
      (-(13584381614807102870191 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2570619527121791 / 10000000000000000 : ℚ))
        (r' := (2570619527121791 / 2500000000000000 : ℚ))
        (U := (-(13584381614807102870191 / 10000000000000000000000 : ℚ)))
        (U' := (278561991192897129809 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (229970650849 / 500000000000 : ℚ))
      (s := (1138970271851791 / 5000000000000000 : ℚ))
      (q := (2570619527121791 / 10000000000000000 : ℚ))
      (U := (-(13584381614807102870191 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_435_11 :
    Uω (aρ 11) (bρ 11) (229970650849 / 500000000000 : ℝ) ≤
      (-(1714166942718427090193 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (360227406247933 / 2000000000000000 : ℝ) ≤
      (-(1714166942718427090193 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (360227406247933 / 2000000000000000 : ℚ))
        (r' := (360227406247933 / 250000000000000 : ℚ))
        (U := (-(1714166942718427090193 / 1000000000000000000000 : ℚ)))
        (U' := (365274598181572909807 / 1000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (229970650849 / 500000000000 : ℚ))
      (s := (115745217814433 / 1000000000000000 : ℚ))
      (q := (360227406247933 / 2000000000000000 : ℚ))
      (U := (-(1714166942718427090193 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_435_12 :
    Uω (aρ 12) (bρ 12) (229970650849 / 500000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_435_13 :
    Uω (aρ 13) (bρ 13) (229970650849 / 500000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_435_14 :
    Uω (aρ 14) (bρ 14) (229970650849 / 500000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_435_15 :
    Uω (aρ 15) (bρ 15) (229970650849 / 500000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_435_16 :
    Uω (aρ 16) (bρ 16) (229970650849 / 500000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_435 :
    Uρ (229970650849 / 500000000000 : ℝ) ≤
      (-(1170360560847339253183 / 1000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_435_1 U_435_2 U_435_3 U_435_4 U_435_5 U_435_6 U_435_7 U_435_8 U_435_9 U_435_10
    U_435_11 U_435_12 U_435_13 U_435_14 U_435_15 U_435_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
