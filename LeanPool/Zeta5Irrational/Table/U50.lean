/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U50) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_604_1 :
    Uω (aρ 1) (bρ 1) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(185358815803223170541 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6902388154904741 / 10000000000000000 : ℝ) ≤
      (-(185358815803223170541 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6902388154904741 / 10000000000000000 : ℚ))
        (r' := (6902388154904741 / 5000000000000000 : ℚ))
        (U := (-(185358815803223170541 / 500000000000000000000 : ℚ)))
        (U' := (161214774346776829459 / 500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (215698897902601 / 312500000000000 : ℚ))
      (q := (6902388154904741 / 10000000000000000 : ℚ))
      (U := (-(185358815803223170541 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_2 :
    Uω (aρ 2) (bρ 2) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(3741861849853575925477 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6878488326024889 / 10000000000000000 : ℝ) ≤
      (-(3741861849853575925477 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6878488326024889 / 10000000000000000 : ℚ))
        (r' := (6878488326024889 / 5000000000000000 : ℚ))
        (U := (-(3741861849853575925477 / 10000000000000000000000 : ℚ)))
        (U' := (3189609953146424074523 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (859791760954191 / 1250000000000000 : ℚ))
      (q := (6878488326024889 / 10000000000000000 : ℚ))
      (U := (-(3741861849853575925477 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_3 :
    Uω (aρ 3) (bρ 3) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(762314428217885278549 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13661409853630741 / 20000000000000000 : ℝ) ≤
      (-(762314428217885278549 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13661409853630741 / 20000000000000000 : ℚ))
        (r' := (13661409853630741 / 10000000000000000 : ℚ))
        (U := (-(762314428217885278549 / 2000000000000000000000 : ℚ)))
        (U' := (623979932382114721451 / 2000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (6830163395564491 / 10000000000000000 : ℚ))
      (q := (13661409853630741 / 20000000000000000 : ℚ))
      (U := (-(762314428217885278549 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_4 :
    Uω (aρ 4) (bρ 4) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(392836090377941199433 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6751394001858091 / 10000000000000000 : ℝ) ≤
      (-(392836090377941199433 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6751394001858091 / 10000000000000000 : ℚ))
        (r' := (6751394001858091 / 5000000000000000 : ℚ))
        (U := (-(392836090377941199433 / 1000000000000000000000 : ℚ)))
        (U' := (300311089922058800567 / 1000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (1687458931678733 / 2500000000000000 : ℚ))
      (q := (6751394001858091 / 10000000000000000 : ℚ))
      (U := (-(392836090377941199433 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_5 :
    Uω (aρ 5) (bρ 5) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(2054338537821379043431 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13261492907724353 / 20000000000000000 : ℝ) ≤
      (-(2054338537821379043431 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13261492907724353 / 20000000000000000 : ℚ))
        (r' := (13261492907724353 / 10000000000000000 : ℚ))
        (U := (-(2054338537821379043431 / 5000000000000000000000 : ℚ)))
        (U' := (1411397363678620956569 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (6626730550058103 / 10000000000000000 : ℚ))
      (q := (13261492907724353 / 20000000000000000 : ℚ))
      (U := (-(2054338537821379043431 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_6 :
    Uω (aρ 6) (bρ 6) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(1093155636640941648659 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12916040888783747 / 20000000000000000 : ℝ) ≤
      (-(1093155636640941648659 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12916040888783747 / 20000000000000000 : ℚ))
        (r' := (12916040888783747 / 10000000000000000 : ℚ))
        (U := (-(1093155636640941648659 / 2500000000000000000000 : ℚ)))
        (U' := (639712314109058351341 / 2500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (6448518906257497 / 10000000000000000 : ℚ))
      (q := (12916040888783747 / 20000000000000000 : ℚ))
      (U := (-(1093155636640941648659 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_7 :
    Uω (aρ 7) (bρ 7) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(948658707005702538837 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12446045224417483 / 20000000000000000 : ℝ) ≤
      (-(948658707005702538837 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12446045224417483 / 20000000000000000 : ℚ))
        (r' := (12446045224417483 / 10000000000000000 : ℚ))
        (U := (-(948658707005702538837 / 2000000000000000000000 : ℚ)))
        (U' := (437635653594297461163 / 2000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (6202184622651233 / 10000000000000000 : ℚ))
      (q := (12446045224417483 / 20000000000000000 : ℚ))
      (U := (-(948658707005702538837 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_8 :
    Uω (aρ 8) (bρ 8) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(5246381739293769484407 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5917694430933567 / 10000000000000000 : ℝ) ≤
      (-(5246381739293769484407 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5917694430933567 / 10000000000000000 : ℚ))
        (r' := (5917694430933567 / 5000000000000000 : ℚ))
        (U := (-(5246381739293769484407 / 10000000000000000000000 : ℚ)))
        (U' := (1685090063706230515593 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (1468767477860221 / 2500000000000000 : ℚ))
      (q := (5917694430933567 / 10000000000000000 : ℚ))
      (U := (-(5246381739293769484407 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_9 :
    Uω (aρ 9) (bρ 9) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(591028782044301194203 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11075145917614141 / 20000000000000000 : ℝ) ≤
      (-(591028782044301194203 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11075145917614141 / 20000000000000000 : ℚ))
        (r' := (11075145917614141 / 10000000000000000 : ℚ))
        (U := (-(591028782044301194203 / 1000000000000000000000 : ℚ)))
        (U' := (102118398255698805797 / 1000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (5455792595547891 / 10000000000000000 : ℚ))
      (q := (11075145917614141 / 20000000000000000 : ℚ))
      (U := (-(591028782044301194203 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_10 :
    Uω (aρ 10) (bρ 10) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(6767284209621708981663 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10165542878878319 / 20000000000000000 : ℝ) ≤
      (-(6767284209621708981663 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10165542878878319 / 20000000000000000 : ℚ))
        (r' := (10165542878878319 / 10000000000000000 : ℚ))
        (U := (-(6767284209621708981663 / 10000000000000000000000 : ℚ)))
        (U' := (164187593378291018337 / 10000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (4934748590307069 / 10000000000000000 : ℚ))
      (q := (10165542878878319 / 20000000000000000 : ℚ))
      (U := (-(6767284209621708981663 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_11 :
    Uω (aρ 11) (bρ 11) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(1964276446295185408741 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4557957078120433 / 10000000000000000 : ℝ) ≤
      (-(1964276446295185408741 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4557957078120433 / 10000000000000000 : ℚ))
        (r' := (4557957078120433 / 2500000000000000 : ℚ))
        (U := (-(1964276446295185408741 / 2500000000000000000000 : ℚ)))
        (U' := (1501459455204814591259 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (537949561734327 / 1250000000000000 : ℚ))
      (q := (4557957078120433 / 10000000000000000 : ℚ))
      (U := (-(1964276446295185408741 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_12 :
    Uω (aρ 12) (bρ 12) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(9237298431489610316859 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1588141583857573 / 4000000000000000 : ℝ) ≤
      (-(9237298431489610316859 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1588141583857573 / 4000000000000000 : ℚ))
        (r' := (1588141583857573 / 1000000000000000 : ℚ))
        (U := (-(9237298431489610316859 / 10000000000000000000000 : ℚ)))
        (U' := (4625645174510389683141 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (710418070721323 / 2000000000000000 : ℚ))
      (q := (1588141583857573 / 4000000000000000 : ℚ))
      (U := (-(9237298431489610316859 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_13 :
    Uω (aρ 13) (bρ 13) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(440752782161147218229 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6644904481908243 / 20000000000000000 : ℝ) ≤
      (-(440752782161147218229 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6644904481908243 / 20000000000000000 : ℚ))
        (r' := (6644904481908243 / 5000000000000000 : ℚ))
        (U := (-(440752782161147218229 / 400000000000000000000 : ℚ)))
        (U' := (113764962078852781771 / 400000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (2655668657821993 / 10000000000000000 : ℚ))
      (q := (6644904481908243 / 20000000000000000 : ℚ))
      (U := (-(440752782161147218229 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_14 :
    Uω (aρ 14) (bρ 14) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(13569695675472187431089 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1029758998734929 / 4000000000000000 : ℝ) ≤
      (-(13569695675472187431089 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1029758998734929 / 4000000000000000 : ℚ))
        (r' := (1029758998734929 / 1000000000000000 : ℚ))
        (U := (-(13569695675472187431089 / 10000000000000000000000 : ℚ)))
        (U' := (293247930527812568911 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (5573527036009 / 8000000000000 : ℚ))
      (s := (300697290926679 / 2000000000000000 : ℚ))
      (q := (1029758998734929 / 4000000000000000 : ℚ))
      (U := (-(13569695675472187431089 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_604_15 :
    Uω (aρ 15) (bρ 15) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_604_16 :
    Uω (aρ 16) (bρ 16) (5573527036009 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_604 :
    Uρ (5573527036009 / 8000000000000 : ℝ) ≤
      (-(392603247597578016043 / 625000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_604_1 U_604_2 U_604_3 U_604_4 U_604_5 U_604_6 U_604_7 U_604_8 U_604_9 U_604_10
    U_604_11 U_604_12 U_604_13 U_604_14 U_604_15 U_604_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_605_1 :
    Uω (aρ 1) (bρ 1) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(3683697828136284471879 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27674451831362653 / 40000000000000000 : ℝ) ≤
      (-(3683697828136284471879 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27674451831362653 / 40000000000000000 : ℚ))
        (r' := (27674451831362653 / 20000000000000000 : ℚ))
        (U := (-(3683697828136284471879 / 10000000000000000000000 : ℚ)))
        (U' := (3247773974863715528121 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (3459294795373007 / 5000000000000000 : ℚ))
      (q := (27674451831362653 / 40000000000000000 : ℚ))
      (U := (-(3683697828136284471879 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_2 :
    Uω (aρ 2) (bρ 2) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(743660286677977302009 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27578853747993111 / 40000000000000000 : ℝ) ≤
      (-(743660286677977302009 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27578853747993111 / 40000000000000000 : ℚ))
        (r' := (27578853747993111 / 20000000000000000 : ℚ))
        (U := (-(743660286677977302009 / 2000000000000000000000 : ℚ)))
        (U' := (642634073922022697991 / 2000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (6894559561571243 / 10000000000000000 : ℚ))
      (q := (27578853747993111 / 40000000000000000 : ℚ))
      (U := (-(743660286677977302009 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_3 :
    Uω (aρ 3) (bρ 3) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(236740360101894332047 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27387723832635927 / 40000000000000000 : ℝ) ≤
      (-(236740360101894332047 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27387723832635927 / 40000000000000000 : ℚ))
        (r' := (27387723832635927 / 20000000000000000 : ℚ))
        (U := (-(236740360101894332047 / 625000000000000000000 : ℚ)))
        (U' := (196476627585605667953 / 625000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (6846390710242651 / 10000000000000000 : ℚ))
      (q := (27387723832635927 / 40000000000000000 : ℚ))
      (U := (-(236740360101894332047 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_4 :
    Uω (aρ 4) (bρ 4) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(488044063950332874121 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27070489946191399 / 40000000000000000 : ℝ) ≤
      (-(488044063950332874121 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27070489946191399 / 40000000000000000 : ℚ))
        (r' := (27070489946191399 / 20000000000000000 : ℚ))
        (U := (-(488044063950332874121 / 1250000000000000000000 : ℚ)))
        (U' := (378389911424667125879 / 1250000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (6766067948085387 / 10000000000000000 : ℚ))
      (q := (27070489946191399 / 40000000000000000 : ℚ))
      (U := (-(488044063950332874121 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_5 :
    Uω (aρ 5) (bρ 5) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(1021055811405140322069 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26587924041186297 / 40000000000000000 : ℝ) ≤
      (-(1021055811405140322069 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26587924041186297 / 40000000000000000 : ℚ))
        (r' := (26587924041186297 / 20000000000000000 : ℚ))
        (U := (-(1021055811405140322069 / 2500000000000000000000 : ℚ)))
        (U' := (711812139344859677931 / 2500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (1660743728729459 / 2500000000000000 : ℚ))
      (q := (26587924041186297 / 40000000000000000 : ℚ))
      (U := (-(1021055811405140322069 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_6 :
    Uω (aρ 6) (bρ 6) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(4347493813142281048483 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25897076154356201 / 40000000000000000 : ℝ) ≤
      (-(4347493813142281048483 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25897076154356201 / 40000000000000000 : ℚ))
        (r' := (25897076154356201 / 20000000000000000 : ℚ))
        (U := (-(4347493813142281048483 / 10000000000000000000000 : ℚ)))
        (U' := (2583977989857718951517 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (1616197836660697 / 2500000000000000 : ℚ))
      (q := (25897076154356201 / 40000000000000000 : ℚ))
      (U := (-(4347493813142281048483 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_7 :
    Uω (aρ 7) (bρ 7) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(235858409498393209151 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24957206916533209 / 40000000000000000 : ℝ) ≤
      (-(235858409498393209151 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24957206916533209 / 40000000000000000 : ℚ))
        (r' := (24957206916533209 / 20000000000000000 : ℚ))
        (U := (-(235858409498393209151 / 500000000000000000000 : ℚ)))
        (U' := (110715180651606790849 / 500000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (1554629527122823 / 2500000000000000 : ℚ))
      (q := (24957206916533209 / 40000000000000000 : ℚ))
      (U := (-(235858409498393209151 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_8 :
    Uω (aρ 8) (bρ 8) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(5218804088661256319739 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23736146261667077 / 40000000000000000 : ℝ) ≤
      (-(5218804088661256319739 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23736146261667077 / 40000000000000000 : ℚ))
        (r' := (23736146261667077 / 20000000000000000 : ℚ))
        (U := (-(5218804088661256319739 / 10000000000000000000000 : ℚ)))
        (U' := (1712667714338743680261 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (2945764716199113 / 5000000000000000 : ℚ))
      (q := (23736146261667077 / 40000000000000000 : ℚ))
      (U := (-(5218804088661256319739 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_9 :
    Uω (aρ 9) (bρ 9) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(1470148674486619797487 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22216160712343729 / 40000000000000000 : ℝ) ≤
      (-(1470148674486619797487 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (22216160712343729 / 40000000000000000 : ℚ))
        (r' := (22216160712343729 / 20000000000000000 : ℚ))
        (U := (-(1470148674486619797487 / 2500000000000000000000 : ℚ)))
        (U' := (262719276263380202513 / 2500000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (684062785762069 / 1250000000000000 : ℚ))
      (q := (22216160712343729 / 40000000000000000 : ℚ))
      (U := (-(1470148674486619797487 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_10 :
    Uω (aρ 10) (bρ 10) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(3367231395774420070013 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20397924892066461 / 40000000000000000 : ℝ) ≤
      (-(3367231395774420070013 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20397924892066461 / 40000000000000000 : ℚ))
        (r' := (20397924892066461 / 20000000000000000 : ℚ))
        (U := (-(3367231395774420070013 / 5000000000000000000000 : ℚ)))
        (U' := (98504505725579929987 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (2475971704726459 / 5000000000000000 : ℚ))
      (q := (20397924892066461 / 40000000000000000 : ℚ))
      (U := (-(3367231395774420070013 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_11 :
    Uω (aρ 11) (bρ 11) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(977435570934079413611 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18300547855289677 / 40000000000000000 : ℝ) ≤
      (-(977435570934079413611 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18300547855289677 / 40000000000000000 : ℚ))
        (r' := (18300547855289677 / 10000000000000000 : ℚ))
        (U := (-(977435570934079413611 / 1250000000000000000000 : ℚ)))
        (U' := (755432379815920586389 / 1250000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (2160865758634763 / 5000000000000000 : ℚ))
      (q := (18300547855289677 / 40000000000000000 : ℚ))
      (U := (-(977435570934079413611 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_12 :
    Uω (aρ 12) (bρ 12) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(4595875065596004995123 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15953917980471991 / 40000000000000000 : ℝ) ≤
      (-(4595875065596004995123 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (15953917980471991 / 40000000000000000 : ℚ))
        (r' := (15953917980471991 / 10000000000000000 : ℚ))
        (U := (-(4595875065596004995123 / 5000000000000000000000 : ℚ)))
        (U' := (2335596737403995004877 / 5000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (3572116676545683 / 10000000000000000 : ℚ))
      (q := (15953917980471991 / 40000000000000000 : ℚ))
      (U := (-(4595875065596004995123 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_13 :
    Uω (aρ 13) (bρ 13) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(10958002953060884909373 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2674175867206639 / 8000000000000000 : ℝ) ≤
      (-(10958002953060884909373 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2674175867206639 / 8000000000000000 : ℚ))
        (r' := (2674175867206639 / 2000000000000000 : ℚ))
        (U := (-(10958002953060884909373 / 10000000000000000000000 : ℚ)))
        (U' := (2904940652939115090627 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (535995819184257 / 2000000000000000 : ℚ))
      (q := (2674175867206639 / 8000000000000000 : ℚ))
      (U := (-(10958002953060884909373 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_14 :
    Uω (aρ 14) (bρ 14) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(6731579740574347026997 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10407883059168421 / 40000000000000000 : ℝ) ≤
      (-(6731579740574347026997 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10407883059168421 / 40000000000000000 : ℚ))
        (r' := (10407883059168421 / 10000000000000000 : ℚ))
        (U := (-(6731579740574347026997 / 5000000000000000000000 : ℚ)))
        (U' := (199892062425652973003 / 5000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (4469205467533 / 6400000000000 : ℚ))
      (s := (771204121266949 / 5000000000000000 : ℚ))
      (q := (10407883059168421 / 40000000000000000 : ℚ))
      (U := (-(6731579740574347026997 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_605_15 :
    Uω (aρ 15) (bρ 15) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_605_16 :
    Uω (aρ 16) (bρ 16) (4469205467533 / 6400000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_605 :
    Uρ (4469205467533 / 6400000000000 : ℝ) ≤
      (-(781257351911533191943 / 1250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_605_1 U_605_2 U_605_3 U_605_4 U_605_5 U_605_6 U_605_7 U_605_8 U_605_9 U_605_10
    U_605_11 U_605_12 U_605_13 U_605_14 U_605_15 U_605_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_606_1 :
    Uω (aρ 1) (bρ 1) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(36602743354238826769 / 100000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (693483776051957 / 1000000000000000 : ℝ) ≤
      (-(36602743354238826769 / 100000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (693483776051957 / 1000000000000000 : ℚ))
        (r' := (693483776051957 / 500000000000000 : ℚ))
        (U := (-(36602743354238826769 / 100000000000000000000 : ℚ)))
        (U' := (32711974675761173231 / 100000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (1386962889618953 / 2000000000000000 : ℚ))
      (q := (693483776051957 / 1000000000000000 : ℚ))
      (U := (-(36602743354238826769 / 100000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_2 :
    Uω (aρ 2) (bρ 2) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(1847398199132677266083 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3455469273133667 / 5000000000000000 : ℝ) ≤
      (-(1847398199132677266083 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3455469273133667 / 5000000000000000 : ℚ))
        (r' := (3455469273133667 / 2500000000000000 : ℚ))
        (U := (-(1847398199132677266083 / 5000000000000000000000 : ℚ)))
        (U' := (1618337702367322733917 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (6910785032100293 / 10000000000000000 : ℚ))
      (q := (3455469273133667 / 5000000000000000 : ℚ))
      (U := (-(1847398199132677266083 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_3 :
    Uω (aρ 3) (bρ 3) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(47052194398732723493 / 125000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6863156983433939 / 10000000000000000 : ℝ) ≤
      (-(47052194398732723493 / 125000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6863156983433939 / 10000000000000000 : ℚ))
        (r' := (6863156983433939 / 5000000000000000 : ℚ))
        (U := (-(47052194398732723493 / 125000000000000000000 : ℚ)))
        (U' := (39591203138767276507 / 125000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (6862618012783503 / 10000000000000000 : ℚ))
      (q := (6863156983433939 / 10000000000000000 : ℚ))
      (U := (-(47052194398732723493 / 125000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_4 :
    Uω (aρ 4) (bρ 4) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(1940200824024491061991 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6783850953355573 / 10000000000000000 : ℝ) ≤
      (-(1940200824024491061991 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6783850953355573 / 10000000000000000 : ℚ))
        (r' := (6783850953355573 / 5000000000000000 : ℚ))
        (U := (-(1940200824024491061991 / 5000000000000000000000 : ℚ)))
        (U' := (1525535077475508938009 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (6782300133691771 / 10000000000000000 : ℚ))
      (q := (6783850953355573 / 10000000000000000 : ℚ))
      (U := (-(1940200824024491061991 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_5 :
    Uω (aρ 5) (bρ 5) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(4059829140506769287007 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13326431037813833 / 20000000000000000 : ℝ) ≤
      (-(4059829140506769287007 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13326431037813833 / 20000000000000000 : ℚ))
        (r' := (13326431037813833 / 10000000000000000 : ℚ))
        (U := (-(4059829140506769287007 / 10000000000000000000000 : ℚ)))
        (U' := (2871642662493230712993 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (3329609592064729 / 5000000000000000 : ℚ))
      (q := (13326431037813833 / 20000000000000000 : ℚ))
      (U := (-(4059829140506769287007 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_6 :
    Uω (aρ 6) (bρ 6) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(2161214125510321744941 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (519241401057381 / 800000000000000 : ℝ) ≤
      (-(2161214125510321744941 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (519241401057381 / 800000000000000 : ℚ))
        (r' := (519241401057381 / 400000000000000 : ℚ))
        (U := (-(2161214125510321744941 / 5000000000000000000000 : ℚ)))
        (U' := (1304521775989678255059 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (129621270957803 / 200000000000000 : ℚ))
      (q := (519241401057381 / 800000000000000 : ℚ))
      (U := (-(2161214125510321744941 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_7 :
    Uω (aρ 7) (bρ 7) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(4691111374317235430867 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12511161124289557 / 20000000000000000 : ℝ) ≤
      (-(4691111374317235430867 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12511161124289557 / 20000000000000000 : ℚ))
        (r' := (12511161124289557 / 10000000000000000 : ℚ))
        (U := (-(4691111374317235430867 / 10000000000000000000000 : ℚ)))
        (U' := (2240360428682764569133 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (3117425513252591 / 5000000000000000 : ℚ))
      (q := (12511161124289557 / 20000000000000000 : ℚ))
      (U := (-(4691111374317235430867 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_8 :
    Uω (aρ 8) (bρ 8) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(2595651686485454946769 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11900756100985221 / 20000000000000000 : ℝ) ≤
      (-(2595651686485454946769 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11900756100985221 / 20000000000000000 : ℚ))
        (r' := (11900756100985221 / 10000000000000000 : ℚ))
        (U := (-(2595651686485454946769 / 5000000000000000000000 : ℚ)))
        (U' := (870084215014545053231 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (2953993827270423 / 5000000000000000 : ℚ))
      (q := (11900756100985221 / 20000000000000000 : ℚ))
      (U := (-(2595651686485454946769 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_9 :
    Uω (aρ 9) (bρ 9) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(5850992094238623056519 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2785252971286799 / 5000000000000000 : ℝ) ≤
      (-(5850992094238623056519 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2785252971286799 / 5000000000000000 : ℚ))
        (r' := (2785252971286799 / 2500000000000000 : ℚ))
        (U := (-(5850992094238623056519 / 10000000000000000000000 : ℚ)))
        (U' := (1080479708761376943481 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (5489209067062821 / 10000000000000000 : ℚ))
      (q := (2785252971286799 / 5000000000000000 : ℚ))
      (U := (-(5850992094238623056519 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_10 :
    Uω (aρ 10) (bρ 10) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(837719390211303050617 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (204647509780861 / 400000000000000 : ℝ) ≤
      (-(837719390211303050617 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (204647509780861 / 400000000000000 : ℚ))
        (r' := (204647509780861 / 200000000000000 : ℚ))
        (U := (-(837719390211303050617 / 1250000000000000000000 : ℚ)))
        (U' := (28714585163696949383 / 1250000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (198765268178147 / 400000000000000 : ℚ))
      (q := (204647509780861 / 400000000000000 : ℚ))
      (U := (-(837719390211303050617 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_11 :
    Uω (aρ 11) (bρ 11) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(7782020821850845249701 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9184618574910929 / 20000000000000000 : ℝ) ≤
      (-(7782020821850845249701 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9184618574910929 / 20000000000000000 : ℚ))
        (r' := (9184618574910929 / 5000000000000000 : ℚ))
        (U := (-(7782020821850845249701 / 10000000000000000000000 : ℚ)))
        (U' := (6080922784149154750299 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (2169925708263277 / 5000000000000000 : ℚ))
      (q := (9184618574910929 / 20000000000000000 : ℚ))
      (U := (-(7782020821850845249701 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_12 :
    Uω (aρ 12) (bρ 12) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(2286614058101796570093 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1602634339274003 / 4000000000000000 : ℝ) ≤
      (-(2286614058101796570093 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1602634339274003 / 4000000000000000 : ℚ))
        (r' := (1602634339274003 / 1000000000000000 : ℚ))
        (U := (-(2286614058101796570093 / 2500000000000000000000 : ℚ)))
        (U' := (1179121843398203429907 / 2500000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (44901307933383 / 125000000000000 : ℚ))
      (q := (1602634339274003 / 4000000000000000 : ℚ))
      (U := (-(2286614058101796570093 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_13 :
    Uω (aρ 13) (bρ 13) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(5448867091589979705297 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6725853653235283 / 20000000000000000 : ℝ) ≤
      (-(5448867091589979705297 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6725853653235283 / 20000000000000000 : ℚ))
        (r' := (6725853653235283 / 5000000000000000 : ℚ))
        (U := (-(5448867091589979705297 / 5000000000000000000000 : ℚ)))
        (U' := (1482604711410020294703 / 5000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (676042083282727 / 2500000000000000 : ℚ))
      (q := (6725853653235283 / 20000000000000000 : ℚ))
      (U := (-(5448867091589979705297 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_14 :
    Uω (aρ 14) (bρ 14) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(13359251881499432432203 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (657287042718211 / 2500000000000000 : ℝ) ≤
      (-(13359251881499432432203 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (657287042718211 / 2500000000000000 : ℚ))
        (r' := (657287042718211 / 625000000000000 : ℚ))
        (U := (-(13359251881499432432203 / 10000000000000000000000 : ℚ)))
        (U' := (503691724500567567797 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (11198973265647 / 16000000000000 : ℚ))
      (s := (1580538306686313 / 10000000000000000 : ℚ))
      (q := (657287042718211 / 2500000000000000 : ℚ))
      (U := (-(13359251881499432432203 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_606_15 :
    Uω (aρ 15) (bρ 15) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_606_16 :
    Uω (aρ 16) (bρ 16) (11198973265647 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_606 :
    Uρ (11198973265647 / 16000000000000 : ℝ) ≤
      (-(1554673099640420038419 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_606_1 U_606_2 U_606_3 U_606_4 U_606_5 U_606_6 U_606_7 U_606_8 U_606_9 U_606_10
    U_606_11 U_606_12 U_606_13 U_606_14 U_606_15 U_606_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_607_1 :
    Uω (aρ 1) (bρ 1) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(727381116177924738757 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27804250251773043 / 40000000000000000 : ℝ) ≤
      (-(727381116177924738757 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27804250251773043 / 40000000000000000 : ℚ))
        (r' := (27804250251773043 / 20000000000000000 : ℚ))
        (U := (-(727381116177924738757 / 2000000000000000000000 : ℚ)))
        (U' := (658913244422075261243 / 2000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (1737759826233271 / 2500000000000000 : ℚ))
      (q := (27804250251773043 / 40000000000000000 : ℚ))
      (U := (-(727381116177924738757 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_2 :
    Uω (aρ 2) (bρ 2) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(1835673242359555576149 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27708654615376139 / 40000000000000000 : ℝ) ≤
      (-(1835673242359555576149 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27708654615376139 / 40000000000000000 : ℚ))
        (r' := (27708654615376139 / 20000000000000000 : ℚ))
        (U := (-(1835673242359555576149 / 5000000000000000000000 : ℚ)))
        (U' := (1630062659140444423851 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (865876312405579 / 1250000000000000 : ℚ))
      (q := (27708654615376139 / 40000000000000000 : ℚ))
      (U := (-(1835673242359555576149 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_3 :
    Uω (aρ 3) (bρ 3) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(748112249305770301769 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27517532010732761 / 40000000000000000 : ℝ) ≤
      (-(748112249305770301769 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27517532010732761 / 40000000000000000 : ℚ))
        (r' := (27517532010732761 / 20000000000000000 : ℚ))
        (U := (-(748112249305770301769 / 2000000000000000000000 : ℚ)))
        (U' := (638182111294229698231 / 2000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (6878845303272943 / 10000000000000000 : ℚ))
      (q := (27517532010732761 / 40000000000000000 : ℚ))
      (U := (-(748112249305770301769 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_4 :
    Uω (aρ 4) (bρ 4) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(3856508037953090883837 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5440063521927477 / 8000000000000000 : ℝ) ≤
      (-(3856508037953090883837 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5440063521927477 / 8000000000000000 : ℚ))
        (r' := (5440063521927477 / 4000000000000000 : ℚ))
        (U := (-(3856508037953090883837 / 10000000000000000000000 : ℚ)))
        (U' := (3074963765046909116163 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (1359706456758051 / 2000000000000000 : ℚ))
      (q := (5440063521927477 / 8000000000000000 : ℚ))
      (U := (-(3856508037953090883837 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_5 :
    Uω (aρ 5) (bρ 5) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(4035494468925474550957 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26717799920169329 / 40000000000000000 : ℝ) ≤
      (-(4035494468925474550957 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26717799920169329 / 40000000000000000 : ℚ))
        (r' := (26717799920169329 / 20000000000000000 : ℚ))
        (U := (-(4035494468925474550957 / 10000000000000000000000 : ℚ)))
        (U' := (2895977334074525449043 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (6675463358391227 / 10000000000000000 : ℚ))
      (q := (26717799920169329 / 40000000000000000 : ℚ))
      (U := (-(4035494468925474550957 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_6 :
    Uω (aρ 6) (bρ 6) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(4297425542463654092731 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26027063476699487 / 40000000000000000 : ℝ) ≤
      (-(4297425542463654092731 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26027063476699487 / 40000000000000000 : ℚ))
        (r' := (26027063476699487 / 20000000000000000 : ℚ))
        (U := (-(4297425542463654092731 / 10000000000000000000000 : ℚ)))
        (U' := (2634046260536345907269 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (3248667755898153 / 5000000000000000 : ℚ))
      (q := (26027063476699487 / 40000000000000000 : ℚ))
      (U := (-(4297425542463654092731 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_7 :
    Uω (aρ 7) (bρ 7) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(466512272714342381551 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25087436453874287 / 40000000000000000 : ℝ) ≤
      (-(466512272714342381551 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25087436453874287 / 40000000000000000 : ℚ))
        (r' := (25087436453874287 / 20000000000000000 : ℚ))
        (U := (-(466512272714342381551 / 1000000000000000000000 : ℚ)))
        (U' := (226634907585657618449 / 1000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (3125591690571853 / 5000000000000000 : ℚ))
      (q := (25087436453874287 / 40000000000000000 : ℚ))
      (U := (-(466512272714342381551 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_8 :
    Uω (aρ 8) (bρ 8) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(1032775831632319691089 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23866875566293157 / 40000000000000000 : ℝ) ≤
      (-(1032775831632319691089 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23866875566293157 / 40000000000000000 : ℚ))
        (r' := (23866875566293157 / 20000000000000000 : ℚ))
        (U := (-(1032775831632319691089 / 2000000000000000000000 : ℚ)))
        (U' := (353518528967680308911 / 2000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (5924444588693141 / 10000000000000000 : ℚ))
      (q := (23866875566293157 / 40000000000000000 : ℚ))
      (U := (-(1032775831632319691089 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_9 :
    Uω (aρ 9) (bρ 9) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(29107397217795261913 / 50000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22347881062052147 / 40000000000000000 : ℝ) ≤
      (-(29107397217795261913 / 50000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (22347881062052147 / 40000000000000000 : ℚ))
        (r' := (22347881062052147 / 20000000000000000 : ℚ))
        (U := (-(29107397217795261913 / 50000000000000000000 : ℚ)))
        (U' := (5549961797204738087 / 50000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (1376478241233159 / 2500000000000000 : ℚ))
      (q := (22347881062052147 / 40000000000000000 : ℚ))
      (U := (-(29107397217795261913 / 50000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_10 :
    Uω (aρ 10) (bρ 10) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(666916037184109468323 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20531564150751633 / 40000000000000000 : ℝ) ≤
      (-(666916037184109468323 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20531564150751633 / 40000000000000000 : ℚ))
        (r' := (20531564150751633 / 20000000000000000 : ℚ))
        (U := (-(666916037184109468323 / 1000000000000000000000 : ℚ)))
        (U' := (26231143115890531677 / 1000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (4986313542777379 / 10000000000000000 : ℚ))
      (q := (20531564150751633 / 40000000000000000 : ℚ))
      (U := (-(666916037184109468323 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_11 :
    Uω (aρ 11) (bρ 11) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(193617827665090779411 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18437896573385211 / 40000000000000000 : ℝ) ≤
      (-(193617827665090779411 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18437896573385211 / 40000000000000000 : ℚ))
        (r' := (18437896573385211 / 10000000000000000 : ℚ))
        (U := (-(193617827665090779411 / 250000000000000000000 : ℚ)))
        (U' := (152955762484909220589 / 250000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (136186136884349 / 312500000000000 : ℚ))
      (q := (18437896573385211 / 40000000000000000 : ℚ))
      (U := (-(193617827665090779411 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_12 :
    Uω (aρ 12) (bρ 12) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(9101413433336903069591 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16098693349171741 / 40000000000000000 : ℝ) ≤
      (-(9101413433336903069591 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16098693349171741 / 40000000000000000 : ℚ))
        (r' := (16098693349171741 / 10000000000000000 : ℚ))
        (U := (-(9101413433336903069591 / 10000000000000000000000 : ℚ)))
        (U' := (4761530172663096930409 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (3612054864877433 / 10000000000000000 : ℚ))
      (q := (16098693349171741 / 40000000000000000 : ℚ))
      (U := (-(9101413433336903069591 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_13 :
    Uω (aρ 13) (bρ 13) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(2709500208247898408319 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13532299322712177 / 40000000000000000 : ℝ) ≤
      (-(2709500208247898408319 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13532299322712177 / 40000000000000000 : ℚ))
        (r' := (13532299322712177 / 10000000000000000 : ℚ))
        (U := (-(2709500208247898408319 / 2500000000000000000000 : ℚ)))
        (U' := (756235693252101591681 / 2500000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (2728239593242651 / 10000000000000000 : ℚ))
      (q := (13532299322712177 / 40000000000000000 : ℚ))
      (U := (-(2709500208247898408319 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_14 :
    Uω (aρ 14) (bρ 14) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(1325779785845717507177 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10623830814298537 / 40000000000000000 : ℝ) ≤
      (-(1325779785845717507177 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10623830814298537 / 40000000000000000 : ℚ))
        (r' := (10623830814298537 / 10000000000000000 : ℚ))
        (U := (-(1325779785845717507177 / 1000000000000000000000 : ℚ)))
        (U' := (60514574754282492823 / 1000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (22449865724923 / 32000000000000 : ℚ))
      (s := (1617932624080831 / 10000000000000000 : ℚ))
      (q := (10623830814298537 / 40000000000000000 : ℚ))
      (U := (-(1325779785845717507177 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_607_15 :
    Uω (aρ 15) (bρ 15) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_607_16 :
    Uω (aρ 16) (bρ 16) (22449865724923 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_607 :
    Uρ (22449865724923 / 32000000000000 : ℝ) ≤
      (-(6187543587831002428899 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_607_1 U_607_2 U_607_3 U_607_4 U_607_5 U_607_6 U_607_7 U_607_8 U_607_9 U_607_10
    U_607_11 U_607_12 U_607_13 U_607_14 U_607_15 U_607_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_608_1 :
    Uω (aρ 1) (bρ 1) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(3613591309293704288903 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6967287365113519 / 10000000000000000 : ℝ) ≤
      (-(3613591309293704288903 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6967287365113519 / 10000000000000000 : ℚ))
        (r' := (6967287365113519 / 5000000000000000 : ℚ))
        (U := (-(3613591309293704288903 / 10000000000000000000000 : ℚ)))
        (U' := (3317880493706295711097 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (3483632080632269 / 5000000000000000 : ℚ))
      (q := (6967287365113519 / 10000000000000000 : ℚ))
      (U := (-(3613591309293704288903 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_2 :
    Uω (aρ 2) (bρ 2) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(1823975717406834395501 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13886777519480489 / 20000000000000000 : ℝ) ≤
      (-(1823975717406834395501 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13886777519480489 / 20000000000000000 : ℚ))
        (r' := (13886777519480489 / 10000000000000000 : ℚ))
        (U := (-(1823975717406834395501 / 5000000000000000000000 : ℚ)))
        (U' := (1641760184093165604499 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (6943235963027989 / 10000000000000000 : ℚ))
      (q := (13886777519480489 / 20000000000000000 : ℚ))
      (U := (-(1823975717406834395501 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_3 :
    Uω (aρ 3) (bρ 3) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(29039082672124137669 / 78125000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43097556349683 / 62500000000000 : ℝ) ≤
      (-(29039082672124137669 / 78125000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43097556349683 / 62500000000000 : ℚ))
        (r' := (43097556349683 / 31250000000000 : ℚ))
        (U := (-(29039082672124137669 / 78125000000000000000 : ℚ)))
        (U' := (25113040788813362331 / 78125000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (344753629089803 / 500000000000000 : ℚ))
      (q := (43097556349683 / 62500000000000 : ℚ))
      (U := (-(29039082672124137669 / 78125000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_4 :
    Uω (aρ 4) (bρ 4) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(479083926015013648739 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13632615667672069 / 20000000000000000 : ℝ) ≤
      (-(479083926015013648739 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13632615667672069 / 20000000000000000 : ℚ))
        (r' := (13632615667672069 / 10000000000000000 : ℚ))
        (U := (-(479083926015013648739 / 1250000000000000000000 : ℚ)))
        (U' := (387350049359986351261 / 1250000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (6814764398634569 / 10000000000000000 : ℚ))
      (q := (13632615667672069 / 20000000000000000 : ℚ))
      (U := (-(479083926015013648739 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_5 :
    Uω (aρ 5) (bρ 5) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(2005609470815187270507 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (83696054925607 / 125000000000000 : ℝ) ≤
      (-(2005609470815187270507 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (83696054925607 / 125000000000000 : ℚ))
        (r' := (83696054925607 / 62500000000000 : ℚ))
        (U := (-(2005609470815187270507 / 5000000000000000000000 : ℚ)))
        (U' := (1460126430684812729493 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (334585371919731 / 500000000000000 : ℚ))
      (q := (83696054925607 / 125000000000000 : ℚ))
      (U := (-(2005609470815187270507 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_6 :
    Uω (aρ 6) (bρ 6) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(4272485372134123980927 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13046028214702497 / 20000000000000000 : ℝ) ≤
      (-(4272485372134123980927 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13046028214702497 / 20000000000000000 : ℚ))
        (r' := (13046028214702497 / 10000000000000000 : ℚ))
        (U := (-(4272485372134123980927 / 10000000000000000000000 : ℚ)))
        (U' := (2658986430865876019073 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (6513607240139997 / 10000000000000000 : ℚ))
      (q := (13046028214702497 / 20000000000000000 : ℚ))
      (U := (-(4272485372134123980927 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_7 :
    Uω (aρ 7) (bρ 7) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(4639201890375419235181 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6288137385306809 / 10000000000000000 : ℝ) ≤
      (-(4639201890375419235181 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6288137385306809 / 10000000000000000 : ℚ))
        (r' := (6288137385306809 / 5000000000000000 : ℚ))
        (U := (-(4639201890375419235181 / 10000000000000000000000 : ℚ)))
        (U' := (2292269912624580764819 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (3133757588405559 / 5000000000000000 : ℚ))
      (q := (6288137385306809 / 10000000000000000 : ℚ))
      (U := (-(4639201890375419235181 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_8 :
    Uω (aρ 8) (bρ 8) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(1027306202776836780947 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11966118188021229 / 20000000000000000 : ℝ) ≤
      (-(1027306202776836780947 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11966118188021229 / 20000000000000000 : ℚ))
        (r' := (11966118188021229 / 10000000000000000 : ℚ))
        (U := (-(1027306202776836780947 / 2000000000000000000000 : ℚ)))
        (U' := (358988157823163219053 / 2000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (5940900245558729 / 10000000000000000 : ℚ))
      (q := (11966118188021229 / 20000000000000000 : ℚ))
      (U := (-(1027306202776836780947 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_9 :
    Uω (aρ 9) (bρ 9) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(579205618557146584257 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2801716579992363 / 5000000000000000 : ℝ) ≤
      (-(579205618557146584257 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2801716579992363 / 5000000000000000 : ℚ))
        (r' := (2801716579992363 / 2500000000000000 : ℚ))
        (U := (-(579205618557146584257 / 1000000000000000000000 : ℚ)))
        (U' := (113941561742853415743 / 1000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (690326750733369 / 1250000000000000 : ℚ))
      (q := (2801716579992363 / 5000000000000000 : ℚ))
      (U := (-(579205618557146584257 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_10 :
    Uω (aρ 10) (bρ 10) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(3318338861609870053377 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (643698891971729 / 1250000000000000 : ℝ) ≤
      (-(3318338861609870053377 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (643698891971729 / 1250000000000000 : ℚ))
        (r' := (643698891971729 / 625000000000000 : ℚ))
        (U := (-(3318338861609870053377 / 5000000000000000000000 : ℚ)))
        (U' := (147397039890129946623 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (1250872247735041 / 2500000000000000 : ℚ))
      (q := (643698891971729 / 1250000000000000 : ℚ))
      (U := (-(3318338861609870053377 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_11 :
    Uω (aρ 11) (bρ 11) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(481722500072513733311 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9253263248367061 / 20000000000000000 : ℝ) ≤
      (-(481722500072513733311 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9253263248367061 / 20000000000000000 : ℚ))
        (r' := (9253263248367061 / 5000000000000000 : ℚ))
        (U := (-(481722500072513733311 / 625000000000000000000 : ℚ)))
        (U' := (384711475302486266689 / 625000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (4376046593964561 / 10000000000000000 : ℚ))
      (q := (9253263248367061 / 20000000000000000 : ℚ))
      (U := (-(481722500072513733311 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_12 :
    Uω (aρ 12) (bρ 12) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(4528309251245035771429 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8085484546596681 / 20000000000000000 : ℝ) ≤
      (-(4528309251245035771429 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8085484546596681 / 20000000000000000 : ℚ))
        (r' := (8085484546596681 / 5000000000000000 : ℚ))
        (U := (-(4528309251245035771429 / 5000000000000000000000 : ℚ)))
        (U' := (2403162551754964228571 / 5000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (3631967988879181 / 10000000000000000 : ℚ))
      (q := (8085484546596681 / 20000000000000000 : ℚ))
      (U := (-(4528309251245035771429 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_13 :
    Uω (aρ 13) (bρ 13) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(538939547868169931167 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3403165393967557 / 10000000000000000 : ℝ) ≤
      (-(538939547868169931167 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3403165393967557 / 10000000000000000 : ℚ))
        (r' := (3403165393967557 / 2500000000000000 : ℚ))
        (U := (-(538939547868169931167 / 500000000000000000000 : ℚ)))
        (U' := (154207632431830068833 / 500000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (1376097985906307 / 5000000000000000 : ℚ))
      (q := (3403165393967557 / 10000000000000000 : ℚ))
      (U := (-(538939547868169931167 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_14 :
    Uω (aρ 14) (bρ 14) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(13158641155386919367299 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (536484860941541 / 2000000000000000 : ℝ) ≤
      (-(13158641155386919367299 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (536484860941541 / 2000000000000000 : ℚ))
        (r' := (536484860941541 / 500000000000000 : ℚ))
        (U := (-(13158641155386919367299 / 10000000000000000000000 : ℚ)))
        (U' := (704302450613080632701 / 10000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (2812723114819 / 4000000000000 : ℚ))
      (s := (165464107833791 / 1000000000000000 : ℚ))
      (q := (536484860941541 / 2000000000000000 : ℚ))
      (U := (-(13158641155386919367299 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_608_15 :
    Uω (aρ 15) (bρ 15) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_608_16 :
    Uω (aρ 16) (bρ 16) (2812723114819 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_608 :
    Uρ (2812723114819 / 4000000000000 : ℝ) ≤
      (-(6156604129477609587247 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_608_1 U_608_2 U_608_3 U_608_4 U_608_5 U_608_6 U_608_7 U_608_8 U_608_9 U_608_10
    U_608_11 U_608_12 U_608_13 U_608_14 U_608_15 U_608_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_609_1 :
    Uω (aρ 1) (bρ 1) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(718066253435485445603 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27934048668128443 / 40000000000000000 : ℝ) ≤
      (-(718066253435485445603 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27934048668128443 / 40000000000000000 : ℚ))
        (r' := (27934048668128443 / 20000000000000000 : ℚ))
        (U := (-(718066253435485445603 / 2000000000000000000000 : ℚ)))
        (U' := (668228107164514554397 / 2000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (6983489017092659 / 10000000000000000 : ℚ))
      (q := (27934048668128443 / 40000000000000000 : ℚ))
      (U := (-(718066253435485445603 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_2 :
    Uω (aρ 2) (bρ 2) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(1812305496208947558473 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5567691091174173 / 8000000000000000 : ℝ) ≤
      (-(1812305496208947558473 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5567691091174173 / 8000000000000000 : ℚ))
        (r' := (5567691091174173 / 4000000000000000 : ℚ))
        (U := (-(1812305496208947558473 / 5000000000000000000000 : ℚ)))
        (U' := (1653430405291052441527 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (695946142347387 / 1000000000000000 : ℚ))
      (q := (5567691091174173 / 8000000000000000 : ℚ))
      (U := (-(1812305496208947558473 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_3 :
    Uω (aρ 3) (bρ 3) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(1846749648388671706299 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27647340093097407 / 40000000000000000 : ℝ) ≤
      (-(1846749648388671706299 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27647340093097407 / 40000000000000000 : ℚ))
        (r' := (27647340093097407 / 20000000000000000 : ℚ))
        (U := (-(1846749648388671706299 / 5000000000000000000000 : ℚ)))
        (U' := (1618986253111328293701 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (6911299848437141 / 10000000000000000 : ℚ))
      (q := (27647340093097407 / 40000000000000000 : ℚ))
      (U := (-(1846749648388671706299 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_4 :
    Uω (aρ 4) (bρ 4) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(119027858978336842039 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27330144991045187 / 40000000000000000 : ℝ) ≤
      (-(119027858978336842039 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27330144991045187 / 40000000000000000 : ℚ))
        (r' := (27330144991045187 / 20000000000000000 : ℚ))
        (U := (-(119027858978336842039 / 312500000000000000000 : ℚ)))
        (U' := (97580634865413157961 / 312500000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (6830996478476031 / 10000000000000000 : ℚ))
      (q := (27330144991045187 / 40000000000000000 : ℚ))
      (U := (-(119027858978336842039 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_5 :
    Uω (aρ 5) (bρ 5) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(797400454296810172779 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26847675045071939 / 40000000000000000 : ℝ) ≤
      (-(797400454296810172779 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26847675045071939 / 40000000000000000 : ℚ))
        (r' := (26847675045071939 / 20000000000000000 : ℚ))
        (U := (-(797400454296810172779 / 2000000000000000000000 : ℚ)))
        (U' := (588893906303189827221 / 2000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (6707951424824407 / 10000000000000000 : ℚ))
      (q := (26847675045071939 / 40000000000000000 : ℚ))
      (U := (-(797400454296810172779 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_6 :
    Uω (aρ 6) (bρ 6) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(212380371353436732361 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5231409782901509 / 8000000000000000 : ℝ) ≤
      (-(212380371353436732361 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5231409782901509 / 8000000000000000 : ℚ))
        (r' := (5231409782901509 / 4000000000000000 : ℚ))
        (U := (-(212380371353436732361 / 500000000000000000000 : ℚ)))
        (U' := (134193218796563267639 / 500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (652987873468221 / 1000000000000000 : ℚ))
      (q := (5231409782901509 / 8000000000000000 : ℚ))
      (U := (-(212380371353436732361 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_7 :
    Uω (aρ 7) (bρ 7) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(2306674254387015104923 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25217661519354599 / 40000000000000000 : ℝ) ≤
      (-(2306674254387015104923 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25217661519354599 / 40000000000000000 : ℚ))
        (r' := (25217661519354599 / 20000000000000000 : ℚ))
        (U := (-(2306674254387015104923 / 5000000000000000000000 : ℚ)))
        (U' := (1159061647112984895077 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (6283846417865737 / 10000000000000000 : ℚ))
      (q := (25217661519354599 / 40000000000000000 : ℚ))
      (U := (-(2306674254387015104923 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_8 :
    Uω (aρ 8) (bρ 8) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(5109258513458795500777 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23997594652387391 / 40000000000000000 : ℝ) ≤
      (-(5109258513458795500777 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23997594652387391 / 40000000000000000 : ℚ))
        (r' := (23997594652387391 / 20000000000000000 : ℚ))
        (U := (-(5109258513458795500777 / 10000000000000000000000 : ℚ)))
        (U' := (1822213289541204499223 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (5957354635722133 / 10000000000000000 : ℚ))
      (q := (23997594652387391 / 40000000000000000 : ℚ))
      (U := (-(5109258513458795500777 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_9 :
    Uω (aρ 9) (bρ 9) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(720340220661621150801 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22479578555636669 / 40000000000000000 : ℝ) ≤
      (-(720340220661621150801 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (22479578555636669 / 40000000000000000 : ℚ))
        (r' := (22479578555636669 / 20000000000000000 : ℚ))
        (U := (-(720340220661621150801 / 1250000000000000000000 : ℚ)))
        (U' := (146093754713378849199 / 1250000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (1384828053926693 / 2500000000000000 : ℚ))
      (q := (22479578555636669 / 40000000000000000 : ℚ))
      (U := (-(720340220661621150801 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_10 :
    Uω (aρ 10) (bρ 10) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(1651076591580467623333 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (826606091451197 / 1600000000000000 : ℝ) ≤
      (-(1651076591580467623333 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (826606091451197 / 1600000000000000 : ℚ))
        (r' := (826606091451197 / 800000000000000 : ℚ))
        (U := (-(1651076591580467623333 / 2500000000000000000000 : ℚ)))
        (U' := (81791359169532376667 / 2500000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (25103290572617 / 50000000000000 : ℚ))
      (q := (826606091451197 / 1600000000000000 : ℚ))
      (U := (-(1651076591580467623333 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_11 :
    Uω (aρ 11) (bρ 11) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(3835280052829488580907 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18575127284217941 / 40000000000000000 : ℝ) ≤
      (-(3835280052829488580907 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18575127284217941 / 40000000000000000 : ℚ))
        (r' := (18575127284217941 / 10000000000000000 : ℚ))
        (U := (-(3835280052829488580907 / 5000000000000000000000 : ℚ)))
        (U' := (3096191750170511419093 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (8582269999409 / 19531250000000 : ℚ))
      (q := (18575127284217941 / 40000000000000000 : ℚ))
      (U := (-(3835280052829488580907 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_12 :
    Uω (aρ 12) (bρ 12) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(2253017069146923309059 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16243171838822357 / 40000000000000000 : ℝ) ≤
      (-(2253017069146923309059 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16243171838822357 / 40000000000000000 : ℚ))
        (r' := (16243171838822357 / 10000000000000000 : ℚ))
        (U := (-(2253017069146923309059 / 2500000000000000000000 : ℚ)))
        (U' := (1212718832353076690941 / 2500000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (456480576710577 / 1250000000000000 : ℚ))
      (q := (16243171838822357 / 40000000000000000 : ℚ))
      (U := (-(2253017069146923309059 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_13 :
    Uω (aρ 13) (bρ 13) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(2144018610618247468463 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13692800014302969 / 40000000000000000 : ℝ) ≤
      (-(2144018610618247468463 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13692800014302969 / 40000000000000000 : ℚ))
        (r' := (13692800014302969 / 10000000000000000 : ℚ))
        (U := (-(2144018610618247468463 / 2000000000000000000000 : ℚ)))
        (U' := (628570110581752531537 / 2000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (1388020221509961 / 5000000000000000 : ℚ))
      (q := (13692800014302969 / 40000000000000000 : ℚ))
      (U := (-(2144018610618247468463 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_14 :
    Uω (aρ 14) (bρ 14) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(6530820785372481273627 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10834281246531611 / 40000000000000000 : ℝ) ≤
      (-(6530820785372481273627 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10834281246531611 / 40000000000000000 : ℚ))
        (r' := (10834281246531611 / 10000000000000000 : ℚ))
        (U := (-(6530820785372481273627 / 5000000000000000000000 : ℚ)))
        (U' := (400651017627518726373 / 5000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (22553704112181 / 32000000000000 : ℚ))
      (s := (1690708344179243 / 10000000000000000 : ℚ))
      (q := (10834281246531611 / 40000000000000000 : ℚ))
      (U := (-(6530820785372481273627 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_609_15 :
    Uω (aρ 15) (bρ 15) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_609_16 :
    Uω (aρ 16) (bρ 16) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_609 :
    Uρ (22553704112181 / 32000000000000 : ℝ) ≤
      (-(6125866517931195617109 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_609_1 U_609_2 U_609_3 U_609_4 U_609_5 U_609_6 U_609_7 U_609_8 U_609_9 U_609_10
    U_609_11 U_609_12 U_609_13 U_609_14 U_609_15 U_609_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_610_1 :
    Uω (aρ 1) (bρ 1) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(3567125202846665950607 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3499868484350393 / 5000000000000000 : ℝ) ≤
      (-(3567125202846665950607 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3499868484350393 / 5000000000000000 : ℚ))
        (r' := (3499868484350393 / 2500000000000000 : ℚ))
        (U := (-(3567125202846665950607 / 10000000000000000000000 : ℚ)))
        (U' := (3364346600153334049393 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (6999713872420947 / 10000000000000000 : ℚ))
      (q := (3499868484350393 / 5000000000000000 : ℚ))
      (U := (-(3567125202846665950607 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_2 :
    Uω (aρ 2) (bρ 2) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(720264980638036197189 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13951677933076191 / 20000000000000000 : ℝ) ≤
      (-(720264980638036197189 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13951677933076191 / 20000000000000000 : ℚ))
        (r' := (13951677933076191 / 10000000000000000 : ℚ))
        (U := (-(720264980638036197189 / 2000000000000000000000 : ℚ)))
        (U' := (666029379961963802811 / 2000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (3487843440302783 / 5000000000000000 : ℚ))
      (q := (13951677933076191 / 20000000000000000 : ℚ))
      (U := (-(720264980638036197189 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_3 :
    Uω (aρ 3) (bρ 3) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(146802045239044294797 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13856122049400311 / 20000000000000000 : ℝ) ≤
      (-(146802045239044294797 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13856122049400311 / 20000000000000000 : ℚ))
        (r' := (13856122049400311 / 10000000000000000 : ℚ))
        (U := (-(146802045239044294797 / 400000000000000000000 : ℚ)))
        (U' := (130456826880955705203 / 400000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (3463763551639843 / 5000000000000000 : ℚ))
      (q := (13856122049400311 / 20000000000000000 : ℚ))
      (U := (-(146802045239044294797 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_4 :
    Uω (aρ 4) (bρ 4) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(1892584003101455628531 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8560955805387 / 12500000000000 : ℝ) ≤
      (-(1892584003101455628531 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8560955805387 / 12500000000000 : ℚ))
        (r' := (8560955805387 / 6250000000000 : ℚ))
        (U := (-(1892584003101455628531 / 5000000000000000000000 : ℚ)))
        (U' := (1573151898398544371469 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (273889140942543 / 400000000000000 : ℚ))
      (q := (8560955805387 / 12500000000000 : ℚ))
      (U := (-(1892584003101455628531 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_5 :
    Uω (aρ 5) (bρ 5) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(3962844173437486658913 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13456306164079367 / 20000000000000000 : ℝ) ≤
      (-(3962844173437486658913 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13456306164079367 / 20000000000000000 : ℚ))
        (r' := (13456306164079367 / 10000000000000000 : ℚ))
        (U := (-(3962844173437486658913 / 10000000000000000000000 : ℚ)))
        (U' := (2968627629562513341087 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (3362097659179371 / 5000000000000000 : ℚ))
      (q := (13456306164079367 / 20000000000000000 : ℚ))
      (U := (-(3962844173437486658913 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_6 :
    Uω (aρ 6) (bρ 6) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(2111395698327103507627 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (655551023387351 / 1000000000000000 : ℝ) ≤
      (-(2111395698327103507627 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (655551023387351 / 1000000000000000 : ℚ))
        (r' := (655551023387351 / 500000000000000 : ℚ))
        (U := (-(2111395698327103507627 / 5000000000000000000000 : ℚ)))
        (U' := (1354340203172896492373 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (1309229999433279 / 2000000000000000 : ℚ))
      (q := (655551023387351 / 1000000000000000 : ℚ))
      (U := (-(2111395698327103507627 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_7 :
    Uω (aρ 7) (bρ 7) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(4587562229901919172883 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1264138619844117 / 2000000000000000 : ℝ) ≤
      (-(4587562229901919172883 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1264138619844117 / 2000000000000000 : ℚ))
        (r' := (1264138619844117 / 1000000000000000 : ℚ))
        (U := (-(4587562229901919172883 / 10000000000000000000000 : ℚ)))
        (U' := (2343909573098080827117 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (1260035421724109 / 2000000000000000 : ℚ))
      (q := (1264138619844117 / 2000000000000000 : ℚ))
      (U := (-(4587562229901919172883 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_8 :
    Uω (aρ 8) (bρ 8) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(2541030616916354549827 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12031475208131079 / 20000000000000000 : ℝ) ≤
      (-(2541030616916354549827 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12031475208131079 / 20000000000000000 : ℚ))
        (r' := (12031475208131079 / 10000000000000000 : ℚ))
        (U := (-(2541030616916354549827 / 5000000000000000000000 : ℚ)))
        (U' := (924705284583645450173 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (2986903884825227 / 5000000000000000 : ℚ))
      (q := (12031475208131079 / 20000000000000000 : ℚ))
      (U := (-(2541030616916354549827 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_9 :
    Uω (aρ 9) (bρ 9) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(179171113532017318017 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5636354715049359 / 10000000000000000 : ℝ) ≤
      (-(179171113532017318017 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5636354715049359 / 10000000000000000 : ℚ))
        (r' := (5636354715049359 / 5000000000000000 : ℚ))
        (U := (-(179171113532017318017 / 312500000000000000000 : ℚ)))
        (U' := (37437380311732681983 / 312500000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (5556007619978093 / 10000000000000000 : ℚ))
      (q := (5636354715049359 / 10000000000000000 : ℚ))
      (U := (-(179171113532017318017 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_10 :
    Uω (aρ 10) (bρ 10) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(821505687596867965743 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10365963754816079 / 20000000000000000 : ℝ) ≤
      (-(821505687596867965743 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10365963754816079 / 20000000000000000 : ℚ))
        (r' := (10365963754816079 / 10000000000000000 : ℚ))
        (U := (-(821505687596867965743 / 1250000000000000000000 : ℚ)))
        (U' := (44928287778132034257 / 1250000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (2518910489095227 / 5000000000000000 : ℚ))
      (q := (10365963754816079 / 20000000000000000 : ℚ))
      (U := (-(821505687596867965743 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_11 :
    Uω (aρ 11) (bρ 11) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(7633712040526915893759 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2330462411740549 / 5000000000000000 : ℝ) ≤
      (-(7633712040526915893759 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2330462411740549 / 5000000000000000 : ℚ))
        (r' := (2330462411740549 / 1250000000000000 : ℚ))
        (U := (-(7633712040526915893759 / 10000000000000000000000 : ℚ)))
        (U' := (6229231565473084106241 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (4412183496541571 / 10000000000000000 : ℚ))
      (q := (2330462411740549 / 5000000000000000 : ℚ))
      (U := (-(7633712040526915893759 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_12 :
    Uω (aρ 12) (bρ 12) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(8967759658547838351263 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4078825692896653 / 10000000000000000 : ℝ) ≤
      (-(8967759658547838351263 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4078825692896653 / 10000000000000000 : ℚ))
        (r' := (4078825692896653 / 2500000000000000 : ℚ))
        (U := (-(8967759658547838351263 / 10000000000000000000000 : ℚ)))
        (U' := (4895183947452161648737 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (3671685332057681 / 10000000000000000 : ℚ))
      (q := (4078825692896653 / 10000000000000000 : ℚ))
      (U := (-(8967759658547838351263 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_13 :
    Uω (aρ 13) (bρ 13) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(10661896036179101416151 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1721590044551353 / 5000000000000000 : ℝ) ≤
      (-(10661896036179101416151 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1721590044551353 / 5000000000000000 : ℚ))
        (r' := (1721590044551353 / 1250000000000000 : ℚ))
        (U := (-(10661896036179101416151 / 10000000000000000000000 : ℚ)))
        (U' := (3201047569820898583849 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (2799775866064787 / 10000000000000000 : ℚ))
      (q := (1721590044551353 / 5000000000000000 : ℚ))
      (U := (-(10661896036179101416151 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_14 :
    Uω (aρ 14) (bρ 14) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(6483336367110149200723 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5468831640779683 / 20000000000000000 : ℝ) ≤
      (-(6483336367110149200723 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5468831640779683 / 20000000000000000 : ℚ))
        (r' := (5468831640779683 / 5000000000000000 : ℚ))
        (U := (-(6483336367110149200723 / 5000000000000000000000 : ℚ)))
        (U' := (448135435889850799277 / 5000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (2260562330581 / 3200000000000 : ℚ))
      (s := (863087306842029 / 5000000000000000 : ℚ))
      (q := (5468831640779683 / 20000000000000000 : ℚ))
      (U := (-(6483336367110149200723 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_610_15 :
    Uω (aρ 15) (bρ 15) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_610_16 :
    Uω (aρ 16) (bρ 16) (2260562330581 / 3200000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_610 :
    Uρ (2260562330581 / 3200000000000 : ℝ) ≤
      (-(3047661947672350956073 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_610_1 U_610_2 U_610_3 U_610_4 U_610_5 U_610_6 U_610_7 U_610_8 U_610_9 U_610_10
    U_610_11 U_610_12 U_610_13 U_610_14 U_610_15 U_610_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_611_1 :
    Uω (aρ 1) (bρ 1) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(1771986433177761046279 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28063847080485117 / 40000000000000000 : ℝ) ≤
      (-(1771986433177761046279 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (28063847080485117 / 40000000000000000 : ℚ))
        (r' := (28063847080485117 / 20000000000000000 : ℚ))
        (U := (-(1771986433177761046279 / 5000000000000000000000 : ℚ)))
        (U' := (1693749468322238953721 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (7015938727252871 / 10000000000000000 : ℚ))
      (q := (28063847080485117 / 40000000000000000 : ℚ))
      (U := (-(1771986433177761046279 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_2 :
    Uω (aρ 2) (bρ 2) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(715618582912362501781 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27968256269851673 / 40000000000000000 : ℝ) ≤
      (-(715618582912362501781 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27968256269851673 / 40000000000000000 : ℚ))
        (r' := (27968256269851673 / 20000000000000000 : ℚ))
        (U := (-(715618582912362501781 / 2000000000000000000000 : ℚ)))
        (U' := (670675777687637498219 / 2000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (6991912334446149 / 10000000000000000 : ℚ))
      (q := (27968256269851673 / 40000000000000000 : ℚ))
      (U := (-(715618582912362501781 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_3 :
    Uω (aρ 3) (bρ 3) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(91166445666578071919 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27777148081072199 / 40000000000000000 : ℝ) ≤
      (-(91166445666578071919 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27777148081072199 / 40000000000000000 : ℚ))
        (r' := (27777148081072199 / 20000000000000000 : ℚ))
        (U := (-(91166445666578071919 / 250000000000000000000 : ℚ)))
        (U' := (82120349408421928081 / 250000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (1735938586601603 / 2500000000000000 : ℚ))
      (q := (27777148081072199 / 40000000000000000 : ℚ))
      (U := (-(91166445666578071919 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_4 :
    Uω (aρ 4) (bρ 4) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(3761500697413053400093 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27459972094416933 / 40000000000000000 : ℝ) ≤
      (-(3761500697413053400093 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27459972094416933 / 40000000000000000 : ℚ))
        (r' := (27459972094416933 / 20000000000000000 : ℚ))
        (U := (-(3761500697413053400093 / 10000000000000000000000 : ℚ)))
        (U' := (3169971105586946599907 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (6863460534143779 / 10000000000000000 : ℚ))
      (q := (27459972094416933 / 40000000000000000 : ℚ))
      (U := (-(3761500697413053400093 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_5 :
    Uω (aρ 5) (bρ 5) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(1969372182254922753893 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5395509885359569 / 8000000000000000 : ℝ) ≤
      (-(1969372182254922753893 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5395509885359569 / 8000000000000000 : ℚ))
        (r' := (5395509885359569 / 4000000000000000 : ℚ))
        (U := (-(1969372182254922753893 / 5000000000000000000000 : ℚ)))
        (U' := (1496363719245077246107 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (1348087823933847 / 2000000000000000 : ℚ))
      (q := (5395509885359569 / 8000000000000000 : ℚ))
      (U := (-(1969372182254922753893 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_6 :
    Uω (aρ 6) (bρ 6) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(4198036972603761804577 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26287032495816753 / 40000000000000000 : ℝ) ≤
      (-(4198036972603761804577 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26287032495816753 / 40000000000000000 : ℚ))
        (r' := (26287032495816753 / 20000000000000000 : ℚ))
        (U := (-(4198036972603761804577 / 10000000000000000000000 : ℚ)))
        (U' := (2733434830396238195423 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (6562421029318689 / 10000000000000000 : ℚ))
      (q := (26287032495816753 / 40000000000000000 : ℚ))
      (U := (-(4198036972603761804577 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_7 :
    Uω (aρ 7) (bρ 7) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(912368540818807209291 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1013915287293877 / 1600000000000000 : ℝ) ≤
      (-(912368540818807209291 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1013915287293877 / 1600000000000000 : ℚ))
        (r' := (1013915287293877 / 800000000000000 : ℚ))
        (U := (-(912368540818807209291 / 2000000000000000000000 : ℚ)))
        (U' := (473925819781192790709 / 2000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (252660290133751 / 400000000000000 : ℚ))
      (q := (1013915287293877 / 1600000000000000 : ℚ))
      (U := (-(912368540818807209291 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_8 :
    Uω (aρ 8) (bρ 8) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(5054938755538850791503 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24128303688369371 / 40000000000000000 : ℝ) ≤
      (-(5054938755538850791503 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24128303688369371 / 40000000000000000 : ℚ))
        (r' := (24128303688369371 / 20000000000000000 : ℚ))
        (U := (-(5054938755538850791503 / 10000000000000000000000 : ℚ)))
        (U' := (1876533047461149208497 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (2995129828847499 / 5000000000000000 : ℚ))
      (q := (24128303688369371 / 40000000000000000 : ℚ))
      (U := (-(5054938755538850791503 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_9 :
    Uω (aρ 9) (bρ 9) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(713039655535341428553 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22611253604052877 / 40000000000000000 : ℝ) ≤
      (-(713039655535341428553 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (22611253604052877 / 40000000000000000 : ℚ))
        (r' := (22611253604052877 / 20000000000000000 : ℚ))
        (U := (-(713039655535341428553 / 1250000000000000000000 : ℚ)))
        (U' := (153394319839658571447 / 1250000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (5572700243896751 / 10000000000000000 : ℚ))
      (q := (22611253604052877 / 40000000000000000 : ℚ))
      (U := (-(713039655535341428553 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_10 :
    Uω (aρ 10) (bρ 10) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(6539894335196580513757 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20798690340675543 / 40000000000000000 : ℝ) ≤
      (-(6539894335196580513757 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20798690340675543 / 40000000000000000 : ℚ))
        (r' := (20798690340675543 / 20000000000000000 : ℚ))
        (U := (-(6539894335196580513757 / 10000000000000000000000 : ℚ)))
        (U' := (391577467803419486243 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (1263744411425771 / 2500000000000000 : ℚ))
      (q := (20798690340675543 / 40000000000000000 : ℚ))
      (U := (-(6539894335196580513757 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_11 :
    Uω (aρ 11) (bρ 11) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(1899253611517541986453 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18712242877819023 / 40000000000000000 : ℝ) ≤
      (-(1899253611517541986453 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18712242877819023 / 40000000000000000 : ℚ))
        (r' := (18712242877819023 / 10000000000000000 : ℚ))
        (U := (-(1899253611517541986453 / 2500000000000000000000 : ℚ)))
        (U' := (1566482289982458013547 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (276889408779989 / 625000000000000 : ℚ))
      (q := (18712242877819023 / 40000000000000000 : ℚ))
      (U := (-(1899253611517541986453 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_12 :
    Uω (aρ 12) (bρ 12) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(8923689615546948989069 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16387363049407717 / 40000000000000000 : ℝ) ≤
      (-(8923689615546948989069 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16387363049407717 / 40000000000000000 : ℚ))
        (r' := (16387363049407717 / 10000000000000000 : ℚ))
        (U := (-(8923689615546948989069 / 10000000000000000000000 : ℚ)))
        (U' := (4939253990453051010931 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (3691490722959171 / 10000000000000000 : ℚ))
      (q := (16387363049407717 / 40000000000000000 : ℚ))
      (U := (-(8923689615546948989069 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_13 :
    Uω (aρ 13) (bρ 13) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(1325523652575441464269 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13852428102585417 / 40000000000000000 : ℝ) ≤
      (-(1325523652575441464269 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13852428102585417 / 40000000000000000 : ℚ))
        (r' := (13852428102585417 / 10000000000000000 : ℚ))
        (U := (-(1325523652575441464269 / 1250000000000000000000 : ℚ)))
        (U' := (407344298174558535731 / 1250000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (2823404991143021 / 10000000000000000 : ℚ))
      (q := (13852428102585417 / 40000000000000000 : ℚ))
      (U := (-(1325523652575441464269 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_14 :
    Uω (aρ 14) (bρ 14) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(3218405066046634124583 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11039915945363911 / 40000000000000000 : ℝ) ≤
      (-(3218405066046634124583 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11039915945363911 / 40000000000000000 : ℚ))
        (r' := (11039915945363911 / 10000000000000000 : ℚ))
        (U := (-(3218405066046634124583 / 2500000000000000000000 : ℚ)))
        (U' := (247330835453365875417 / 2500000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (22657542499439 / 32000000000000 : ℚ))
      (s := (440269049394317 / 2500000000000000 : ℚ))
      (q := (11039915945363911 / 40000000000000000 : ℚ))
      (U := (-(3218405066046634124583 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_611_15 :
    Uω (aρ 15) (bρ 15) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_611_16 :
    Uω (aρ 16) (bρ 16) (22657542499439 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_611 :
    Uρ (22657542499439 / 32000000000000 : ℝ) ≤
      (-(1516242492074414445773 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_611_1 U_611_2 U_611_3 U_611_4 U_611_5 U_611_6 U_611_7 U_611_8 U_611_9 U_611_10
    U_611_11 U_611_12 U_611_13 U_611_14 U_611_15 U_611_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_612_1 :
    Uω (aρ 1) (bρ 1) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(704174801898035062819 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2812874628518123 / 4000000000000000 : ℝ) ≤
      (-(704174801898035062819 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2812874628518123 / 4000000000000000 : ℚ))
        (r' := (2812874628518123 / 2000000000000000 : ℚ))
        (U := (-(704174801898035062819 / 2000000000000000000000 : ℚ)))
        (U' := (682119558701964937181 / 2000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (1406432716318373 / 2000000000000000 : ℚ))
      (q := (2812874628518123 / 4000000000000000 : ℚ))
      (U := (-(704174801898035062819 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_2 :
    Uω (aρ 2) (bρ 2) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(888728693930132351883 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14016578333507227 / 20000000000000000 : ℝ) ≤
      (-(888728693930132351883 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (14016578333507227 / 20000000000000000 : ℚ))
        (r' := (14016578333507227 / 10000000000000000 : ℚ))
        (U := (-(888728693930132351883 / 2500000000000000000000 : ℚ)))
        (U' := (844139256819867648117 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (7008137785018477 / 10000000000000000 : ℚ))
      (q := (14016578333507227 / 20000000000000000 : ℚ))
      (U := (-(888728693930132351883 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_3 :
    Uω (aρ 3) (bρ 3) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(3623319127680336539177 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (108758015781547 / 156250000000000 : ℝ) ≤
      (-(3623319127680336539177 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (108758015781547 / 156250000000000 : ℚ))
        (r' := (108758015781547 / 78125000000000 : ℚ))
        (U := (-(3623319127680336539177 / 10000000000000000000000 : ℚ)))
        (U' := (3308152675319663460823 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (3479990788949633 / 5000000000000000 : ℚ))
      (q := (108758015781547 / 156250000000000 : ℚ))
      (U := (-(3623319127680336539177 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_4 :
    Uω (aρ 4) (bρ 4) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(116809040482449137779 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13762442771534643 / 20000000000000000 : ℝ) ≤
      (-(116809040482449137779 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13762442771534643 / 20000000000000000 : ℚ))
        (r' := (13762442771534643 / 10000000000000000 : ℚ))
        (U := (-(116809040482449137779 / 312500000000000000000 : ℚ)))
        (U' := (99799453361300862221 / 312500000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (6879692510460893 / 10000000000000000 : ℚ))
      (q := (13762442771534643 / 20000000000000000 : ℚ))
      (U := (-(116809040482449137779 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_5 :
    Uω (aρ 5) (bρ 5) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(1957351281884243234707 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1690155396394973 / 2500000000000000 : ℝ) ≤
      (-(1957351281884243234707 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1690155396394973 / 2500000000000000 : ℚ))
        (r' := (1690155396394973 / 1250000000000000 : ℚ))
        (U := (-(1957351281884243234707 / 5000000000000000000000 : ℚ)))
        (U' := (1508384619615756765293 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (3378341414710517 / 5000000000000000 : ℚ))
      (q := (1690155396394973 / 2500000000000000 : ℚ))
      (U := (-(1957351281884243234707 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_6 :
    Uω (aρ 6) (bρ 6) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(4173343848933882049953 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13176011799446877 / 20000000000000000 : ℝ) ≤
      (-(4173343848933882049953 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13176011799446877 / 20000000000000000 : ℚ))
        (r' := (13176011799446877 / 10000000000000000 : ℚ))
        (U := (-(4173343848933882049953 / 10000000000000000000000 : ℚ)))
        (U' := (2758127954066117950047 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (6578691832848127 / 10000000000000000 : ℚ))
      (q := (13176011799446877 / 20000000000000000 : ℚ))
      (U := (-(4173343848933882049953 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_7 :
    Uω (aρ 7) (bρ 7) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(2268094792214219806731 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3176623860524561 / 5000000000000000 : ℝ) ≤
      (-(2268094792214219806731 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3176623860524561 / 5000000000000000 : ℚ))
        (r' := (3176623860524561 / 2500000000000000 : ℚ))
        (U := (-(2268094792214219806731 / 5000000000000000000000 : ℚ)))
        (U' := (1197641109285780193269 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (3166418428129747 / 5000000000000000 : ℚ))
      (q := (3176623860524561 / 5000000000000000 : ℚ))
      (U := (-(2268094792214219806731 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_8 :
    Uω (aρ 8) (bρ 8) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(2513945331327445238627 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3024206811147909 / 5000000000000000 : ℝ) ≤
      (-(2513945331327445238627 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3024206811147909 / 5000000000000000 : ℚ))
        (r' := (3024206811147909 / 2500000000000000 : ℚ))
        (U := (-(2513945331327445238627 / 5000000000000000000000 : ℚ)))
        (U' := (951790570172554761373 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (3003355155046443 / 5000000000000000 : ℚ))
      (q := (3024206811147909 / 5000000000000000 : ℚ))
      (U := (-(2513945331327445238627 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_9 :
    Uω (aρ 9) (bρ 9) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(5675246059732281515241 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2834635354627983 / 5000000000000000 : ℝ) ≤
      (-(5675246059732281515241 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2834635354627983 / 5000000000000000 : ℚ))
        (r' := (2834635354627983 / 2500000000000000 : ℚ))
        (U := (-(5675246059732281515241 / 10000000000000000000000 : ℚ)))
        (U' := (1256225743267718484759 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (2794695056186591 / 5000000000000000 : ℚ))
      (q := (2834635354627983 / 5000000000000000 : ℚ))
      (U := (-(5675246059732281515241 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_10 :
    Uω (aρ 10) (bρ 10) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(650785208705559288509 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10432720452581229 / 20000000000000000 : ℝ) ≤
      (-(650785208705559288509 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10432720452581229 / 20000000000000000 : ℚ))
        (r' := (10432720452581229 / 10000000000000000 : ℚ))
        (U := (-(650785208705559288509 / 1000000000000000000000 : ℚ)))
        (U' := (42361971594440711491 / 1000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (5072128179937479 / 10000000000000000 : ℚ))
      (q := (10432720452581229 / 20000000000000000 : ℚ))
      (U := (-(650785208705559288509 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_11 :
    Uω (aρ 11) (bρ 11) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(7560465982075085006291 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1878075838188081 / 4000000000000000 : ℝ) ≤
      (-(7560465982075085006291 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1878075838188081 / 4000000000000000 : ℚ))
        (r' := (1878075838188081 / 1000000000000000 : ℚ))
        (U := (-(7560465982075085006291 / 10000000000000000000000 : ℚ)))
        (U' := (6302477623924914993709 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (889652708900331 / 2000000000000000 : ℚ))
      (q := (1878075838188081 / 4000000000000000 : ℚ))
      (U := (-(7560465982075085006291 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_12 :
    Uω (aρ 12) (bρ 12) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(8879855177153937258143 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4114838450862511 / 10000000000000000 : ℝ) ≤
      (-(8879855177153937258143 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4114838450862511 / 10000000000000000 : ℚ))
        (r' := (4114838450862511 / 2500000000000000 : ℚ))
        (U := (-(8879855177153937258143 / 10000000000000000000000 : ℚ)))
        (U' := (4983088428846062741857 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (463907668996409 / 1250000000000000 : ℚ))
      (q := (4114838450862511 / 10000000000000000 : ℚ))
      (U := (-(8879855177153937258143 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_13 :
    Uω (aρ 13) (bρ 13) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(2636740574611385909277 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3482982136594709 / 10000000000000000 : ℝ) ≤
      (-(2636740574611385909277 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3482982136594709 / 10000000000000000 : ℚ))
        (r' := (3482982136594709 / 2500000000000000 : ℚ))
        (U := (-(2636740574611385909277 / 2500000000000000000000 : ℚ)))
        (U' := (828995326888614090723 / 2500000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (711732616257667 / 2500000000000000 : ℚ))
      (q := (3482982136594709 / 10000000000000000 : ℚ))
      (U := (-(2636740574611385909277 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_14 :
    Uω (aρ 14) (bρ 14) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(12782380229451382714503 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5570552549959177 / 20000000000000000 : ℝ) ≤
      (-(12782380229451382714503 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5570552549959177 / 20000000000000000 : ℚ))
        (r' := (5570552549959177 / 5000000000000000 : ℚ))
        (U := (-(12782380229451382714503 / 10000000000000000000000 : ℚ)))
        (U' := (1080563376548617285497 / 10000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (5677365423267 / 8000000000000 : ℚ))
      (s := (1795446026845427 / 10000000000000000 : ℚ))
      (q := (5570552549959177 / 20000000000000000 : ℚ))
      (U := (-(12782380229451382714503 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_612_15 :
    Uω (aρ 15) (bρ 15) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_612_16 :
    Uω (aρ 16) (bρ 16) (5677365423267 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_612 :
    Uρ (5677365423267 / 8000000000000 : ℝ) ≤
      (-(48278391504829887333 / 80000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_612_1 U_612_2 U_612_3 U_612_4 U_612_5 U_612_6 U_612_7 U_612_8 U_612_9 U_612_10
    U_612_11 U_612_12 U_612_13 U_612_14 U_612_15 U_612_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_613_1 :
    Uω (aρ 1) (bρ 1) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(874457096438228208609 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28193645488898291 / 40000000000000000 : ℝ) ≤
      (-(874457096438228208609 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (28193645488898291 / 40000000000000000 : ℚ))
        (r' := (28193645488898291 / 20000000000000000 : ℚ))
        (U := (-(874457096438228208609 / 2500000000000000000000 : ℚ)))
        (U' := (858410854311771791391 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (7048388435441333 / 10000000000000000 : ℚ))
      (q := (28193645488898291 / 40000000000000000 : ℚ))
      (U := (-(874457096438228208609 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_2 :
    Uω (aρ 2) (bρ 2) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(3531790237594273493879 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28098057057686023 / 40000000000000000 : ℝ) ≤
      (-(3531790237594273493879 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (28098057057686023 / 40000000000000000 : ℚ))
        (r' := (28098057057686023 / 20000000000000000 : ℚ))
        (U := (-(3531790237594273493879 / 10000000000000000000000 : ℚ)))
        (U' := (3399681565405726506121 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (7024363232345199 / 10000000000000000 : ℚ))
      (q := (28098057057686023 / 40000000000000000 : ℚ))
      (U := (-(3531790237594273493879 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_3 :
    Uω (aρ 3) (bρ 3) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(3600034779659862000939 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27906955975974487 / 40000000000000000 : ℝ) ≤
      (-(3600034779659862000939 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27906955975974487 / 40000000000000000 : ℚ))
        (r' := (27906955975974487 / 20000000000000000 : ℚ))
        (U := (-(3600034779659862000939 / 10000000000000000000000 : ℚ)))
        (U' := (3331437023340137999061 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (6976208797839431 / 10000000000000000 : ℚ))
      (q := (27906955975974487 / 40000000000000000 : ℚ))
      (U := (-(3600034779659862000939 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_4 :
    Uω (aρ 4) (bρ 4) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(371433353665875078499 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27589798923679363 / 40000000000000000 : ℝ) ≤
      (-(371433353665875078499 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27589798923679363 / 40000000000000000 : ℚ))
        (r' := (27589798923679363 / 20000000000000000 : ℚ))
        (U := (-(371433353665875078499 / 1000000000000000000000 : ℚ)))
        (U' := (321713826634124921501 / 1000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (6895924452756869 / 10000000000000000 : ℚ))
      (q := (27589798923679363 / 40000000000000000 : ℚ))
      (U := (-(371433353665875078499 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_5 :
    Uω (aρ 5) (bρ 5) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(486339811538652721501 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27107423076041433 / 40000000000000000 : ℝ) ≤
      (-(486339811538652721501 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27107423076041433 / 40000000000000000 : ℚ))
        (r' := (27107423076041433 / 20000000000000000 : ℚ))
        (U := (-(486339811538652721501 / 1250000000000000000000 : ℚ)))
        (U' := (380094163836347278499 / 1250000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (846615806034113 / 1250000000000000 : ℚ))
      (q := (27107423076041433 / 40000000000000000 : ℚ))
      (U := (-(486339811538652721501 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_6 :
    Uω (aρ 6) (bρ 6) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(1037177930485340854641 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26417014248109331 / 40000000000000000 : ℝ) ≤
      (-(1037177930485340854641 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26417014248109331 / 40000000000000000 : ℚ))
        (r' := (26417014248109331 / 20000000000000000 : ℚ))
        (U := (-(1037177930485340854641 / 2500000000000000000000 : ℚ)))
        (U' := (695690020264659145359 / 2500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (6594962409446853 / 10000000000000000 : ℚ))
      (q := (26417014248109331 / 40000000000000000 : ℚ))
      (U := (-(1037177930485340854641 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_7 :
    Uω (aρ 7) (bρ 7) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(902120505339501589781 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25478098510791969 / 40000000000000000 : ℝ) ≤
      (-(902120505339501589781 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25478098510791969 / 40000000000000000 : ℚ))
        (r' := (25478098510791969 / 20000000000000000 : ℚ))
        (U := (-(902120505339501589781 / 2000000000000000000000 : ℚ)))
        (U' := (484173855260498410219 / 2000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (1587291480387043 / 2500000000000000 : ℚ))
      (q := (25478098510791969 / 40000000000000000 : ℚ))
      (U := (-(902120505339501589781 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_8 :
    Uω (aρ 8) (bρ 8) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(1250229135690731567857 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24259002838952893 / 40000000000000000 : ℝ) ≤
      (-(1250229135690731567857 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24259002838952893 / 40000000000000000 : ℚ))
        (r' := (24259002838952893 / 20000000000000000 : ℚ))
        (U := (-(1250229135690731567857 / 2500000000000000000000 : ℚ)))
        (U' := (482638815059268432143 / 2500000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (3011579868484317 / 5000000000000000 : ℚ))
      (q := (24259002838952893 / 40000000000000000 : ℚ))
      (U := (-(1250229135690731567857 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_9 :
    Uω (aρ 9) (bρ 9) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(141156538628002730241 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22742906608329809 / 40000000000000000 : ℝ) ≤
      (-(141156538628002730241 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (22742906608329809 / 40000000000000000 : ℚ))
        (r' := (22742906608329809 / 20000000000000000 : ℚ))
        (U := (-(141156538628002730241 / 250000000000000000000 : ℚ)))
        (U' := (32130256446997269759 / 250000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (1401519312504273 / 2500000000000000 : ℚ))
      (q := (22742906608329809 / 40000000000000000 : ℚ))
      (U := (-(141156538628002730241 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_10 :
    Uω (aρ 10) (bρ 10) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(6475917982535767971497 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20932179327105513 / 40000000000000000 : ℝ) ≤
      (-(6475917982535767971497 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20932179327105513 / 40000000000000000 : ℚ))
        (r' := (20932179327105513 / 20000000000000000 : ℚ))
        (U := (-(6475917982535767971497 / 10000000000000000000000 : ℚ)))
        (U' := (455553820464232028503 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (636159080362493 / 1250000000000000 : ℚ))
      (q := (20932179327105513 / 40000000000000000 : ℚ))
      (U := (-(6475917982535767971497 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_11 :
    Uω (aρ 11) (bρ 11) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(7524065327419626836843 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3769849229246809 / 8000000000000000 : ℝ) ≤
      (-(7524065327419626836843 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3769849229246809 / 8000000000000000 : ℚ))
        (r' := (3769849229246809 / 2000000000000000 : ℚ))
        (U := (-(7524065327419626836843 / 10000000000000000000000 : ℚ)))
        (U' := (6338878278580373163157 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (446628267866921 / 1000000000000000 : ℚ))
      (q := (3769849229246809 / 8000000000000000 : ℚ))
      (U := (-(7524065327419626836843 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_12 :
    Uω (aρ 12) (bρ 12) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(8836253433533761614819 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16531276138937201 / 40000000000000000 : ℝ) ≤
      (-(8836253433533761614819 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16531276138937201 / 40000000000000000 : ℚ))
        (r' := (16531276138937201 / 10000000000000000 : ℚ))
        (U := (-(8836253433533761614819 / 10000000000000000000000 : ℚ)))
        (U' := (5026690172466238385181 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (932749442926447 / 2500000000000000 : ℚ))
      (q := (16531276138937201 / 40000000000000000 : ℚ))
      (U := (-(8836253433533761614819 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_13 :
    Uω (aρ 13) (bρ 13) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(2098041064256764806811 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14011226784954181 / 40000000000000000 : ℝ) ≤
      (-(2098041064256764806811 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (14011226784954181 / 40000000000000000 : ℚ))
        (r' := (14011226784954181 / 10000000000000000 : ℚ))
        (U := (-(2098041064256764806811 / 2000000000000000000000 : ℚ)))
        (U' := (674547656943235193189 / 2000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (1435177418154639 / 5000000000000000 : ℚ))
      (q := (14011226784954181 / 40000000000000000 : ℚ))
      (U := (-(2098041064256764806811 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_14 :
    Uω (aρ 14) (bρ 14) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(1586607232003425158267 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11241290690528949 / 40000000000000000 : ℝ) ≤
      (-(1586607232003425158267 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11241290690528949 / 40000000000000000 : ℚ))
        (r' := (11241290690528949 / 10000000000000000 : ℚ))
        (U := (-(1586607232003425158267 / 1250000000000000000000 : ℚ)))
        (U' := (146260718746574841733 / 1250000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (22761380886697 / 32000000000000 : ℚ))
      (s := (914657037070831 / 5000000000000000 : ℚ))
      (q := (11241290690528949 / 40000000000000000 : ℚ))
      (U := (-(1586607232003425158267 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_613_15 :
    Uω (aρ 15) (bρ 15) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_613_16 :
    Uω (aρ 16) (bρ 16) (22761380886697 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_613 :
    Uρ (22761380886697 / 32000000000000 : ℝ) ≤
      (-(6004805442082874770883 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_613_1 U_613_2 U_613_3 U_613_4 U_613_5 U_613_6 U_613_7 U_613_8 U_613_9 U_613_10
    U_613_11 U_613_12 U_613_13 U_613_14 U_613_15 U_613_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_614_1 :
    Uω (aρ 1) (bρ 1) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(347483575034634540937 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (565170893832861 / 800000000000000 : ℝ) ≤
      (-(347483575034634540937 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (565170893832861 / 800000000000000 : ℚ))
        (r' := (565170893832861 / 400000000000000 : ℚ))
        (U := (-(347483575034634540937 / 1000000000000000000000 : ℚ)))
        (U' := (345663605265365459063 / 1000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (141292265776093 / 200000000000000 : ℚ))
      (q := (565170893832861 / 800000000000000 : ℚ))
      (U := (-(347483575034634540937 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_2 :
    Uω (aρ 2) (bρ 2) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(350871905283512890253 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14081478720955629 / 20000000000000000 : ℝ) ≤
      (-(350871905283512890253 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (14081478720955629 / 20000000000000000 : ℚ))
        (r' := (14081478720955629 / 10000000000000000 : ℚ))
        (U := (-(350871905283512890253 / 1000000000000000000000 : ℚ)))
        (U' := (342275275016487109747 / 1000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (3520294338224377 / 5000000000000000 : ℚ))
      (q := (14081478720955629 / 20000000000000000 : ℚ))
      (U := (-(350871905283512890253 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_3 :
    Uω (aρ 3) (bρ 3) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(894201132501833096559 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6992964972232107 / 10000000000000000 : ℝ) ≤
      (-(894201132501833096559 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6992964972232107 / 10000000000000000 : ℚ))
        (r' := (6992964972232107 / 5000000000000000 : ℚ))
        (U := (-(894201132501833096559 / 2500000000000000000000 : ℚ)))
        (U' := (838666818248166903441 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (6992436006307339 / 10000000000000000 : ℚ))
      (q := (6992964972232107 / 10000000000000000 : ℚ))
      (U := (-(894201132501833096559 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_4 :
    Uω (aρ 4) (bρ 4) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(3690833159315097836869 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13827356118363259 / 20000000000000000 : ℝ) ≤
      (-(3690833159315097836869 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13827356118363259 / 20000000000000000 : ℚ))
        (r' := (13827356118363259 / 10000000000000000 : ℚ))
        (U := (-(3690833159315097836869 / 10000000000000000000000 : ℚ)))
        (U' := (3240638643684902163131 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (864019545158923 / 1250000000000000 : ℚ))
      (q := (13827356118363259 / 20000000000000000 : ℚ))
      (U := (-(3690833159315097836869 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_5 :
    Uω (aρ 5) (bρ 5) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(3866791873236816182813 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6793089907317087 / 10000000000000000 : ℝ) ≤
      (-(3866791873236816182813 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6793089907317087 / 10000000000000000 : ℚ))
        (r' := (6793089907317087 / 5000000000000000 : ℚ))
        (U := (-(3866791873236816182813 / 10000000000000000000000 : ℚ)))
        (U' := (3064679929763183817187 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (6789169976877299 / 10000000000000000 : ℚ))
      (q := (6793089907317087 / 10000000000000000 : ℚ))
      (U := (-(3866791873236816182813 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_6 :
    Uω (aρ 6) (bρ 6) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(412414029018064730309 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13241002223407207 / 20000000000000000 : ℝ) ≤
      (-(412414029018064730309 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13241002223407207 / 20000000000000000 : ℚ))
        (r' := (13241002223407207 / 10000000000000000 : ℚ))
        (U := (-(412414029018064730309 / 1000000000000000000000 : ℚ)))
        (U' := (280733151281935269691 / 1000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (1652808190197583 / 2500000000000000 : ℚ))
      (q := (13241002223407207 / 20000000000000000 : ℚ))
      (U := (-(412414029018064730309 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_7 :
    Uω (aρ 7) (bρ 7) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(897016237875904629603 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12771602535204123 / 20000000000000000 : ℝ) ≤
      (-(897016237875904629603 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12771602535204123 / 20000000000000000 : ℚ))
        (r' := (12771602535204123 / 10000000000000000 : ℚ))
        (U := (-(897016237875904629603 / 2000000000000000000000 : ℚ)))
        (U' := (489278122724095370397 / 2000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (397843403334203 / 625000000000000 : ℚ))
      (q := (12771602535204123 / 20000000000000000 : ℚ))
      (U := (-(897016237875904629603 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_8 :
    Uω (aρ 8) (bρ 8) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(4974015986909744955749 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1520271797356573 / 2500000000000000 : ℝ) ≤
      (-(4974015986909744955749 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1520271797356573 / 2500000000000000 : ℚ))
        (r' := (1520271797356573 / 1250000000000000 : ℚ))
        (U := (-(4974015986909744955749 / 10000000000000000000000 : ℚ)))
        (U' := (1957455816090255044251 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (6039607948335709 / 10000000000000000 : ℚ))
      (q := (1520271797356573 / 2500000000000000 : ℚ))
      (U := (-(4974015986909744955749 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_9 :
    Uω (aρ 9) (bρ 9) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(1404340792802545254119 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11404362483298911 / 20000000000000000 : ℝ) ≤
      (-(1404340792802545254119 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11404362483298911 / 20000000000000000 : ℚ))
        (r' := (11404362483298911 / 10000000000000000 : ℚ))
        (U := (-(1404340792802545254119 / 2500000000000000000000 : ℚ)))
        (U' := (328527157947454745881 / 2500000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (1405690420285509 / 2500000000000000 : ℚ))
      (q := (11404362483298911 / 20000000000000000 : ℚ))
      (U := (-(1404340792802545254119 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_10 :
    Uω (aρ 10) (bρ 10) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(6444091256402327224063 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (328107902012629 / 625000000000000 : ℝ) ≤
      (-(6444091256402327224063 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (328107902012629 / 625000000000000 : ℚ))
        (r' := (328107902012629 / 312500000000000 : ℚ))
        (U := (-(6444091256402327224063 / 10000000000000000000000 : ℚ)))
        (U' := (487380546597672775937 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (5106411095742253 / 10000000000000000 : ℚ))
      (q := (328107902012629 / 625000000000000 : ℚ))
      (U := (-(6444091256402327224063 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_11 :
    Uω (aρ 11) (bρ 11) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(7487811179694703890357 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2364713313159581 / 5000000000000000 : ℝ) ≤
      (-(7487811179694703890357 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2364713313159581 / 5000000000000000 : ℚ))
        (r' := (2364713313159581 / 1250000000000000 : ℚ))
        (U := (-(7487811179694703890357 / 10000000000000000000000 : ℚ)))
        (U' := (6375132426305296109643 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (4484288110181449 / 10000000000000000 : ℚ))
      (q := (2364713313159581 / 5000000000000000 : ℚ))
      (U := (-(7487811179694703890357 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_12 :
    Uω (aρ 12) (bρ 12) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(8792881533717337725777 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4150782783984341 / 10000000000000000 : ℝ) ≤
      (-(8792881533717337725777 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4150782783984341 / 10000000000000000 : ℚ))
        (r' := (4150782783984341 / 2500000000000000 : ℚ))
        (U := (-(8792881533717337725777 / 10000000000000000000000 : ℚ)))
        (U' := (5070062072282662274223 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (3750700522196807 / 10000000000000000 : ℚ))
      (q := (4150782783984341 / 10000000000000000 : ℚ))
      (U := (-(8792881533717337725777 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_13 :
    Uω (aρ 13) (bρ 13) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(5216954341376271766899 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3522581932218237 / 10000000000000000 : ℝ) ≤
      (-(5216954341376271766899 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3522581932218237 / 10000000000000000 : ℚ))
        (r' := (3522581932218237 / 2500000000000000 : ℚ))
        (U := (-(5216954341376271766899 / 5000000000000000000000 : ℚ)))
        (U' := (1714517461623728233101 / 5000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (2893680560259599 / 10000000000000000 : ℚ))
      (q := (3522581932218237 / 10000000000000000 : ℚ))
      (U := (-(5216954341376271766899 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_14 :
    Uω (aρ 14) (bρ 14) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(6302483216415656992739 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5670263729237359 / 20000000000000000 : ℝ) ≤
      (-(6302483216415656992739 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5670263729237359 / 20000000000000000 : ℚ))
        (r' := (5670263729237359 / 5000000000000000 : ℚ))
        (U := (-(6302483216415656992739 / 5000000000000000000000 : ℚ)))
        (U' := (628988586584343007261 / 5000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (11406650040163 / 16000000000000 : ℚ))
      (s := (465676927526371 / 2500000000000000 : ℚ))
      (q := (5670263729237359 / 20000000000000000 : ℚ))
      (U := (-(6302483216415656992739 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_614_15 :
    Uω (aρ 15) (bρ 15) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_614_16 :
    Uω (aρ 16) (bρ 16) (11406650040163 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_614 :
    Uρ (11406650040163 / 16000000000000 : ℝ) ≤
      (-(5974984503744520764127 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_614_1 U_614_2 U_614_3 U_614_4 U_614_5 U_614_6 U_614_7 U_614_8 U_614_9 U_614_10
    U_614_11 U_614_12 U_614_13 U_614_14 U_614_15 U_614_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_615_1 :
    Uω (aρ 1) (bρ 1) (89520072139 / 125000000000 : ℝ) ≤
      (-(3429008473743938263037 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7097085773560581 / 10000000000000000 : ℝ) ≤
      (-(3429008473743938263037 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7097085773560581 / 10000000000000000 : ℚ))
        (r' := (7097085773560581 / 5000000000000000 : ℚ))
        (U := (-(3429008473743938263037 / 10000000000000000000000 : ℚ)))
        (U' := (3502463329256061736963 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (89520072139 / 125000000000 : ℚ))
      (s := (3548531497043081 / 5000000000000000 : ℚ))
      (q := (7097085773560581 / 10000000000000000 : ℚ))
      (U := (-(3429008473743938263037 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_2 :
    Uω (aρ 2) (bρ 2) (89520072139 / 125000000000 : ℝ) ≤
      (-(432841970319017025881 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14146379095600089 / 20000000000000000 : ℝ) ≤
      (-(432841970319017025881 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (14146379095600089 / 20000000000000000 : ℚ))
        (r' := (14146379095600089 / 10000000000000000 : ℚ))
        (U := (-(432841970319017025881 / 1250000000000000000000 : ℚ)))
        (U' := (433592005055982974119 / 1250000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (89520072139 / 125000000000 : ℚ))
      (s := (7073039555075089 / 10000000000000000 : ℚ))
      (q := (14146379095600089 / 20000000000000000 : ℚ))
      (U := (-(432841970319017025881 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_3 :
    Uω (aρ 3) (bρ 3) (89520072139 / 125000000000 : ℝ) ≤
      (-(882626331049433886807 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7025416911659693 / 10000000000000000 : ℝ) ≤
      (-(882626331049433886807 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7025416911659693 / 10000000000000000 : ℚ))
        (r' := (7025416911659693 / 5000000000000000 : ℚ))
        (U := (-(882626331049433886807 / 2500000000000000000000 : ℚ)))
        (U' := (850241619700566113193 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (89520072139 / 125000000000 : ℚ))
      (s := (3512445194572193 / 5000000000000000 : ℚ))
      (q := (7025416911659693 / 10000000000000000 : ℚ))
      (U := (-(882626331049433886807 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_4 :
    Uω (aρ 4) (bρ 4) (89520072139 / 125000000000 : ℝ) ≤
      (-(728799502219952959019 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13892269331013533 / 20000000000000000 : ℝ) ≤
      (-(728799502219952959019 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13892269331013533 / 20000000000000000 : ℚ))
        (r' := (13892269331013533 / 10000000000000000 : ℚ))
        (U := (-(728799502219952959019 / 2000000000000000000000 : ℚ)))
        (U' := (657494858380047040981 / 2000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (89520072139 / 125000000000 : ℚ))
      (s := (6944620077903533 / 10000000000000000 : ℚ))
      (q := (13892269331013533 / 20000000000000000 : ℚ))
      (U := (-(728799502219952959019 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_5 :
    Uω (aρ 5) (bρ 5) (89520072139 / 125000000000 : ℝ) ≤
      (-(954777473650250097291 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6825558049848699 / 10000000000000000 : ℝ) ≤
      (-(954777473650250097291 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6825558049848699 / 10000000000000000 : ℚ))
        (r' := (6825558049848699 / 5000000000000000 : ℚ))
        (U := (-(954777473650250097291 / 2500000000000000000000 : ℚ)))
        (U' := (778090477099749902709 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (89520072139 / 125000000000 : ℚ))
      (s := (3410828382961199 / 5000000000000000 : ℚ))
      (q := (6825558049848699 / 10000000000000000 : ℚ))
      (U := (-(954777473650250097291 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_6 :
    Uω (aρ 6) (bρ 6) (89520072139 / 125000000000 : ℝ) ≤
      (-(1018794579431653135779 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (532239670118649 / 800000000000000 : ℝ) ≤
      (-(1018794579431653135779 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (532239670118649 / 800000000000000 : ℚ))
        (r' := (532239670118649 / 400000000000000 : ℚ))
        (U := (-(1018794579431653135779 / 2500000000000000000000 : ℚ)))
        (U' := (714073371318346864221 / 2500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (89520072139 / 125000000000 : ℚ))
      (s := (265750911773249 / 400000000000000 : ℚ))
      (q := (532239670118649 / 800000000000000 : ℚ))
      (U := (-(1018794579431653135779 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_7 :
    Uω (aρ 7) (bρ 7) (89520072139 / 125000000000 : ℝ) ≤
      (-(4434234323157178674073 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12836707510689501 / 20000000000000000 : ℝ) ≤
      (-(4434234323157178674073 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12836707510689501 / 20000000000000000 : ℚ))
        (r' := (12836707510689501 / 10000000000000000 : ℚ))
        (U := (-(4434234323157178674073 / 10000000000000000000000 : ℚ)))
        (U' := (2497237479842821325927 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (89520072139 / 125000000000 : ℚ))
      (s := (6398149932814501 / 10000000000000000 : ℚ))
      (q := (12836707510689501 / 20000000000000000 : ℚ))
      (U := (-(4434234323157178674073 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_8 :
    Uω (aρ 8) (bρ 8) (89520072139 / 125000000000 : ℝ) ≤
      (-(307527121787241753561 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12227516690586597 / 20000000000000000 : ℝ) ≤
      (-(307527121787241753561 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12227516690586597 / 20000000000000000 : ℚ))
        (r' := (12227516690586597 / 10000000000000000 : ℚ))
        (U := (-(307527121787241753561 / 625000000000000000000 : ℚ)))
        (U' := (125689865900258246439 / 625000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (89520072139 / 125000000000 : ℚ))
      (s := (6072500764051597 / 10000000000000000 : ℚ))
      (q := (12227516690586597 / 20000000000000000 : ℚ))
      (U := (-(307527121787241753561 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_9 :
    Uω (aρ 9) (bρ 9) (89520072139 / 125000000000 : ℝ) ≤
      (-(5559822753255195245599 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5735086408905213 / 10000000000000000 : ℝ) ≤
      (-(5559822753255195245599 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5735086408905213 / 10000000000000000 : ℚ))
        (r' := (5735086408905213 / 5000000000000000 : ℚ))
        (U := (-(5559822753255195245599 / 10000000000000000000000 : ℚ)))
        (U' := (1371649049744804754401 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (89520072139 / 125000000000 : ℚ))
      (s := (2828061259817713 / 5000000000000000 : ℚ))
      (q := (5735086408905213 / 10000000000000000 : ℚ))
      (U := (-(5559822753255195245599 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_10 :
    Uω (aρ 10) (bρ 10) (89520072139 / 125000000000 : ℝ) ≤
      (-(6380756920479711852741 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10566161476170617 / 20000000000000000 : ℝ) ≤
      (-(6380756920479711852741 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10566161476170617 / 20000000000000000 : ℚ))
        (r' := (10566161476170617 / 10000000000000000 : ℚ))
        (U := (-(6380756920479711852741 / 10000000000000000000000 : ℚ)))
        (U' := (550714882520288147259 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (89520072139 / 125000000000 : ℚ))
      (s := (5140670211490617 / 10000000000000000 : ℚ))
      (q := (10566161476170617 / 20000000000000000 : ℚ))
      (U := (-(6380756920479711852741 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_11 :
    Uω (aρ 11) (bρ 11) (89520072139 / 125000000000 : ℝ) ≤
      (-(1853934321690048881789 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9527273158567701 / 20000000000000000 : ℝ) ≤
      (-(1853934321690048881789 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9527273158567701 / 20000000000000000 : ℚ))
        (r' := (9527273158567701 / 5000000000000000 : ℚ))
        (U := (-(1853934321690048881789 / 2500000000000000000000 : ℚ)))
        (U' := (1611801579809951118211 / 2500000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (89520072139 / 125000000000 : ℚ))
      (s := (4520258520092701 / 10000000000000000 : ℚ))
      (q := (9527273158567701 / 20000000000000000 : ℚ))
      (U := (-(1853934321690048881789 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_12 :
    Uω (aρ 12) (bρ 12) (89520072139 / 125000000000 : ℝ) ≤
      (-(272088004562792016049 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (209333041418471 / 500000000000000 : ℝ) ≤
      (-(272088004562792016049 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (209333041418471 / 500000000000000 : ℚ))
        (r' := (209333041418471 / 125000000000000 : ℚ))
        (U := (-(272088004562792016049 / 312500000000000000000 : ℚ)))
        (U' := (161128983124707983951 / 312500000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (89520072139 / 125000000000 : ℚ))
      (s := (94750177873721 / 250000000000000 : ℚ))
      (q := (209333041418471 / 500000000000000 : ℚ))
      (U := (-(272088004562792016049 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_13 :
    Uω (aρ 13) (bρ 13) (89520072139 / 125000000000 : ℝ) ≤
      (-(5161329804599260628999 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3561989124115103 / 10000000000000000 : ℝ) ≤
      (-(5161329804599260628999 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3561989124115103 / 10000000000000000 : ℚ))
        (r' := (3561989124115103 / 2500000000000000 : ℚ))
        (U := (-(5161329804599260628999 / 5000000000000000000000 : ℚ)))
        (U' := (1770141998400739371001 / 5000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (89520072139 / 125000000000 : ℚ))
      (s := (1470022724017603 / 5000000000000000 : ℚ))
      (q := (3561989124115103 / 10000000000000000 : ℚ))
      (U := (-(5161329804599260628999 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_14 :
    Uω (aρ 14) (bρ 14) (89520072139 / 125000000000 : ℝ) ≤
      (-(6216882226043502495963 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2884087755233591 / 10000000000000000 : ℝ) ≤
      (-(6216882226043502495963 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2884087755233591 / 10000000000000000 : ℚ))
        (r' := (2884087755233591 / 2500000000000000 : ℚ))
        (U := (-(6216882226043502495963 / 5000000000000000000000 : ℚ)))
        (U' := (714589576956497504037 / 5000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (89520072139 / 125000000000 : ℚ))
      (s := (964084997658591 / 5000000000000000 : ℚ))
      (q := (2884087755233591 / 10000000000000000 : ℚ))
      (U := (-(6216882226043502495963 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_615_15 :
    Uω (aρ 15) (bρ 15) (89520072139 / 125000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_615_16 :
    Uω (aρ 16) (bρ 16) (89520072139 / 125000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_615 :
    Uρ (89520072139 / 125000000000 : ℝ) ≤
      (-(5915842076011854104723 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_615_1 U_615_2 U_615_3 U_615_4 U_615_5 U_615_6 U_615_7 U_615_8 U_615_9 U_615_10
    U_615_11 U_615_12 U_615_13 U_615_14 U_615_15 U_615_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
