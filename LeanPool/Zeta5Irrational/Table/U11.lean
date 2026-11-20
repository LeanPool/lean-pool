/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U11) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_136_1 :
    Uω (aρ 1) (bρ 1) (257805414251 / 3200000000000 : ℝ) ≤
      (-(26024389347350076319563 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (296370601810347 / 4000000000000000 : ℝ) ≤
      (-(26024389347350076319563 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (296370601810347 / 4000000000000000 : ℚ))
        (r' := (296370601810347 / 250000000000000 : ℚ))
        (U := (-(26024389347350076319563 / 10000000000000000000000 : ℚ)))
        (U' := (1701497864649923680437 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (257805414251 / 3200000000000 : ℚ))
      (s := (18517707690059 / 250000000000000 : ℚ))
      (q := (296370601810347 / 4000000000000000 : ℚ))
      (U := (-(26024389347350076319563 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_136_2 :
    Uω (aρ 2) (bρ 2) (257805414251 / 3200000000000 : ℝ) ≤
      (-(26368086404189464320953 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1431787454788469 / 20000000000000000 : ℝ) ≤
      (-(26368086404189464320953 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1431787454788469 / 20000000000000000 : ℚ))
        (r' := (1431787454788469 / 1250000000000000 : ℚ))
        (U := (-(26368086404189464320953 / 10000000000000000000000 : ℚ)))
        (U' := (1357800807810535679047 / 10000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (257805414251 / 3200000000000 : ℚ))
      (s := (357205882924547 / 5000000000000000 : ℚ))
      (q := (1431787454788469 / 20000000000000000 : ℚ))
      (U := (-(26368086404189464320953 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_136_3 :
    Uω (aρ 3) (bρ 3) (257805414251 / 3200000000000 : ℝ) ≤
      (-(3389297048001651951123 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (664412195038341 / 10000000000000000 : ℝ) ≤
      (-(3389297048001651951123 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (664412195038341 / 10000000000000000 : ℚ))
        (r' := (664412195038341 / 625000000000000 : ℚ))
        (U := (-(3389297048001651951123 / 1250000000000000000000 : ℚ)))
        (U' := (76438853498348048877 / 1250000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (257805414251 / 3200000000000 : ℚ))
      (s := (658844807487307 / 10000000000000000 : ℚ))
      (q := (664412195038341 / 10000000000000000 : ℚ))
      (U := (-(3389297048001651951123 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_136_4 :
    Uω (aρ 4) (bρ 4) (257805414251 / 3200000000000 : ℝ) ≤
      (-(7147172329350315520741 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1146671434283737 / 20000000000000000 : ℝ) ≤
      (-(7147172329350315520741 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1146671434283737 / 20000000000000000 : ℚ))
        (r' := (1146671434283737 / 625000000000000 : ℚ))
        (U := (-(7147172329350315520741 / 2500000000000000000000 : ℚ)))
        (U' := (1517167424399684479259 / 2500000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (257805414251 / 3200000000000 : ℚ))
      (s := (277493016379681 / 5000000000000000 : ℚ))
      (q := (1146671434283737 / 20000000000000000 : ℚ))
      (U := (-(7147172329350315520741 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_136_5 :
    Uω (aρ 5) (bρ 5) (257805414251 / 3200000000000 : ℝ) ≤
      (-(31984033130623965837531 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2551708774461 / 62500000000000 : ℝ) ≤
      (-(31984033130623965837531 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2551708774461 / 62500000000000 : ℚ))
        (r' := (2551708774461 / 1953125000000 : ℚ))
        (U := (-(31984033130623965837531 / 10000000000000000000000 : ℚ)))
        (U' := (2673325884376034162469 / 10000000000000000000000 : ℚ))
        5 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (257805414251 / 3200000000000 : ℚ))
      (s := (68610265127629 / 2000000000000000 : ℚ))
      (q := (2551708774461 / 62500000000000 : ℚ))
      (U := (-(31984033130623965837531 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_136_6 :
    Uω (aρ 6) (bρ 6) (257805414251 / 3200000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_136_7 :
    Uω (aρ 7) (bρ 7) (257805414251 / 3200000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_136_8 :
    Uω (aρ 8) (bρ 8) (257805414251 / 3200000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_136_9 :
    Uω (aρ 9) (bρ 9) (257805414251 / 3200000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_136_10 :
    Uω (aρ 10) (bρ 10) (257805414251 / 3200000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_136_11 :
    Uω (aρ 11) (bρ 11) (257805414251 / 3200000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_136_12 :
    Uω (aρ 12) (bρ 12) (257805414251 / 3200000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_136_13 :
    Uω (aρ 13) (bρ 13) (257805414251 / 3200000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_136_14 :
    Uω (aρ 14) (bρ 14) (257805414251 / 3200000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_136_15 :
    Uω (aρ 15) (bρ 15) (257805414251 / 3200000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_136_16 :
    Uω (aρ 16) (bρ 16) (257805414251 / 3200000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_136 :
    Uρ (257805414251 / 3200000000000 : ℝ) ≤
      (-(24683602313731326949681 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_136_1 U_136_2 U_136_3 U_136_4 U_136_5 U_136_6 U_136_7 U_136_8 U_136_9 U_136_10
    U_136_11 U_136_12 U_136_13 U_136_14 U_136_15 U_136_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_137_1 :
    Uω (aρ 1) (bρ 1) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(25883504479644690843899 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3005755663550111 / 40000000000000000 : ℝ) ≤
      (-(25883504479644690843899 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3005755663550111 / 40000000000000000 : ℚ))
        (r' := (3005755663550111 / 2500000000000000 : ℚ))
        (U := (-(25883504479644690843899 / 10000000000000000000000 : ℚ)))
        (U' := (1842382732355309156101 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2611684090831 / 32000000000000 : ℚ))
      (s := (93902971434421 / 1250000000000000 : ℚ))
      (q := (3005755663550111 / 40000000000000000 : ℚ))
      (U := (-(25883504479644690843899 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_137_2 :
    Uω (aρ 2) (bρ 2) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(5244411439855569471477 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2905698279867373 / 40000000000000000 : ℝ) ≤
      (-(5244411439855569471477 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2905698279867373 / 40000000000000000 : ℚ))
        (r' := (2905698279867373 / 2500000000000000 : ℚ))
        (U := (-(5244411439855569471477 / 2000000000000000000000 : ℚ)))
        (U' := (300766002544430528523 / 2000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2611684090831 / 32000000000000 : ℚ))
      (s := (724964092143999 / 10000000000000000 : ℚ))
      (q := (2905698279867373 / 40000000000000000 : ℚ))
      (U := (-(5244411439855569471477 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_137_3 :
    Uω (aρ 3) (bρ 3) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(26956144140679057589663 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2700035818426691 / 40000000000000000 : ℝ) ≤
      (-(26956144140679057589663 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2700035818426691 / 40000000000000000 : ℚ))
        (r' := (2700035818426691 / 2500000000000000 : ℚ))
        (U := (-(26956144140679057589663 / 10000000000000000000000 : ℚ)))
        (U' := (769743071320942410337 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2611684090831 / 32000000000000 : ℚ))
      (s := (334764483886829 / 5000000000000000 : ℚ))
      (q := (2700035818426691 / 40000000000000000 : ℚ))
      (U := (-(26956144140679057589663 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_137_4 :
    Uω (aρ 4) (bρ 4) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(1136048455279144140469 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2336743549494169 / 40000000000000000 : ℝ) ≤
      (-(1136048455279144140469 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2336743549494169 / 40000000000000000 : ℚ))
        (r' := (2336743549494169 / 1250000000000000 : ℚ))
        (U := (-(1136048455279144140469 / 400000000000000000000 : ℚ)))
        (U' := (250245905320855859531 / 400000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2611684090831 / 32000000000000 : ℚ))
      (s := (566177014372397 / 10000000000000000 : ℚ))
      (q := (2336743549494169 / 40000000000000000 : ℚ))
      (U := (-(1136048455279144140469 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_137_5 :
    Uω (aρ 5) (bρ 5) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(15841971990601673642843 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (336568744601939 / 8000000000000000 : ℝ) ≤
      (-(15841971990601673642843 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (336568744601939 / 8000000000000000 : ℚ))
        (r' := (336568744601939 / 250000000000000 : ℚ))
        (U := (-(15841971990601673642843 / 5000000000000000000000 : ℚ)))
        (U' := (1486707516898326357157 / 5000000000000000000000 : ℚ))
        5 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2611684090831 / 32000000000000 : ℚ))
      (s := (8935425511629 / 250000000000000 : ℚ))
      (q := (336568744601939 / 8000000000000000 : ℚ))
      (U := (-(15841971990601673642843 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_137_6 :
    Uω (aρ 6) (bρ 6) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_137_7 :
    Uω (aρ 7) (bρ 7) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_137_8 :
    Uω (aρ 8) (bρ 8) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_137_9 :
    Uω (aρ 9) (bρ 9) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_137_10 :
    Uω (aρ 10) (bρ 10) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_137_11 :
    Uω (aρ 11) (bρ 11) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_137_12 :
    Uω (aρ 12) (bρ 12) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_137_13 :
    Uω (aρ 13) (bρ 13) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_137_14 :
    Uω (aρ 14) (bρ 14) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_137_15 :
    Uω (aρ 15) (bρ 15) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_137_16 :
    Uω (aρ 16) (bρ 16) (2611684090831 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_137 :
    Uρ (2611684090831 / 32000000000000 : ℝ) ≤
      (-(12319697019856429271619 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_137_1 U_137_2 U_137_3 U_137_4 U_137_5 U_137_6 U_137_7 U_137_8 U_137_9 U_137_10
    U_137_11 U_137_12 U_137_13 U_137_14 U_137_15 U_137_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_138_1 :
    Uω (aρ 1) (bρ 1) (165332127447 / 2000000000000 : ℝ) ≤
      (-(25744578028657117086197 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (38097562149829 / 500000000000000 : ℝ) ≤
      (-(25744578028657117086197 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (38097562149829 / 500000000000000 : ℚ))
        (r' := (38097562149829 / 31250000000000 : ℚ))
        (U := (-(25744578028657117086197 / 10000000000000000000000 : ℚ)))
        (U' := (1981309183342882913803 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (165332127447 / 2000000000000 : ℚ))
      (s := (19043476671079 / 250000000000000 : ℚ))
      (q := (38097562149829 / 500000000000000 : ℚ))
      (U := (-(25744578028657117086197 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_138_2 :
    Uω (aρ 2) (bρ 2) (165332127447 / 2000000000000 : ℝ) ≤
      (-(3259767267427656465799 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1473909594695023 / 20000000000000000 : ℝ) ≤
      (-(3259767267427656465799 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1473909594695023 / 20000000000000000 : ℚ))
        (r' := (1473909594695023 / 1250000000000000 : ℚ))
        (U := (-(3259767267427656465799 / 1250000000000000000000 : ℚ)))
        (U' := (205968634072343534201 / 1250000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (165332127447 / 2000000000000 : ℚ))
      (s := (735515188055023 / 10000000000000000 : ℚ))
      (q := (1473909594695023 / 20000000000000000 : ℚ))
      (U := (-(3259767267427656465799 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_138_3 :
    Uω (aρ 3) (bρ 3) (165332127447 / 2000000000000 : ℝ) ≤
      (-(3350052051316778232639 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (685602991004679 / 10000000000000000 : ℝ) ≤
      (-(3350052051316778232639 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (685602991004679 / 10000000000000000 : ℚ))
        (r' := (685602991004679 / 625000000000000 : ℚ))
        (U := (-(3350052051316778232639 / 1250000000000000000000 : ℚ)))
        (U' := (115683850183221767361 / 1250000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (165332127447 / 2000000000000 : ℚ))
      (s := (340103840859679 / 5000000000000000 : ℚ))
      (q := (685602991004679 / 10000000000000000 : ℚ))
      (U := (-(3350052051316778232639 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_138_4 :
    Uω (aρ 4) (bρ 4) (165332127447 / 2000000000000 : ℝ) ≤
      (-(14108699468577326473109 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (297511623973151 / 5000000000000000 : ℝ) ≤
      (-(14108699468577326473109 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (297511623973151 / 5000000000000000 : ℚ))
        (r' := (297511623973151 / 156250000000000 : ℚ))
        (U := (-(14108699468577326473109 / 5000000000000000000000 : ℚ)))
        (U' := (3219980038922673526891 / 5000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (165332127447 / 2000000000000 : ℚ))
      (s := (144335594166901 / 2500000000000000 : ℚ))
      (q := (297511623973151 / 5000000000000000 : ℚ))
      (U := (-(14108699468577326473109 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_138_5 :
    Uω (aρ 5) (bρ 5) (165332127447 / 2000000000000 : ℝ) ≤
      (-(627911566201869230741 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (34641552310843 / 800000000000000 : ℝ) ≤
      (-(627911566201869230741 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (34641552310843 / 800000000000000 : ℚ))
        (r' := (34641552310843 / 25000000000000 : ℚ))
        (U := (-(627911566201869230741 / 200000000000000000000 : ℚ)))
        (U' := (65235614098130769259 / 200000000000000000000 : ℚ))
        5 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (165332127447 / 2000000000000 : ℚ))
      (s := (14860984315243 / 400000000000000 : ℚ))
      (q := (34641552310843 / 800000000000000 : ℚ))
      (U := (-(627911566201869230741 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_138_6 :
    Uω (aρ 6) (bρ 6) (165332127447 / 2000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_138_7 :
    Uω (aρ 7) (bρ 7) (165332127447 / 2000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_138_8 :
    Uω (aρ 8) (bρ 8) (165332127447 / 2000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_138_9 :
    Uω (aρ 9) (bρ 9) (165332127447 / 2000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_138_10 :
    Uω (aρ 10) (bρ 10) (165332127447 / 2000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_138_11 :
    Uω (aρ 11) (bρ 11) (165332127447 / 2000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_138_12 :
    Uω (aρ 12) (bρ 12) (165332127447 / 2000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_138_13 :
    Uω (aρ 13) (bρ 13) (165332127447 / 2000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_138_14 :
    Uω (aρ 14) (bρ 14) (165332127447 / 2000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_138_15 :
    Uω (aρ 15) (bρ 15) (165332127447 / 2000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_138_16 :
    Uω (aρ 16) (bρ 16) (165332127447 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_138 :
    Uρ (165332127447 / 2000000000000 : ℝ) ≤
      (-(4919279757412061629749 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_138_1 U_138_2 U_138_3 U_138_4 U_138_5 U_138_6 U_138_7 U_138_8 U_138_9 U_138_10
    U_138_11 U_138_12 U_138_13 U_138_14 U_138_15 U_138_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_139_1 :
    Uω (aρ 1) (bρ 1) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(25607556263304084967409 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3089853957178669 / 40000000000000000 : ℝ) ≤
      (-(25607556263304084967409 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3089853957178669 / 40000000000000000 : ℚ))
        (r' := (3089853957178669 / 2500000000000000 : ℚ))
        (U := (-(25607556263304084967409 / 10000000000000000000000 : ℚ)))
        (U' := (2118330948695915032591 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2678943987473 / 32000000000000 : ℚ))
      (s := (386127100294511 / 5000000000000000 : ℚ))
      (q := (3089853957178669 / 40000000000000000 : ℚ))
      (U := (-(25607556263304084967409 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_139_2 :
    Uω (aρ 2) (bρ 2) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(3242033609723343368109 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (597987548509579 / 8000000000000000 : ℝ) ≤
      (-(3242033609723343368109 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (597987548509579 / 8000000000000000 : ℚ))
        (r' := (597987548509579 / 500000000000000 : ℚ))
        (U := (-(3242033609723343368109 / 1250000000000000000000 : ℚ)))
        (U' := (223702291776656631891 / 1250000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2678943987473 / 32000000000000 : ℚ))
      (s := (149213021156727 / 2000000000000000 : ℚ))
      (q := (597987548509579 / 8000000000000000 : ℚ))
      (U := (-(3242033609723343368109 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_139_3 :
    Uω (aρ 3) (bρ 3) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(5329422790878437414709 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2784777722022853 / 40000000000000000 : ℝ) ≤
      (-(5329422790878437414709 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2784777722022853 / 40000000000000000 : ℚ))
        (r' := (2784777722022853 / 2500000000000000 : ℚ))
        (U := (-(5329422790878437414709 / 2000000000000000000000 : ℚ)))
        (U' := (215754651521562585291 / 2000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2678943987473 / 32000000000000 : ℚ))
      (s := (345440600935557 / 5000000000000000 : ℚ))
      (q := (2784777722022853 / 40000000000000000 : ℚ))
      (U := (-(5329422790878437414709 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_139_4 :
    Uω (aρ 4) (bρ 4) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(350463796210277297691 / 125000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2423394111912659 / 40000000000000000 : ℝ) ≤
      (-(350463796210277297691 / 125000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2423394111912659 / 40000000000000000 : ℚ))
        (r' := (2423394111912659 / 1250000000000000 : ℚ))
        (U := (-(350463796210277297691 / 125000000000000000000 : ℚ)))
        (U' := (82753191477222702309 / 125000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2678943987473 / 32000000000000 : ℚ))
      (s := (588483577881017 / 10000000000000000 : ℚ))
      (q := (2423394111912659 / 40000000000000000 : ℚ))
      (U := (-(350463796210277297691 / 125000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_139_5 :
    Uω (aρ 5) (bρ 5) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(15558937803900991527783 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (356170396638393 / 8000000000000000 : ℝ) ≤
      (-(15558937803900991527783 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (356170396638393 / 8000000000000000 : ℚ))
        (r' := (356170396638393 / 250000000000000 : ℚ))
        (U := (-(15558937803900991527783 / 5000000000000000000000 : ℚ)))
        (U' := (1769741703599008472217 / 5000000000000000000000 : ℚ))
        5 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2678943987473 / 32000000000000 : ℚ))
      (s := (38540243285567 / 1000000000000000 : ℚ))
      (q := (356170396638393 / 8000000000000000 : ℚ))
      (U := (-(15558937803900991527783 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_139_6 :
    Uω (aρ 6) (bρ 6) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_139_7 :
    Uω (aρ 7) (bρ 7) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_139_8 :
    Uω (aρ 8) (bρ 8) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_139_9 :
    Uω (aρ 9) (bρ 9) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_139_10 :
    Uω (aρ 10) (bρ 10) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_139_11 :
    Uω (aρ 11) (bρ 11) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_139_12 :
    Uω (aρ 12) (bρ 12) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_139_13 :
    Uω (aρ 13) (bρ 13) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_139_14 :
    Uω (aρ 14) (bρ 14) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_139_15 :
    Uω (aρ 15) (bρ 15) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_139_16 :
    Uω (aρ 16) (bρ 16) (2678943987473 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_139 :
    Uρ (2678943987473 / 32000000000000 : ℝ) ≤
      (-(3069316120527173883389 / 1250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_139_1 U_139_2 U_139_3 U_139_4 U_139_5 U_139_6 U_139_7 U_139_8 U_139_9 U_139_10
    U_139_11 U_139_12 U_139_13 U_139_14 U_139_15 U_139_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_140_1 :
    Uω (aρ 1) (bρ 1) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(25472387635023400139573 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1565951316076903 / 20000000000000000 : ℝ) ≤
      (-(25472387635023400139573 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1565951316076903 / 20000000000000000 : ℚ))
        (r' := (1565951316076903 / 1250000000000000 : ℚ))
        (U := (-(25472387635023400139573 / 10000000000000000000000 : ℚ)))
        (U' := (2253499576976599860427 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1356286967897 / 16000000000000 : ℚ))
      (s := (391384589613139 / 5000000000000000 : ℚ))
      (q := (1565951316076903 / 20000000000000000 : ℚ))
      (U := (-(25472387635023400139573 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_140_2 :
    Uω (aρ 2) (bρ 2) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(12898195814616624135193 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1516027018954759 / 20000000000000000 : ℝ) ≤
      (-(12898195814616624135193 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1516027018954759 / 20000000000000000 : ℚ))
        (r' := (1516027018954759 / 1250000000000000 : ℚ))
        (U := (-(12898195814616624135193 / 5000000000000000000000 : ℚ)))
        (U' := (964747791383375864807 / 5000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1356286967897 / 16000000000000 : ℚ))
      (s := (378306947307067 / 5000000000000000 : ℚ))
      (q := (1516027018954759 / 20000000000000000 : ℚ))
      (U := (-(12898195814616624135193 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_140_3 :
    Uω (aρ 3) (bρ 3) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(26496161287310828503139 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (141356678327789 / 2000000000000000 : ℝ) ≤
      (-(26496161287310828503139 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (141356678327789 / 2000000000000000 : ℚ))
        (r' := (141356678327789 / 125000000000000 : ℚ))
        (U := (-(26496161287310828503139 / 10000000000000000000000 : ℚ)))
        (U' := (1229725924689171496861 / 10000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1356286967897 / 16000000000000 : ℚ))
      (s := (140309953057453 / 2000000000000000 : ℚ))
      (q := (141356678327789 / 2000000000000000 : ℚ))
      (U := (-(26496161287310828503139 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_140_4 :
    Uω (aρ 4) (bρ 4) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(217657707718408659519 / 78125000000000000000 : ℝ)) := by
  have hlg :
    Real.log (246664960350121 / 4000000000000000 : ℝ) ≤
      (-(217657707718408659519 / 78125000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (246664960350121 / 4000000000000000 : ℚ))
        (r' := (246664960350121 / 125000000000000 : ℚ))
        (U := (-(217657707718408659519 / 78125000000000000000 : ℚ)))
        (U' := (53102909586278840481 / 78125000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1356286967897 / 16000000000000 : ℚ))
      (s := (29980098241249 / 500000000000000 : ℚ))
      (q := (246664960350121 / 4000000000000000 : ℚ))
      (U := (-(217657707718408659519 / 78125000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_140_5 :
    Uω (aρ 5) (bρ 5) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(30849926669156202687773 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (457303691842081 / 10000000000000000 : ℝ) ≤
      (-(30849926669156202687773 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (457303691842081 / 10000000000000000 : ℚ))
        (r' := (457303691842081 / 312500000000000 : ℚ))
        (U := (-(30849926669156202687773 / 10000000000000000000000 : ℚ)))
        (U' := (3807432345843797312227 / 10000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1356286967897 / 16000000000000 : ℚ))
      (s := (399074466093537 / 10000000000000000 : ℚ))
      (q := (457303691842081 / 10000000000000000 : ℚ))
      (U := (-(30849926669156202687773 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_140_6 :
    Uω (aρ 6) (bρ 6) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_140_7 :
    Uω (aρ 7) (bρ 7) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_140_8 :
    Uω (aρ 8) (bρ 8) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_140_9 :
    Uω (aρ 9) (bρ 9) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_140_10 :
    Uω (aρ 10) (bρ 10) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_140_11 :
    Uω (aρ 11) (bρ 11) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_140_12 :
    Uω (aρ 12) (bρ 12) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_140_13 :
    Uω (aρ 13) (bρ 13) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_140_14 :
    Uω (aρ 14) (bρ 14) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_140_15 :
    Uω (aρ 15) (bρ 15) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_140_16 :
    Uω (aρ 16) (bρ 16) (1356286967897 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_140 :
    Uρ (1356286967897 / 16000000000000 : ℝ) ≤
      (-(12256854110596322856331 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_140_1 U_140_2 U_140_3 U_140_4 U_140_5 U_140_6 U_140_7 U_140_8 U_140_9 U_140_10
    U_140_11 U_140_12 U_140_13 U_140_14 U_140_15 U_140_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_141_1 :
    Uω (aρ 1) (bρ 1) (694958458109 / 8000000000000 : ℝ) ≤
      (-(1260370690780799325851 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (200999943759371 / 2500000000000000 : ℝ) ≤
      (-(1260370690780799325851 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (200999943759371 / 2500000000000000 : ℚ))
        (r' := (200999943759371 / 156250000000000 : ℚ))
        (U := (-(1260370690780799325851 / 500000000000000000000 : ℚ)))
        (U' := (125923669819200674149 / 500000000000000000000 : ℚ))
        4 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (694958458109 / 8000000000000 : ℚ))
      (s := (401899347761859 / 5000000000000000 : ℚ))
      (q := (200999943759371 / 2500000000000000 : ℚ))
      (U := (-(1260370690780799325851 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_141_2 :
    Uω (aρ 2) (bρ 2) (694958458109 / 8000000000000 : ℝ) ≤
      (-(3190299248545577399671 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1558140111364829 / 20000000000000000 : ℝ) ≤
      (-(3190299248545577399671 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1558140111364829 / 20000000000000000 : ℚ))
        (r' := (1558140111364829 / 1250000000000000 : ℚ))
        (U := (-(3190299248545577399671 / 1250000000000000000000 : ℚ)))
        (U' := (275436652954422600329 / 1250000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (694958458109 / 8000000000000 : ℚ))
      (s := (777708269323579 / 10000000000000000 : ℚ))
      (q := (1558140111364829 / 20000000000000000 : ℚ))
      (U := (-(3190299248545577399671 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_141_3 :
    Uω (aρ 3) (bρ 3) (694958458109 / 8000000000000 : ℝ) ≤
      (-(3275127593940399875157 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (727954317676977 / 10000000000000000 : ℝ) ≤
      (-(3275127593940399875157 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (727954317676977 / 10000000000000000 : ℚ))
        (r' := (727954317676977 / 625000000000000 : ℚ))
        (U := (-(3275127593940399875157 / 1250000000000000000000 : ℚ)))
        (U' := (190608307559600124843 / 1250000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (694958458109 / 8000000000000 : ℚ))
      (s := (45179556228919 / 625000000000000 : ℚ))
      (q := (727954317676977 / 10000000000000000 : ℚ))
      (U := (-(3275127593940399875157 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_141_4 :
    Uω (aρ 4) (bρ 4) (694958458109 / 8000000000000 : ℝ) ≤
      (-(13757985990762632792871 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (319129185882303 / 5000000000000000 : ℝ) ≤
      (-(13757985990762632792871 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (319129185882303 / 5000000000000000 : ℚ))
        (r' := (319129185882303 / 312500000000000 : ℚ))
        (U := (-(13757985990762632792871 / 5000000000000000000000 : ℚ)))
        (U' := (104957615237367207129 / 5000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (694958458109 / 8000000000000 : ℚ))
      (s := (310887594451481 / 5000000000000000 : ℚ))
      (q := (319129185882303 / 5000000000000000 : ℚ))
      (U := (-(13757985990762632792871 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_141_5 :
    Uω (aρ 5) (bρ 5) (694958458109 / 8000000000000 : ℝ) ≤
      (-(30340243654537166784837 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (240607945013181 / 5000000000000000 : ℝ) ≤
      (-(30340243654537166784837 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (240607945013181 / 5000000000000000 : ℚ))
        (r' := (240607945013181 / 156250000000000 : ℚ))
        (U := (-(30340243654537166784837 / 10000000000000000000000 : ℚ)))
        (U' := (4317115360462833215163 / 10000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (694958458109 / 8000000000000 : ℚ))
      (s := (212940072380737 / 5000000000000000 : ℚ))
      (q := (240607945013181 / 5000000000000000 : ℚ))
      (U := (-(30340243654537166784837 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_141_6 :
    Uω (aρ 6) (bρ 6) (694958458109 / 8000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_141_7 :
    Uω (aρ 7) (bρ 7) (694958458109 / 8000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_141_8 :
    Uω (aρ 8) (bρ 8) (694958458109 / 8000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_141_9 :
    Uω (aρ 9) (bρ 9) (694958458109 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_141_10 :
    Uω (aρ 10) (bρ 10) (694958458109 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_141_11 :
    Uω (aρ 11) (bρ 11) (694958458109 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_141_12 :
    Uω (aρ 12) (bρ 12) (694958458109 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_141_13 :
    Uω (aρ 13) (bρ 13) (694958458109 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_141_14 :
    Uω (aρ 14) (bρ 14) (694958458109 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_141_15 :
    Uω (aρ 15) (bρ 15) (694958458109 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_141_16 :
    Uω (aρ 16) (bρ 16) (694958458109 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_141 :
    Uρ (694958458109 / 8000000000000 : ℝ) ≤
      (-(24434952955612677719747 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_141_1 U_141_2 U_141_3 U_141_4 U_141_5 U_141_6 U_141_7 U_141_8 U_141_9 U_141_10
    U_141_11 U_141_12 U_141_13 U_141_14 U_141_15 U_141_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_142_1 :
    Uω (aρ 1) (bρ 1) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(3118660448249061296987 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1650047233580129 / 20000000000000000 : ℝ) ≤
      (-(3118660448249061296987 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1650047233580129 / 20000000000000000 : ℚ))
        (r' := (1650047233580129 / 1250000000000000 : ℚ))
        (U := (-(3118660448249061296987 / 1250000000000000000000 : ℚ)))
        (U' := (347075453250938703013 / 1250000000000000000000 : ℚ))
        4 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1423546864539 / 16000000000000 : ℚ))
      (s := (412413830664127 / 5000000000000000 : ℚ))
      (q := (1650047233580129 / 20000000000000000 : ℚ))
      (U := (-(3118660448249061296987 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_142_2 :
    Uω (aρ 2) (bρ 2) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(12627864479779576637511 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (800124607553441 / 10000000000000000 : ℝ) ≤
      (-(12627864479779576637511 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (800124607553441 / 10000000000000000 : ℚ))
        (r' := (800124607553441 / 625000000000000 : ℚ))
        (U := (-(12627864479779576637511 / 5000000000000000000000 : ℚ)))
        (U' := (1235079126220423362489 / 5000000000000000000000 : ℚ))
        4 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1423546864539 / 16000000000000 : ℚ))
      (s := (798798655365007 / 10000000000000000 : ℚ))
      (q := (800124607553441 / 10000000000000000 : ℚ))
      (U := (-(12627864479779576637511 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_142_3 :
    Uω (aρ 3) (bρ 3) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(25914457472574753600061 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1498233167106849 / 20000000000000000 : ℝ) ≤
      (-(25914457472574753600061 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1498233167106849 / 20000000000000000 : ℚ))
        (r' := (1498233167106849 / 1250000000000000 : ℚ))
        (U := (-(25914457472574753600061 / 10000000000000000000000 : ℚ)))
        (U' := (1811429739425246399939 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1423546864539 / 16000000000000 : ℚ))
      (s := (372089356857487 / 5000000000000000 : ℚ))
      (q := (1498233167106849 / 20000000000000000 : ℚ))
      (U := (-(25914457472574753600061 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_142_4 :
    Uω (aρ 4) (bρ 4) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(217470394859432947223 / 80000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (659815621873 / 10000000000000 : ℝ) ≤
      (-(217470394859432947223 / 80000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (659815621873 / 10000000000000 : ℚ))
        (r' := (659815621873 / 625000000000 : ℚ))
        (U := (-(217470394859432947223 / 80000000000000000000 : ℚ)))
        (U' := (4336702836567052777 / 80000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1423546864539 / 16000000000000 : ℚ))
      (s := (5150967771353 / 80000000000000 : ℚ))
      (q := (659815621873 / 10000000000000 : ℚ))
      (U := (-(217470394859432947223 / 80000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_142_5 :
    Uω (aρ 5) (bρ 5) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(7465335220405714049317 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (252411098596889 / 5000000000000000 : ℝ) ≤
      (-(7465335220405714049317 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (252411098596889 / 5000000000000000 : ℚ))
        (r' := (252411098596889 / 156250000000000 : ℚ))
        (U := (-(7465335220405714049317 / 2500000000000000000000 : ℚ)))
        (U' := (1199004533344285950683 / 2500000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1423546864539 / 16000000000000 : ℚ))
      (s := (452074041395681 / 10000000000000000 : ℚ))
      (q := (252411098596889 / 5000000000000000 : ℚ))
      (U := (-(7465335220405714049317 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_142_6 :
    Uω (aρ 6) (bρ 6) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_142_7 :
    Uω (aρ 7) (bρ 7) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_142_8 :
    Uω (aρ 8) (bρ 8) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_142_9 :
    Uω (aρ 9) (bρ 9) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_142_10 :
    Uω (aρ 10) (bρ 10) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_142_11 :
    Uω (aρ 11) (bρ 11) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_142_12 :
    Uω (aρ 12) (bρ 12) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_142_13 :
    Uω (aρ 13) (bρ 13) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_142_14 :
    Uω (aρ 14) (bρ 14) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_142_15 :
    Uω (aρ 15) (bρ 15) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_142_16 :
    Uω (aρ 16) (bρ 16) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_142 :
    Uρ (1423546864539 / 16000000000000 : ℝ) ≤
      (-(12179839953679917785211 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_142_1 U_142_2 U_142_3 U_142_4 U_142_5 U_142_6 U_142_7 U_142_8 U_142_9 U_142_10
    U_142_11 U_142_12 U_142_13 U_142_14 U_142_15 U_142_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_143_1 :
    Uω (aρ 1) (bρ 1) (72858840643 / 800000000000 : ℝ) ≤
      (-(4939530432806504756481 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (423023601912517 / 5000000000000000 : ℝ) ≤
      (-(4939530432806504756481 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (423023601912517 / 5000000000000000 : ℚ))
        (r' := (423023601912517 / 312500000000000 : ℚ))
        (U := (-(4939530432806504756481 / 2000000000000000000000 : ℚ)))
        (U' := (605647009593495243519 / 2000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (72858840643 / 800000000000 : ℚ))
      (s := (26433003678049 / 312500000000000 : ℚ))
      (q := (423023601912517 / 5000000000000000 : ℚ))
      (U := (-(4939530432806504756481 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_143_2 :
    Uω (aρ 2) (bρ 2) (72858840643 / 800000000000 : ℝ) ≤
      (-(12498006527585179078093 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (410588659497357 / 5000000000000000 : ℝ) ≤
      (-(12498006527585179078093 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (410588659497357 / 5000000000000000 : ℚ))
        (r' := (410588659497357 / 312500000000000 : ℚ))
        (U := (-(12498006527585179078093 / 5000000000000000000000 : ℚ)))
        (U' := (1364937078414820921907 / 5000000000000000000000 : ℚ))
        4 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (72858840643 / 800000000000 : ℚ))
      (s := (51242835034183 / 625000000000000 : ℚ))
      (q := (410588659497357 / 5000000000000000 : ℚ))
      (U := (-(12498006527585179078093 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_143_3 :
    Uω (aρ 3) (bρ 3) (72858840643 / 800000000000 : ℝ) ≤
      (-(25635980836800211611331 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1540541824803243 / 20000000000000000 : ℝ) ≤
      (-(25635980836800211611331 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1540541824803243 / 20000000000000000 : ℚ))
        (r' := (1540541824803243 / 1250000000000000 : ℚ))
        (U := (-(25635980836800211611331 / 10000000000000000000000 : ℚ)))
        (U' := (2089906375199788388669 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (72858840643 / 800000000000 : ℚ))
      (s := (765468653710743 / 10000000000000000 : ℚ))
      (q := (1540541824803243 / 20000000000000000 : ℚ))
      (U := (-(25635980836800211611331 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_143_4 :
    Uω (aρ 4) (bρ 4) (72858840643 / 800000000000 : ℝ) ≤
      (-(26862818505948193076349 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1362676011438963 / 20000000000000000 : ℝ) ≤
      (-(26862818505948193076349 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1362676011438963 / 20000000000000000 : ℚ))
        (r' := (1362676011438963 / 1250000000000000 : ℚ))
        (U := (-(26862818505948193076349 / 10000000000000000000000 : ℚ)))
        (U' := (863068706051806923651 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (72858840643 / 800000000000 : ℚ))
      (s := (665897021411463 / 10000000000000000 : ℚ))
      (q := (1362676011438963 / 20000000000000000 : ℚ))
      (U := (-(26862818505948193076349 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_143_5 :
    Uω (aρ 5) (bρ 5) (72858840643 / 800000000000 : ℝ) ≤
      (-(3676145772901062746707 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1056345863520347 / 20000000000000000 : ℝ) ≤
      (-(3676145772901062746707 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1056345863520347 / 20000000000000000 : ℚ))
        (r' := (1056345863520347 / 625000000000000 : ℚ))
        (U := (-(3676145772901062746707 / 1250000000000000000000 : ℚ)))
        (U' := (656024103973937253293 / 1250000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (72858840643 / 800000000000 : ℚ))
      (s := (477756792827847 / 10000000000000000 : ℚ))
      (q := (1056345863520347 / 20000000000000000 : ℚ))
      (U := (-(3676145772901062746707 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_143_6 :
    Uω (aρ 6) (bρ 6) (72858840643 / 800000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_143_7 :
    Uω (aρ 7) (bρ 7) (72858840643 / 800000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_143_8 :
    Uω (aρ 8) (bρ 8) (72858840643 / 800000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_143_9 :
    Uω (aρ 9) (bρ 9) (72858840643 / 800000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_143_10 :
    Uω (aρ 10) (bρ 10) (72858840643 / 800000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_143_11 :
    Uω (aρ 11) (bρ 11) (72858840643 / 800000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_143_12 :
    Uω (aρ 12) (bρ 12) (72858840643 / 800000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_143_13 :
    Uω (aρ 13) (bρ 13) (72858840643 / 800000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_143_14 :
    Uω (aρ 14) (bρ 14) (72858840643 / 800000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_143_15 :
    Uω (aρ 15) (bρ 15) (72858840643 / 800000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_143_16 :
    Uω (aρ 16) (bρ 16) (72858840643 / 800000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_143 :
    Uρ (72858840643 / 800000000000 : ℝ) ≤ (-(189746280053298967991 / 78125000000000000000 : ℝ)) :=
  by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (72858840643 / 800000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(4939530432806504756481 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (72858840643 / 800000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(12498006527585179078093 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (72858840643 / 800000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(25635980836800211611331 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (72858840643 / 800000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(26862818505948193076349 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (72858840643 / 800000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(3676145772901062746707 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (72858840643 / 800000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (72858840643 / 800000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (72858840643 / 800000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (72858840643 / 800000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (72858840643 / 800000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (72858840643 / 800000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (72858840643 / 800000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (72858840643 / 800000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (72858840643 / 800000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (72858840643 / 800000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (72858840643 / 800000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_143_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_144_1 :
    Uω (aρ 1) (bρ 1) (762218354751 / 8000000000000 : ℝ) ≤
      (-(24212631311087841507319 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1776187372263171 / 20000000000000000 : ℝ) ≤
      (-(24212631311087841507319 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1776187372263171 / 20000000000000000 : ℚ))
        (r' := (1776187372263171 / 1250000000000000 : ℚ))
        (U := (-(24212631311087841507319 / 10000000000000000000000 : ℚ)))
        (U' := (3513255900912158492681 / 10000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (762218354751 / 8000000000000 : ℚ))
      (s := (887911646909421 / 10000000000000000 : ℚ))
      (q := (1776187372263171 / 20000000000000000 : ℚ))
      (U := (-(24212631311087841507319 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_144_2 :
    Uω (aρ 2) (bρ 2) (762218354751 / 8000000000000 : ℝ) ≤
      (-(24496038767204679231087 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (431638880396551 / 5000000000000000 : ℝ) ≤
      (-(24496038767204679231087 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (431638880396551 / 5000000000000000 : ℚ))
        (r' := (431638880396551 / 312500000000000 : ℚ))
        (U := (-(24496038767204679231087 / 10000000000000000000000 : ℚ)))
        (U' := (3229848444795320768913 / 10000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (762218354751 / 8000000000000 : ℚ))
      (s := (431024404371227 / 5000000000000000 : ℚ))
      (q := (431638880396551 / 5000000000000000 : ℚ))
      (U := (-(24496038767204679231087 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_144_3 :
    Uω (aρ 3) (bρ 3) (762218354751 / 8000000000000 : ℝ) ≤
      (-(25101527446924252214789 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (406279134060903 / 5000000000000000 : ℝ) ≤
      (-(25101527446924252214789 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (406279134060903 / 5000000000000000 : ℚ))
        (r' := (406279134060903 / 312500000000000 : ℚ))
        (U := (-(25101527446924252214789 / 10000000000000000000000 : ℚ)))
        (U' := (2624359765075747785211 / 10000000000000000000000 : ℚ))
        4 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (762218354751 / 8000000000000 : ℚ))
      (s := (404002964874931 / 5000000000000000 : ℚ))
      (q := (406279134060903 / 5000000000000000 : ℚ))
      (U := (-(25101527446924252214789 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_144_4 :
    Uω (aρ 4) (bρ 4) (762218354751 / 8000000000000 : ℝ) ≤
      (-(13125734602345873881497 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1448582297152821 / 20000000000000000 : ℝ) ≤
      (-(13125734602345873881497 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1448582297152821 / 20000000000000000 : ℚ))
        (r' := (1448582297152821 / 1250000000000000 : ℚ))
        (U := (-(13125734602345873881497 / 5000000000000000000000 : ℚ)))
        (U' := (737209003654126118503 / 5000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (762218354751 / 8000000000000 : ℚ))
      (s := (709765871724071 / 10000000000000000 : ℚ))
      (q := (1448582297152821 / 20000000000000000 : ℚ))
      (U := (-(13125734602345873881497 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_144_5 :
    Uω (aρ 5) (bρ 5) (762218354751 / 8000000000000 : ℝ) ≤
      (-(28572647461235244444859 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1148512384323577 / 20000000000000000 : ℝ) ≤
      (-(28572647461235244444859 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1148512384323577 / 20000000000000000 : ℚ))
        (r' := (1148512384323577 / 625000000000000 : ℚ))
        (U := (-(28572647461235244444859 / 10000000000000000000000 : ℚ)))
        (U' := (6084711553764755555141 / 10000000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (762218354751 / 8000000000000 : ℚ))
      (s := (527885878229827 / 10000000000000000 : ℚ))
      (q := (1148512384323577 / 20000000000000000 : ℚ))
      (U := (-(28572647461235244444859 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_144_6 :
    Uω (aρ 6) (bρ 6) (762218354751 / 8000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_144_7 :
    Uω (aρ 7) (bρ 7) (762218354751 / 8000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_144_8 :
    Uω (aρ 8) (bρ 8) (762218354751 / 8000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_144_9 :
    Uω (aρ 9) (bρ 9) (762218354751 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_144_10 :
    Uω (aρ 10) (bρ 10) (762218354751 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_144_11 :
    Uω (aρ 11) (bρ 11) (762218354751 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_144_12 :
    Uω (aρ 12) (bρ 12) (762218354751 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_144_13 :
    Uω (aρ 13) (bρ 13) (762218354751 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_144_14 :
    Uω (aρ 14) (bρ 14) (762218354751 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_144_15 :
    Uω (aρ 15) (bρ 15) (762218354751 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_144_16 :
    Uω (aρ 16) (bρ 16) (762218354751 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_144 :
    Uρ (762218354751 / 8000000000000 : ℝ) ≤
      (-(6037851914004356594239 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_144_1 U_144_2 U_144_3 U_144_4 U_144_5 U_144_6 U_144_7 U_144_8 U_144_9 U_144_10
    U_144_11 U_144_12 U_144_13 U_144_14 U_144_15 U_144_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_145_1 :
    Uω (aρ 1) (bρ 1) (24870259471 / 250000000000 : ℝ) ≤
      (-(5937514892280973947171 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1860278700728729 / 20000000000000000 : ℝ) ≤
      (-(5937514892280973947171 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1860278700728729 / 20000000000000000 : ℚ))
        (r' := (1860278700728729 / 1250000000000000 : ℚ))
        (U := (-(5937514892280973947171 / 2500000000000000000000 : ℚ)))
        (U' := (993956910719026052829 / 2500000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (24870259471 / 250000000000 : ℚ))
      (s := (929965539973729 / 10000000000000000 : ℚ))
      (q := (1860278700728729 / 20000000000000000 : ℚ))
      (U := (-(5937514892280973947171 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_145_2 :
    Uω (aρ 2) (bρ 2) (24870259471 / 250000000000 : ℝ) ≤
      (-(24019940915667638914899 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (181074467070649 / 2000000000000000 : ℝ) ≤
      (-(24019940915667638914899 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (181074467070649 / 2000000000000000 : ℚ))
        (r' := (181074467070649 / 125000000000000 : ℚ))
        (U := (-(24019940915667638914899 / 10000000000000000000000 : ℚ)))
        (U' := (3705946296332361085101 / 10000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (24870259471 / 250000000000 : ℚ))
      (s := (90420052246149 / 1000000000000000 : ℚ))
      (q := (181074467070649 / 2000000000000000 : ℚ))
      (U := (-(24019940915667638914899 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_145_3 :
    Uω (aρ 3) (bρ 3) (24870259471 / 250000000000 : ℝ) ≤
      (-(12297242736766437788551 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1709641544020893 / 20000000000000000 : ℝ) ≤
      (-(12297242736766437788551 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1709641544020893 / 20000000000000000 : ℚ))
        (r' := (1709641544020893 / 1250000000000000 : ℚ))
        (U := (-(12297242736766437788551 / 5000000000000000000000 : ℚ)))
        (U' := (1565700869233562211449 / 5000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (24870259471 / 250000000000 : ℚ))
      (s := (850493502125893 / 10000000000000000 : ℚ))
      (q := (1709641544020893 / 20000000000000000 : ℚ))
      (U := (-(12297242736766437788551 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_145_4 :
    Uω (aρ 4) (bρ 4) (24870259471 / 250000000000 : ℝ) ≤
      (-(25676711922883085692547 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (95892487016369 / 1250000000000000 : ℝ) ≤
      (-(25676711922883085692547 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (95892487016369 / 1250000000000000 : ℚ))
        (r' := (95892487016369 / 78125000000000 : ℚ))
        (U := (-(25676711922883085692547 / 10000000000000000000000 : ℚ)))
        (U' := (2049175289116914307453 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (24870259471 / 250000000000 : ℚ))
      (s := (23544560357247 / 312500000000000 : ℚ))
      (q := (95892487016369 / 1250000000000000 : ℚ))
      (U := (-(25676711922883085692547 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_145_5 :
    Uω (aρ 5) (bρ 5) (24870259471 / 250000000000 : ℝ) ≤
      (-(13905575961864639085561 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (123938721978887 / 2000000000000000 : ℝ) ≤
      (-(13905575961864639085561 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (123938721978887 / 2000000000000000 : ℚ))
        (r' := (123938721978887 / 62500000000000 : ℚ))
        (U := (-(13905575961864639085561 / 5000000000000000000000 : ℚ)))
        (U' := (3423103545635360914439 / 5000000000000000000000 : ℚ))
        5 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (24870259471 / 250000000000 : ℚ))
      (s := (57672327829387 / 1000000000000000 : ℚ))
      (q := (123938721978887 / 2000000000000000 : ℚ))
      (U := (-(13905575961864639085561 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_145_6 :
    Uω (aρ 6) (bρ 6) (24870259471 / 250000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_145_7 :
    Uω (aρ 7) (bρ 7) (24870259471 / 250000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_145_8 :
    Uω (aρ 8) (bρ 8) (24870259471 / 250000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_145_9 :
    Uω (aρ 9) (bρ 9) (24870259471 / 250000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_145_10 :
    Uω (aρ 10) (bρ 10) (24870259471 / 250000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_145_11 :
    Uω (aρ 11) (bρ 11) (24870259471 / 250000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_145_12 :
    Uω (aρ 12) (bρ 12) (24870259471 / 250000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_145_13 :
    Uω (aρ 13) (bρ 13) (24870259471 / 250000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_145_14 :
    Uω (aρ 14) (bρ 14) (24870259471 / 250000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_145_15 :
    Uω (aρ 15) (bρ 15) (24870259471 / 250000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_145_16 :
    Uω (aρ 16) (bρ 16) (24870259471 / 250000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_145 :
    Uρ (24870259471 / 250000000000 : ℝ) ≤
      (-(6006179333855527615251 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_145_1 U_145_2 U_145_3 U_145_4 U_145_5 U_145_6 U_145_7 U_145_8 U_145_9 U_145_10
    U_145_11 U_145_12 U_145_13 U_145_14 U_145_15 U_145_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_146_1 :
    Uω (aρ 1) (bρ 1) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(23600490741746310132633 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47207794808651 / 500000000000000 : ℝ) ≤
      (-(23600490741746310132633 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47207794808651 / 500000000000000 : ℚ))
        (r' := (47207794808651 / 31250000000000 : ℚ))
        (U := (-(23600490741746310132633 / 10000000000000000000000 : ℚ)))
        (U' := (4125396470253689867367 / 10000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1614118950931 / 16000000000000 : ℚ))
      (s := (188796933219833 / 2000000000000000 : ℚ))
      (q := (47207794808651 / 500000000000000 : ℚ))
      (U := (-(23600490741746310132633 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_146_2 :
    Uω (aρ 2) (bρ 2) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(23866145357694081674823 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (229851046232431 / 2500000000000000 : ℝ) ≤
      (-(23866145357694081674823 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (229851046232431 / 2500000000000000 : ℚ))
        (r' := (229851046232431 / 156250000000000 : ℚ))
        (U := (-(23866145357694081674823 / 10000000000000000000000 : ℚ)))
        (U' := (3859741854305918325177 / 10000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1614118950931 / 16000000000000 : ℚ))
      (s := (918250256122573 / 10000000000000000 : ℚ))
      (q := (229851046232431 / 2500000000000000 : ℚ))
      (U := (-(23866145357694081674823 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_146_3 :
    Uω (aρ 3) (bρ 3) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(4886213425407009894147 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1737809756710397 / 20000000000000000 : ℝ) ≤
      (-(4886213425407009894147 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1737809756710397 / 20000000000000000 : ℚ))
        (r' := (1737809756710397 / 1250000000000000 : ℚ))
        (U := (-(4886213425407009894147 / 2000000000000000000000 : ℚ)))
        (U' := (658964016992990105853 / 2000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1614118950931 / 16000000000000 : ℚ))
      (s := (432323874661761 / 5000000000000000 : ℚ))
      (q := (1737809756710397 / 20000000000000000 : ℚ))
      (U := (-(4886213425407009894147 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_146_4 :
    Uω (aρ 4) (bρ 4) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(25492478055288563125353 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3125616824483 / 40000000000000 : ℝ) ≤
      (-(25492478055288563125353 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3125616824483 / 40000000000000 : ℚ))
        (r' := (3125616824483 / 2500000000000 : ℚ))
        (U := (-(25492478055288563125353 / 10000000000000000000000 : ℚ)))
        (U' := (2233409156711436874647 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1614118950931 / 16000000000000 : ℚ))
      (s := (6143524687357 / 80000000000000 : ℚ))
      (q := (3125616824483 / 40000000000000 : ℚ))
      (U := (-(25492478055288563125353 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_146_5 :
    Uω (aρ 5) (bρ 5) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(27571482204858512832921 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1269450401433503 / 20000000000000000 : ℝ) ≤
      (-(27571482204858512832921 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1269450401433503 / 20000000000000000 : ℚ))
        (r' := (1269450401433503 / 1250000000000000 : ℚ))
        (U := (-(27571482204858512832921 / 10000000000000000000000 : ℚ)))
        (U' := (154405007141487167079 / 10000000000000000000000 : ℚ))
        4 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1614118950931 / 16000000000000 : ℚ))
      (s := (148193123611657 / 2500000000000000 : ℚ))
      (q := (1269450401433503 / 20000000000000000 : ℚ))
      (U := (-(27571482204858512832921 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_146_6 :
    Uω (aρ 6) (bρ 6) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(17303896956176881585291 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (125621101760153 / 4000000000000000 : ℝ) ≤
      (-(17303896956176881585291 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (125621101760153 / 4000000000000000 : ℚ))
        (r' := (125621101760153 / 125000000000000 : ℚ))
        (U := (-(17303896956176881585291 / 5000000000000000000000 : ℚ)))
        (U' := (24782551323118414709 / 5000000000000000000000 : ℚ))
        5 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1614118950931 / 16000000000000 : ℚ))
      (s := (11866797695389 / 1000000000000000 : ℚ))
      (q := (125621101760153 / 4000000000000000 : ℚ))
      (U := (-(17303896956176881585291 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_146_7 :
    Uω (aρ 7) (bρ 7) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_146_8 :
    Uω (aρ 8) (bρ 8) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_146_9 :
    Uω (aρ 9) (bρ 9) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_146_10 :
    Uω (aρ 10) (bρ 10) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_146_11 :
    Uω (aρ 11) (bρ 11) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_146_12 :
    Uω (aρ 12) (bρ 12) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_146_13 :
    Uω (aρ 13) (bρ 13) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_146_14 :
    Uω (aρ 14) (bρ 14) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_146_15 :
    Uω (aρ 15) (bρ 15) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_146_16 :
    Uω (aρ 16) (bρ 16) (1614118950931 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_146 :
    Uρ (1614118950931 / 16000000000000 : ℝ) ≤
      (-(1189858212400226247237 / 500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_146_1 U_146_2 U_146_3 U_146_4 U_146_5 U_146_6 U_146_7 U_146_8 U_146_9 U_146_10
    U_146_11 U_146_12 U_146_13 U_146_14 U_146_15 U_146_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_147_1 :
    Uω (aρ 1) (bρ 1) (818270647859 / 8000000000000 : ℝ) ≤
      (-(586328171474169128263 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (958172366476481 / 10000000000000000 : ℝ) ≤
      (-(586328171474169128263 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (958172366476481 / 10000000000000000 : ℚ))
        (r' := (958172366476481 / 625000000000000 : ℚ))
        (U := (-(586328171474169128263 / 250000000000000000000 : ℚ)))
        (U' := (106819008825830871737 / 250000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (818270647859 / 8000000000000 : ℚ))
      (s := (239500910303553 / 2500000000000000 : ℚ))
      (q := (958172366476481 / 10000000000000000 : ℚ))
      (U := (-(586328171474169128263 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_147_2 :
    Uω (aρ 2) (bρ 2) (818270647859 / 8000000000000 : ℝ) ≤
      (-(23714685092528748377319 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (466717748083379 / 5000000000000000 : ℝ) ≤
      (-(23714685092528748377319 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (466717748083379 / 5000000000000000 : ℚ))
        (r' := (466717748083379 / 312500000000000 : ℚ))
        (U := (-(23714685092528748377319 / 10000000000000000000000 : ℚ)))
        (U' := (4011202119471251622681 / 10000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (818270647859 / 8000000000000 : ℚ))
      (s := (466149456552383 / 5000000000000000 : ℚ))
      (q := (466717748083379 / 5000000000000000 : ℚ))
      (U := (-(23714685092528748377319 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_147_3 :
    Uω (aρ 3) (bρ 3) (818270647859 / 8000000000000 : ℝ) ≤
      (-(3033787739285829484113 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (353194694588661 / 4000000000000000 : ℝ) ≤
      (-(3033787739285829484113 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (353194694588661 / 4000000000000000 : ℚ))
        (r' := (353194694588661 / 250000000000000 : ℚ))
        (U := (-(3033787739285829484113 / 1250000000000000000000 : ℚ)))
        (U' := (431948162214170515887 / 1250000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (818270647859 / 8000000000000 : ℚ))
      (s := (175759500012911 / 2000000000000000 : ℚ))
      (q := (353194694588661 / 4000000000000000 : ℚ))
      (U := (-(3033787739285829484113 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_147_4 :
    Uω (aρ 4) (bρ 4) (818270647859 / 8000000000000 : ℝ) ≤
      (-(25311691807556838955743 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (795659388347077 / 10000000000000000 : ℝ) ≤
      (-(25311691807556838955743 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (795659388347077 / 10000000000000000 : ℚ))
        (r' := (795659388347077 / 625000000000000 : ℚ))
        (U := (-(25311691807556838955743 / 10000000000000000000000 : ℚ)))
        (U' := (2414195404443161044257 / 10000000000000000000000 : ℚ))
        4 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (818270647859 / 8000000000000 : ℚ))
      (s := (195609246220101 / 2500000000000000 : ℚ))
      (q := (795659388347077 / 10000000000000000 : ℚ))
      (U := (-(25311691807556838955743 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_147_5 :
    Uω (aρ 5) (bρ 5) (818270647859 / 8000000000000 : ℝ) ≤
      (-(13669097951678662512941 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (649706537778299 / 10000000000000000 : ℝ) ≤
      (-(13669097951678662512941 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (649706537778299 / 10000000000000000 : ℚ))
        (r' := (649706537778299 / 625000000000000 : ℚ))
        (U := (-(13669097951678662512941 / 5000000000000000000000 : ℚ)))
        (U' := (193845654321337487059 / 5000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (818270647859 / 8000000000000 : ℚ))
      (s := (76090150384731 / 1250000000000000 : ℚ))
      (q := (649706537778299 / 10000000000000000 : ℚ))
      (U := (-(13669097951678662512941 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_147_6 :
    Uω (aρ 6) (bρ 6) (818270647859 / 8000000000000 : ℝ) ≤
      (-(2102041636154490140537 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (346219772076763 / 10000000000000000 : ℝ) ≤
      (-(2102041636154490140537 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (346219772076763 / 10000000000000000 : ℚ))
        (r' := (346219772076763 / 312500000000000 : ℚ))
        (U := (-(2102041636154490140537 / 625000000000000000000 : ℚ)))
        (U' := (64043302283009859463 / 625000000000000000000 : ℚ))
        5 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (818270647859 / 8000000000000 : ℚ))
      (s := (21123505851847 / 1250000000000000 : ℚ))
      (q := (346219772076763 / 10000000000000000 : ℚ))
      (U := (-(2102041636154490140537 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_147_7 :
    Uω (aρ 7) (bρ 7) (818270647859 / 8000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_147_8 :
    Uω (aρ 8) (bρ 8) (818270647859 / 8000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_147_9 :
    Uω (aρ 9) (bρ 9) (818270647859 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_147_10 :
    Uω (aρ 10) (bρ 10) (818270647859 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_147_11 :
    Uω (aρ 11) (bρ 11) (818270647859 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_147_12 :
    Uω (aρ 12) (bρ 12) (818270647859 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_147_13 :
    Uω (aρ 13) (bρ 13) (818270647859 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_147_14 :
    Uω (aρ 14) (bρ 14) (818270647859 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_147_15 :
    Uω (aρ 15) (bρ 15) (818270647859 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_147_16 :
    Uω (aρ 16) (bρ 16) (818270647859 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_147 :
    Uρ (818270647859 / 8000000000000 : ℝ) ≤
      (-(23680709076845825592017 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_147_1 U_147_2 U_147_3 U_147_4 U_147_5 U_147_6 U_147_7 U_147_8 U_147_9 U_147_10
    U_147_11 U_147_12 U_147_13 U_147_14 U_147_15 U_147_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
