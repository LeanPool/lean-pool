/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U44) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_532_1 :
    Uω (aρ 1) (bρ 1) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(1015344587023385956413 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12037899683632227 / 20000000000000000 : ℝ) ≤
      (-(1015344587023385956413 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12037899683632227 / 20000000000000000 : ℚ))
        (r' := (12037899683632227 / 10000000000000000 : ℚ))
        (U := (-(1015344587023385956413 / 2000000000000000000000 : ℚ)))
        (U' := (370949773576614043587 / 2000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (188091343187511 / 312500000000000 : ℚ))
      (q := (12037899683632227 / 20000000000000000 : ℚ))
      (U := (-(1015344587023385956413 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_2 :
    Uω (aρ 2) (bρ 2) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(2558270898826269298443 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2398012288556993 / 4000000000000000 : ℝ) ≤
      (-(2558270898826269298443 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2398012288556993 / 4000000000000000 : ℚ))
        (r' := (2398012288556993 / 2000000000000000 : ℚ))
        (U := (-(2558270898826269298443 / 5000000000000000000000 : ℚ)))
        (U' := (907465002673730701557 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (599485375366309 / 1000000000000000 : ℚ))
      (q := (2398012288556993 / 4000000000000000 : ℚ))
      (U := (-(2558270898826269298443 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_3 :
    Uω (aρ 3) (bρ 3) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(12991658015855303567 / 25000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1189437920312411 / 2000000000000000 : ℝ) ≤
      (-(12991658015855303567 / 25000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1189437920312411 / 2000000000000000 : ℚ))
        (r' := (1189437920312411 / 1000000000000000 : ℚ))
        (U := (-(12991658015855303567 / 25000000000000000000 : ℚ)))
        (U' := (4337021491644696433 / 25000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (1189313524070447 / 2000000000000000 : ℚ))
      (q := (1189437920312411 / 2000000000000000 : ℚ))
      (U := (-(12991658015855303567 / 25000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_4 :
    Uω (aρ 4) (bρ 4) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(5331181911364434298457 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5867724452917411 / 10000000000000000 : ℝ) ≤
      (-(5331181911364434298457 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5867724452917411 / 10000000000000000 : ℚ))
        (r' := (5867724452917411 / 5000000000000000 : ℚ))
        (U := (-(5331181911364434298457 / 10000000000000000000000 : ℚ)))
        (U' := (1600289891635565701543 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (5865931504127947 / 10000000000000000 : ℚ))
      (q := (5867724452917411 / 10000000000000000 : ℚ))
      (U := (-(5331181911364434298457 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_5 :
    Uω (aρ 5) (bρ 5) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(2769801986054336931911 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (359168361562289 / 625000000000000 : ℝ) ≤
      (-(2769801986054336931911 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (359168361562289 / 625000000000000 : ℚ))
        (r' := (359168361562289 / 312500000000000 : ℚ))
        (U := (-(2769801986054336931911 / 5000000000000000000000 : ℚ)))
        (U' := (695933915445663068089 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (5742060087621373 / 10000000000000000 : ℚ))
      (q := (359168361562289 / 625000000000000 : ℚ))
      (U := (-(2769801986054336931911 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_6 :
    Uω (aρ 6) (bρ 6) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(58463779834278348057 / 100000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1114615365762961 / 2000000000000000 : ℝ) ≤
      (-(58463779834278348057 / 100000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1114615365762961 / 2000000000000000 : ℚ))
        (r' := (1114615365762961 / 1000000000000000 : ℚ))
        (U := (-(58463779834278348057 / 100000000000000000000 : ℚ)))
        (U' := (10850938195721651943 / 100000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (1112413310079547 / 2000000000000000 : ℚ))
      (q := (1114615365762961 / 2000000000000000 : ℚ))
      (U := (-(58463779834278348057 / 100000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_7 :
    Uω (aρ 7) (bρ 7) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(6280854844228632773047 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1334031082159119 / 2500000000000000 : ℝ) ≤
      (-(6280854844228632773047 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1334031082159119 / 2500000000000000 : ℚ))
        (r' := (1334031082159119 / 1250000000000000 : ℚ))
        (U := (-(6280854844228632773047 / 10000000000000000000000 : ℚ)))
        (U' := (650616958771367226953 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (5311822930801077 / 10000000000000000 : ℚ))
      (q := (1334031082159119 / 2500000000000000 : ℚ))
      (U := (-(6280854844228632773047 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_8 :
    Uω (aρ 8) (bρ 8) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(343910265860526981271 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2010681720788129 / 4000000000000000 : ℝ) ≤
      (-(343910265860526981271 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2010681720788129 / 4000000000000000 : ℚ))
        (r' := (2010681720788129 / 2000000000000000 : ℚ))
        (U := (-(343910265860526981271 / 500000000000000000000 : ℚ)))
        (U' := (2663324289473018729 / 500000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (497652452880877 / 1000000000000000 : ℚ))
      (q := (2010681720788129 / 4000000000000000 : ℚ))
      (U := (-(343910265860526981271 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_9 :
    Uω (aρ 9) (bρ 9) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(7682410227718395423797 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2319141071075849 / 5000000000000000 : ℝ) ≤
      (-(7682410227718395423797 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2319141071075849 / 5000000000000000 : ℚ))
        (r' := (2319141071075849 / 1250000000000000 : ℚ))
        (U := (-(7682410227718395423797 / 10000000000000000000000 : ℚ)))
        (U' := (6180533378281604576203 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (4540645837531521 / 10000000000000000 : ℚ))
      (q := (2319141071075849 / 5000000000000000 : ℚ))
      (U := (-(7682410227718395423797 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_10 :
    Uω (aρ 10) (bρ 10) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(1750874840954918337967 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8333594307057603 / 20000000000000000 : ℝ) ≤
      (-(1750874840954918337967 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8333594307057603 / 20000000000000000 : ℚ))
        (r' := (8333594307057603 / 5000000000000000 : ℚ))
        (U := (-(1750874840954918337967 / 2000000000000000000000 : ℚ)))
        (U' := (1021713880245081662033 / 2000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (498279361722591 / 1250000000000000 : ℚ))
      (q := (8333594307057603 / 20000000000000000 : ℚ))
      (U := (-(1750874840954918337967 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_11 :
    Uω (aρ 11) (bρ 11) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(2548920187344628660401 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7215014472369557 / 20000000000000000 : ℝ) ≤
      (-(2548920187344628660401 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7215014472369557 / 20000000000000000 : ℚ))
        (r' := (7215014472369557 / 5000000000000000 : ℚ))
        (U := (-(2548920187344628660401 / 2500000000000000000000 : ℚ)))
        (U' := (916815714155371339599 / 2500000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (1643065842648841 / 5000000000000000 : ℚ))
      (q := (7215014472369557 / 20000000000000000 : ℚ))
      (U := (-(2548920187344628660401 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_12 :
    Uω (aρ 12) (bρ 12) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(3060087048242988541479 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (58808273261367 / 200000000000000 : ℝ) ≤
      (-(3060087048242988541479 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (58808273261367 / 200000000000000 : ℚ))
        (r' := (58808273261367 / 50000000000000 : ℚ))
        (U := (-(3060087048242988541479 / 2500000000000000000000 : ℚ)))
        (U' := (405648853257011458521 / 2500000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (95025785429993 / 400000000000000 : ℚ))
      (q := (58808273261367 / 200000000000000 : ℚ))
      (U := (-(3060087048242988541479 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_13 :
    Uω (aρ 13) (bρ 13) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(16115495756291320341457 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3991562256075879 / 20000000000000000 : ℝ) ≤
      (-(16115495756291320341457 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3991562256075879 / 20000000000000000 : ℚ))
        (r' := (3991562256075879 / 2500000000000000 : ℚ))
        (U := (-(16115495756291320341457 / 10000000000000000000000 : ℚ)))
        (U' := (4678919652708679658543 / 10000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (9733558271547 / 16000000000000 : ℚ))
      (s := (221440326821001 / 2500000000000000 : ℚ))
      (q := (3991562256075879 / 20000000000000000 : ℚ))
      (U := (-(16115495756291320341457 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_532_14 :
    Uω (aρ 14) (bρ 14) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_532_15 :
    Uω (aρ 15) (bρ 15) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_532_16 :
    Uω (aρ 16) (bρ 16) (9733558271547 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_532 :
    Uρ (9733558271547 / 16000000000000 : ℝ) ≤
      (-(4092119036616476838689 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_532_1 U_532_2 U_532_3 U_532_4 U_532_5 U_532_6 U_532_7 U_532_8 U_532_9 U_532_10
    U_532_11 U_532_12 U_532_13 U_532_14 U_532_15 U_532_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_533_1 :
    Uω (aρ 1) (bρ 1) (312024205529 / 512000000000 : ℝ) ≤
      (-(2529440222003763779621 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9647517974751029 / 16000000000000000 : ℝ) ≤
      (-(2529440222003763779621 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9647517974751029 / 16000000000000000 : ℚ))
        (r' := (9647517974751029 / 8000000000000000 : ℚ))
        (U := (-(2529440222003763779621 / 5000000000000000000000 : ℚ)))
        (U' := (936295679496236220379 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (312024205529 / 512000000000 : ℚ))
      (s := (1205934384457101 / 2000000000000000 : ℚ))
      (q := (9647517974751029 / 16000000000000000 : ℚ))
      (U := (-(2529440222003763779621 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_2 :
    Uω (aρ 2) (bρ 2) (312024205529 / 512000000000 : ℝ) ≤
      (-(5098627734197961890647 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48046239061209721 / 80000000000000000 : ℝ) ≤
      (-(5098627734197961890647 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48046239061209721 / 80000000000000000 : ℚ))
        (r' := (48046239061209721 / 40000000000000000 : ℚ))
        (U := (-(5098627734197961890647 / 10000000000000000000000 : ℚ)))
        (U' := (1832844068802038109353 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (312024205529 / 512000000000 : ℚ))
      (s := (6005603231659149 / 10000000000000000 : ℚ))
      (q := (48046239061209721 / 80000000000000000 : ℚ))
      (U := (-(5098627734197961890647 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_3 :
    Uω (aρ 3) (bρ 3) (312024205529 / 512000000000 : ℝ) ≤
      (-(5178603814400613640559 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47663516546640373 / 80000000000000000 : ℝ) ≤
      (-(5178603814400613640559 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47663516546640373 / 80000000000000000 : ℚ))
        (r' := (47663516546640373 / 40000000000000000 : ℚ))
        (U := (-(5178603814400613640559 / 10000000000000000000000 : ℚ)))
        (U' := (1752867988599386359441 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (312024205529 / 512000000000 : ℚ))
      (s := (1489329677341703 / 2500000000000000 : ℚ))
      (q := (47663516546640373 / 80000000000000000 : ℚ))
      (U := (-(5178603814400613640559 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_4 :
    Uω (aρ 4) (bρ 4) (312024205529 / 512000000000 : ℝ) ≤
      (-(5312874499598534674163 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1881112504595581 / 3200000000000000 : ℝ) ≤
      (-(5312874499598534674163 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1881112504595581 / 3200000000000000 : ℚ))
        (r' := (1881112504595581 / 1600000000000000 : ℚ))
        (U := (-(5312874499598534674163 / 10000000000000000000000 : ℚ)))
        (U' := (1618597303401465325837 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (312024205529 / 512000000000 : ℚ))
      (s := (58766869074941 / 100000000000000 : ℚ))
      (q := (1881112504595581 / 3200000000000000 : ℚ))
      (U := (-(5312874499598534674163 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_5 :
    Uω (aρ 5) (bρ 5) (312024205529 / 512000000000 : ℝ) ≤
      (-(5520902007877414746151 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46059610298750769 / 80000000000000000 : ℝ) ≤
      (-(5520902007877414746151 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46059610298750769 / 80000000000000000 : ℚ))
        (r' := (46059610298750769 / 40000000000000000 : ℚ))
        (U := (-(5520902007877414746151 / 10000000000000000000000 : ℚ)))
        (U' := (1410569795122585253849 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (312024205529 / 512000000000 : ℚ))
      (s := (5752826247794411 / 10000000000000000 : ℚ))
      (q := (46059610298750769 / 80000000000000000 : ℚ))
      (U := (-(5520902007877414746151 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_6 :
    Uω (aρ 6) (bρ 6) (312024205529 / 512000000000 : ℝ) ≤
      (-(2913535717514371392481 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (44670775279013717 / 80000000000000000 : ℝ) ≤
      (-(2913535717514371392481 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (44670775279013717 / 80000000000000000 : ℚ))
        (r' := (44670775279013717 / 40000000000000000 : ℚ))
        (U := (-(2913535717514371392481 / 5000000000000000000000 : ℚ)))
        (U' := (552200183985628607519 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (312024205529 / 512000000000 : ℚ))
      (s := (1393214467000037 / 2500000000000000 : ℚ))
      (q := (44670775279013717 / 80000000000000000 : ℚ))
      (U := (-(2913535717514371392481 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_7 :
    Uω (aρ 7) (bρ 7) (312024205529 / 512000000000 : ℝ) ≤
      (-(6260639779296802408789 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (42775377991769201 / 80000000000000000 : ℝ) ≤
      (-(6260639779296802408789 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (42775377991769201 / 80000000000000000 : ℚ))
        (r' := (42775377991769201 / 40000000000000000 : ℚ))
        (U := (-(6260639779296802408789 / 10000000000000000000000 : ℚ)))
        (U' := (670832023703197591211 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (312024205529 / 512000000000 : ℚ))
      (s := (5322669926949019 / 10000000000000000 : ℚ))
      (q := (42775377991769201 / 80000000000000000 : ℚ))
      (U := (-(6260639779296802408789 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_8 :
    Uω (aρ 8) (bρ 8) (312024205529 / 512000000000 : ℝ) ≤
      (-(6856629979244132857753 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40300490354719693 / 80000000000000000 : ℝ) ≤
      (-(6856629979244132857753 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (40300490354719693 / 80000000000000000 : ℚ))
        (r' := (40300490354719693 / 40000000000000000 : ℚ))
        (U := (-(6856629979244132857753 / 10000000000000000000000 : ℚ)))
        (U' := (74841823755867142247 / 10000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (312024205529 / 512000000000 : ℚ))
      (s := (2493744834513321 / 5000000000000000 : ℚ))
      (q := (40300490354719693 / 80000000000000000 : ℚ))
      (U := (-(6856629979244132857753 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_9 :
    Uω (aρ 9) (bρ 9) (312024205529 / 512000000000 : ℝ) ≤
      (-(3829383450332178808059 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (37194092469595613 / 80000000000000000 : ℝ) ≤
      (-(3829383450332178808059 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (37194092469595613 / 80000000000000000 : ℚ))
        (r' := (37194092469595613 / 20000000000000000 : ℚ))
        (U := (-(3829383450332178808059 / 5000000000000000000000 : ℚ)))
        (U' := (3102088352667821191941 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (312024205529 / 512000000000 : ℚ))
      (s := (2275927913052811 / 5000000000000000 : ℚ))
      (q := (37194092469595613 / 80000000000000000 : ℚ))
      (U := (-(3829383450332178808059 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_10 :
    Uω (aρ 10) (bρ 10) (312024205529 / 512000000000 : ℝ) ≤
      (-(272732777028236039401 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33424252113150029 / 80000000000000000 : ℝ) ≤
      (-(272732777028236039401 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (33424252113150029 / 80000000000000000 : ℚ))
        (r' := (33424252113150029 / 20000000000000000 : ℚ))
        (U := (-(272732777028236039401 / 312500000000000000000 : ℚ)))
        (U' := (160484210659263960599 / 312500000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (312024205529 / 512000000000 : ℚ))
      (s := (1998977385244613 / 5000000000000000 : ℚ))
      (q := (33424252113150029 / 80000000000000000 : ℚ))
      (U := (-(272732777028236039401 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_11 :
    Uω (aρ 11) (bρ 11) (312024205529 / 512000000000 : ℝ) ≤
      (-(10163034798815418328541 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28954428248479461 / 80000000000000000 : ℝ) ≤
      (-(10163034798815418328541 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (28954428248479461 / 80000000000000000 : ℚ))
        (r' := (28954428248479461 / 20000000000000000 : ℚ))
        (U := (-(10163034798815418328541 / 10000000000000000000000 : ℚ)))
        (U' := (3699908807184581671459 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (312024205529 / 512000000000 : ℚ))
      (s := (412371928815823 / 1250000000000000 : ℚ))
      (q := (28954428248479461 / 80000000000000000 : ℚ))
      (U := (-(10163034798815418328541 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_12 :
    Uω (aρ 12) (bρ 12) (312024205529 / 512000000000 : ℝ) ≤
      (-(12195252362156481322259 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23629629171164773 / 80000000000000000 : ℝ) ≤
      (-(12195252362156481322259 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23629629171164773 / 80000000000000000 : ℚ))
        (r' := (23629629171164773 / 20000000000000000 : ℚ))
        (U := (-(12195252362156481322259 / 10000000000000000000000 : ℚ)))
        (U' := (1667691243843518677741 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (312024205529 / 512000000000 : ℚ))
      (s := (74733617433841 / 312500000000000 : ℚ))
      (q := (23629629171164773 / 80000000000000000 : ℚ))
      (U := (-(12195252362156481322259 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_13 :
    Uω (aρ 13) (bρ 13) (312024205529 / 512000000000 : ℝ) ≤
      (-(3999156105056330198967 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16157174489704889 / 80000000000000000 : ℝ) ≤
      (-(3999156105056330198967 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16157174489704889 / 80000000000000000 : ℚ))
        (r' := (16157174489704889 / 10000000000000000 : ℚ))
        (U := (-(3999156105056330198967 / 2500000000000000000000 : ℚ)))
        (U' := (1199447747193669801033 / 2500000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (312024205529 / 512000000000 : ℚ))
      (s := (922743829112941 / 10000000000000000 : ℚ))
      (q := (16157174489704889 / 80000000000000000 : ℚ))
      (U := (-(3999156105056330198967 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_533_14 :
    Uω (aρ 14) (bρ 14) (312024205529 / 512000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_533_15 :
    Uω (aρ 15) (bρ 15) (312024205529 / 512000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_533_16 :
    Uω (aρ 16) (bρ 16) (312024205529 / 512000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_533 :
    Uρ (312024205529 / 512000000000 : ℝ) ≤
      (-(8158113287143502076381 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_533_1 U_533_2 U_533_3 U_533_4 U_533_5 U_533_6 U_533_7 U_533_8 U_533_9 U_533_10
    U_533_11 U_533_12 U_533_13 U_533_14 U_533_15 U_533_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_534_1 :
    Uω (aρ 1) (bρ 1) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(2520534865968170005413 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4832358101161809 / 8000000000000000 : ℝ) ≤
      (-(2520534865968170005413 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4832358101161809 / 8000000000000000 : ℚ))
        (r' := (4832358101161809 / 4000000000000000 : ℚ))
        (U := (-(2520534865968170005413 / 5000000000000000000000 : ℚ)))
        (U' := (945201035531829994587 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (1208084172445967 / 2000000000000000 : ℚ))
      (q := (4832358101161809 / 8000000000000000 : ℚ))
      (U := (-(2520534865968170005413 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_2 :
    Uω (aρ 2) (bρ 2) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(5080745706614145080733 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24066116171112581 / 40000000000000000 : ℝ) ≤
      (-(5080745706614145080733 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24066116171112581 / 40000000000000000 : ℚ))
        (r' := (24066116171112581 / 20000000000000000 : ℚ))
        (U := (-(5080745706614145080733 / 10000000000000000000000 : ℚ)))
        (U' := (1850726096385854919267 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (6016352707391603 / 10000000000000000 : ℚ))
      (q := (24066116171112581 / 40000000000000000 : ℚ))
      (U := (-(5080745706614145080733 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_3 :
    Uω (aρ 3) (bρ 3) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(258028849230606099 / 500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23874758124220609 / 40000000000000000 : ℝ) ≤
      (-(258028849230606099 / 500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23874758124220609 / 40000000000000000 : ℚ))
        (r' := (23874758124220609 / 20000000000000000 : ℚ))
        (U := (-(258028849230606099 / 500000000000000000 : ℚ)))
        (U' := (88544740919393901 / 500000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (5968069790295617 / 10000000000000000 : ℚ))
      (q := (23874758124220609 / 40000000000000000 : ℚ))
      (U := (-(258028849230606099 / 500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_4 :
    Uω (aρ 4) (bρ 4) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(5294600563066589342857 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23556914755306709 / 40000000000000000 : ℝ) ≤
      (-(5294600563066589342857 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23556914755306709 / 40000000000000000 : ℚ))
        (r' := (23556914755306709 / 20000000000000000 : ℚ))
        (U := (-(5294600563066589342857 / 10000000000000000000000 : ℚ)))
        (U' := (1636871239933410657143 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (5887442286903667 / 10000000000000000 : ℚ))
      (q := (23556914755306709 / 40000000000000000 : ℚ))
      (U := (-(5294600563066589342857 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_5 :
    Uω (aρ 5) (bρ 5) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(1100447002148356538251 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23072835029488537 / 40000000000000000 : ℝ) ≤
      (-(1100447002148356538251 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23072835029488537 / 40000000000000000 : ℚ))
        (r' := (23072835029488537 / 20000000000000000 : ℚ))
        (U := (-(1100447002148356538251 / 2000000000000000000000 : ℚ)))
        (U' := (285847358451643461749 / 2000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (5763592343329581 / 10000000000000000 : ℚ))
      (q := (23072835029488537 / 40000000000000000 : ℚ))
      (U := (-(1100447002148356538251 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_6 :
    Uω (aρ 6) (bρ 6) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(1161560447106391500073 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22378467636055877 / 40000000000000000 : ℝ) ≤
      (-(1161560447106391500073 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (22378467636055877 / 40000000000000000 : ℚ))
        (r' := (22378467636055877 / 20000000000000000 : ℚ))
        (U := (-(1161560447106391500073 / 2000000000000000000000 : ℚ)))
        (U' := (224733913493608499927 / 2000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (5583649021753251 / 10000000000000000 : ℚ))
      (q := (22378467636055877 / 40000000000000000 : ℚ))
      (U := (-(1161560447106391500073 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_7 :
    Uω (aρ 7) (bρ 7) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(1560116466927709879407 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4286175976475109 / 8000000000000000 : ℝ) ≤
      (-(1560116466927709879407 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4286175976475109 / 8000000000000000 : ℚ))
        (r' := (4286175976475109 / 4000000000000000 : ℚ))
        (U := (-(1560116466927709879407 / 2500000000000000000000 : ℚ)))
        (U' := (172751483822290120593 / 2500000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (1066703305134617 / 2000000000000000 : ℚ))
      (q := (4286175976475109 / 8000000000000000 : ℚ))
      (U := (-(1560116466927709879407 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_8 :
    Uω (aρ 8) (bρ 8) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(3417551010603838729737 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20193671267600891 / 40000000000000000 : ℝ) ≤
      (-(3417551010603838729737 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20193671267600891 / 40000000000000000 : ℚ))
        (r' := (20193671267600891 / 20000000000000000 : ℚ))
        (U := (-(3417551010603838729737 / 5000000000000000000000 : ℚ)))
        (U' := (48184890896161270263 / 5000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (2499226934812879 / 5000000000000000 : ℚ))
      (q := (20193671267600891 / 40000000000000000 : ℚ))
      (U := (-(3417551010603838729737 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_9 :
    Uω (aρ 9) (bρ 9) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(7635181723425072818701 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3728191892532483 / 8000000000000000 : ℝ) ≤
      (-(7635181723425072818701 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3728191892532483 / 8000000000000000 : ℚ))
        (r' := (3728191892532483 / 2000000000000000 : ℚ))
        (U := (-(7635181723425072818701 / 10000000000000000000000 : ℚ)))
        (U' := (6227761882574927181299 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (114076589887913 / 250000000000000 : ℚ))
      (q := (3728191892532483 / 8000000000000000 : ℚ))
      (U := (-(7635181723425072818701 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_10 :
    Uω (aρ 10) (bρ 10) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(8700602322136267647359 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16757052616423023 / 40000000000000000 : ℝ) ≤
      (-(8700602322136267647359 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16757052616423023 / 40000000000000000 : ℚ))
        (r' := (16757052616423023 / 10000000000000000 : ℚ))
        (U := (-(8700602322136267647359 / 10000000000000000000000 : ℚ)))
        (U' := (5162341283863732352641 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (250604325368239 / 625000000000000 : ℚ))
      (q := (16757052616423023 / 40000000000000000 : ℚ))
      (U := (-(8700602322136267647359 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_11 :
    Uω (aρ 11) (bρ 11) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(10130515627069486294957 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14524369456552627 / 40000000000000000 : ℝ) ≤
      (-(10130515627069486294957 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (14524369456552627 / 40000000000000000 : ℚ))
        (r' := (14524369456552627 / 10000000000000000 : ℚ))
        (U := (-(10130515627069486294957 / 10000000000000000000000 : ℚ)))
        (U' := (3732427978930513705043 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (1655902126080813 / 5000000000000000 : ℚ))
      (q := (14524369456552627 / 40000000000000000 : ℚ))
      (U := (-(10130515627069486294957 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_12 :
    Uω (aρ 12) (bρ 12) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(6075226774800110837489 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11867862286965257 / 40000000000000000 : ℝ) ≤
      (-(6075226774800110837489 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11867862286965257 / 40000000000000000 : ℚ))
        (r' := (11867862286965257 / 10000000000000000 : ℚ))
        (U := (-(6075226774800110837489 / 5000000000000000000000 : ℚ)))
        (U' := (856245028199889162511 / 5000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (2407250764052941 / 10000000000000000 : ℚ))
      (q := (11867862286965257 / 40000000000000000 : ℚ))
      (U := (-(6075226774800110837489 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_13 :
    Uω (aρ 13) (bρ 13) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(3970586139317389642427 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (65371510173111 / 320000000000000 : ℝ) ≤
      (-(3970586139317389642427 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (65371510173111 / 320000000000000 : ℚ))
        (r' := (65371510173111 / 40000000000000 : ℚ))
        (U := (-(3970586139317389642427 / 2500000000000000000000 : ℚ)))
        (U' := (1228017712932610357573 / 2500000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (19535909148031 / 32000000000000 : ℚ))
      (s := (3833682991939 / 40000000000000 : ℚ))
      (q := (65371510173111 / 320000000000000 : ℚ))
      (U := (-(3970586139317389642427 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_534_14 :
    Uω (aρ 14) (bρ 14) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_534_15 :
    Uω (aρ 15) (bρ 15) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_534_16 :
    Uω (aρ 16) (bρ 16) (19535909148031 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_534 :
    Uρ (19535909148031 / 32000000000000 : ℝ) ≤
      (-(8132319092386912548451 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_534_1 U_534_2 U_534_3 U_534_4 U_534_5 U_534_6 U_534_7 U_534_8 U_534_9 U_534_10
    U_534_11 U_534_12 U_534_13 U_534_14 U_534_15 U_534_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_535_1 :
    Uω (aρ 1) (bρ 1) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(2511645342950552390927 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9681914429625003 / 16000000000000000 : ℝ) ≤
      (-(2511645342950552390927 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9681914429625003 / 16000000000000000 : ℚ))
        (r' := (9681914429625003 / 8000000000000000 : ℚ))
        (U := (-(2511645342950552390927 / 5000000000000000000000 : ℚ)))
        (U' := (954090558549447609073 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (151279245045879 / 250000000000000 : ℚ))
      (q := (9681914429625003 / 16000000000000000 : ℚ))
      (U := (-(2511645342950552390927 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_2 :
    Uω (aρ 2) (bρ 2) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(5062895600518868362853 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48218225614234631 / 80000000000000000 : ℝ) ≤
      (-(5062895600518868362853 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48218225614234631 / 80000000000000000 : ℚ))
        (r' := (48218225614234631 / 40000000000000000 : ℚ))
        (U := (-(5062895600518868362853 / 10000000000000000000000 : ℚ)))
        (U' := (1868576202481131637147 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (1506775545218141 / 2500000000000000 : ℚ))
      (q := (48218225614234631 / 80000000000000000 : ℚ))
      (U := (-(5062895600518868362853 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_3 :
    Uω (aρ 3) (bρ 3) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(1028516519948136732061 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47835515918073447 / 80000000000000000 : ℝ) ≤
      (-(1028516519948136732061 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47835515918073447 / 80000000000000000 : ℚ))
        (r' := (47835515918073447 / 40000000000000000 : ℚ))
        (U := (-(1028516519948136732061 / 2000000000000000000000 : ℚ)))
        (U' := (357777840651863267939 / 2000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (1494705215795567 / 2500000000000000 : ℚ))
      (q := (47835515918073447 / 80000000000000000 : ℚ))
      (U := (-(1028516519948136732061 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_4 :
    Uω (aρ 4) (bρ 4) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(263817998974931911661 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47199846311035179 / 80000000000000000 : ℝ) ≤
      (-(263817998974931911661 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47199846311035179 / 80000000000000000 : ℚ))
        (r' := (47199846311035179 / 40000000000000000 : ℚ))
        (U := (-(263817998974931911661 / 500000000000000000000 : ℚ)))
        (U' := (82755591175068088339 / 500000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (5898197642487701 / 10000000000000000 : ℚ))
      (q := (47199846311035179 / 80000000000000000 : ℚ))
      (U := (-(263817998974931911661 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_5 :
    Uω (aρ 5) (bρ 5) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(685450356247687421249 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46231729562098087 / 80000000000000000 : ℝ) ≤
      (-(685450356247687421249 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46231729562098087 / 80000000000000000 : ℚ))
        (r' := (46231729562098087 / 40000000000000000 : ℚ))
        (U := (-(685450356247687421249 / 1250000000000000000000 : ℚ)))
        (U' := (180983619127312578751 / 1250000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (1443589593647107 / 2500000000000000 : ℚ))
      (q := (46231729562098087 / 80000000000000000 : ℚ))
      (U := (-(685450356247687421249 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_6 :
    Uω (aρ 6) (bρ 6) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(5788570240149873008043 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8968618922721031 / 16000000000000000 : ℝ) ≤
      (-(5788570240149873008043 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8968618922721031 / 16000000000000000 : ℚ))
        (r' := (8968618922721031 / 8000000000000000 : ℚ))
        (U := (-(5788570240149873008043 / 10000000000000000000000 : ℚ)))
        (U' := (1142901562850126991957 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (1118888002521039 / 2000000000000000 : ℚ))
      (q := (8968618922721031 / 16000000000000000 : ℚ))
      (U := (-(5788570240149873008043 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_7 :
    Uω (aρ 7) (bρ 7) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(3110166470379501080453 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (42948139957716527 / 80000000000000000 : ℝ) ≤
      (-(3110166470379501080453 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (42948139957716527 / 80000000000000000 : ℚ))
        (r' := (42948139957716527 / 40000000000000000 : ℚ))
        (U := (-(3110166470379501080453 / 5000000000000000000000 : ℚ)))
        (U' := (355569431120498919547 / 5000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (2672181364696519 / 5000000000000000 : ℚ))
      (q := (42948139957716527 / 80000000000000000 : ℚ))
      (U := (-(3110166470379501080453 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_8 :
    Uω (aρ 8) (bρ 8) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(6813621231441943836873 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40474190981887567 / 80000000000000000 : ℝ) ≤
      (-(6813621231441943836873 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (40474190981887567 / 80000000000000000 : ℚ))
        (r' := (40474190981887567 / 40000000000000000 : ℚ))
        (U := (-(6813621231441943836873 / 10000000000000000000000 : ℚ)))
        (U' := (117850571558056163127 / 10000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (2504708568387899 / 5000000000000000 : ℚ))
      (q := (40474190981887567 / 80000000000000000 : ℚ))
      (U := (-(6813621231441943836873 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_9 :
    Uω (aρ 9) (bρ 9) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(190291359982045990177 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (37369736569649347 / 80000000000000000 : ℝ) ≤
      (-(190291359982045990177 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (37369736569649347 / 80000000000000000 : ℚ))
        (r' := (37369736569649347 / 20000000000000000 : ℚ))
        (U := (-(190291359982045990177 / 250000000000000000000 : ℚ)))
        (U' := (156282230167954009823 / 250000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (4574269162076243 / 10000000000000000 : ℚ))
      (q := (37369736569649347 / 80000000000000000 : ℚ))
      (U := (-(190291359982045990177 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_10 :
    Uω (aρ 10) (bρ 10) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(4336917040251970202751 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33603936777527351 / 80000000000000000 : ℝ) ≤
      (-(4336917040251970202751 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (33603936777527351 / 80000000000000000 : ℚ))
        (r' := (33603936777527351 / 20000000000000000 : ℚ))
        (U := (-(4336917040251970202751 / 5000000000000000000000 : ℚ)))
        (U' := (2594554762748029797249 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (502672280942593 / 1250000000000000 : ℚ))
      (q := (33603936777527351 / 80000000000000000 : ℚ))
      (U := (-(4336917040251970202751 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_11 :
    Uω (aρ 11) (bρ 11) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(5049061054212899413027 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29142990574389979 / 80000000000000000 : ℝ) ≤
      (-(5049061054212899413027 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (29142990574389979 / 80000000000000000 : ℚ))
        (r' := (29142990574389979 / 20000000000000000 : ℚ))
        (U := (-(5049061054212899413027 / 5000000000000000000000 : ℚ)))
        (U' := (1882410748787100586973 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (3324618322961401 / 10000000000000000 : ℚ))
      (q := (29142990574389979 / 80000000000000000 : ℚ))
      (U := (-(5049061054212899413027 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_12 :
    Uω (aρ 12) (bρ 12) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(12105946844337847702467 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23841599897031647 / 80000000000000000 : ℝ) ≤
      (-(12105946844337847702467 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23841599897031647 / 80000000000000000 : ℚ))
        (r' := (23841599897031647 / 20000000000000000 : ℚ))
        (U := (-(12105946844337847702467 / 10000000000000000000000 : ℚ)))
        (U' := (1756996761662152297533 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (1211485375153409 / 5000000000000000 : ℚ))
      (q := (23841599897031647 / 80000000000000000 : ℚ))
      (U := (-(12105946844337847702467 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_13 :
    Uω (aρ 13) (bρ 13) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(7886087677459839047893 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16523921161995631 / 80000000000000000 : ℝ) ≤
      (-(7886087677459839047893 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16523921161995631 / 80000000000000000 : ℚ))
        (r' := (16523921161995631 / 10000000000000000 : ℚ))
        (U := (-(7886087677459839047893 / 5000000000000000000000 : ℚ)))
        (U' := (2511120027040160952107 / 5000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (39140610900999 / 64000000000000 : ℚ))
      (s := (496466404071407 / 5000000000000000 : ℚ))
      (q := (16523921161995631 / 80000000000000000 : ℚ))
      (U := (-(7886087677459839047893 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_535_14 :
    Uω (aρ 14) (bρ 14) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_535_15 :
    Uω (aρ 15) (bρ 15) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_535_16 :
    Uω (aρ 16) (bρ 16) (39140610900999 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_535 :
    Uρ (39140610900999 / 64000000000000 : ℝ) ≤
      (-(8106826625353221444803 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_535_1 U_535_2 U_535_3 U_535_4 U_535_5 U_535_6 U_535_7 U_535_8 U_535_9 U_535_10
    U_535_11 U_535_12 U_535_13 U_535_14 U_535_15 U_535_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_536_1 :
    Uω (aρ 1) (bρ 1) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(1251385798375307642803 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6061945410410391 / 10000000000000000 : ℝ) ≤
      (-(1251385798375307642803 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6061945410410391 / 10000000000000000 : ℚ))
        (r' := (6061945410410391 / 5000000000000000 : ℚ))
        (U := (-(1251385798375307642803 / 2500000000000000000000 : ℚ)))
        (U' := (481482152374692357197 / 2500000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (3030959370551641 / 5000000000000000 : ℚ))
      (q := (6061945410410391 / 10000000000000000 : ℚ))
      (U := (-(1251385798375307642803 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_2 :
    Uω (aρ 2) (bρ 2) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(5045077302141448493163 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6038027359660779 / 10000000000000000 : ℝ) ≤
      (-(5045077302141448493163 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6038027359660779 / 10000000000000000 : ℚ))
        (r' := (6038027359660779 / 5000000000000000 : ℚ))
        (U := (-(5045077302141448493163 / 10000000000000000000000 : ℚ)))
        (U' := (1886394500858551506837 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (3018925826057029 / 5000000000000000 : ℚ))
      (q := (6038027359660779 / 10000000000000000 : ℚ))
      (U := (-(5045077302141448493163 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_3 :
    Uω (aρ 3) (bρ 3) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(640577567897808385041 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2995094722231893 / 5000000000000000 : ℝ) ≤
      (-(640577567897808385041 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2995094722231893 / 5000000000000000 : ℚ))
        (r' := (2995094722231893 / 2500000000000000 : ℚ))
        (U := (-(640577567897808385041 / 1250000000000000000000 : ℚ)))
        (U' := (225856407477191614959 / 1250000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (748696491008759 / 1250000000000000 : ℚ))
      (q := (2995094722231893 / 5000000000000000 : ℚ))
      (U := (-(640577567897808385041 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_4 :
    Uω (aρ 4) (bρ 4) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(164317269602931110393 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2955366438542201 / 5000000000000000 : ℝ) ≤
      (-(164317269602931110393 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2955366438542201 / 5000000000000000 : ℚ))
        (r' := (2955366438542201 / 2500000000000000 : ℚ))
        (U := (-(164317269602931110393 / 312500000000000000000 : ℚ)))
        (U' := (52291224240818889607 / 312500000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (369309560898519 / 625000000000000 : ℚ))
      (q := (2955366438542201 / 5000000000000000 : ℚ))
      (U := (-(164317269602931110393 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_5 :
    Uω (aρ 5) (bρ 5) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(5465005395609099705269 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11579447202387303 / 20000000000000000 : ℝ) ≤
      (-(5465005395609099705269 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11579447202387303 / 20000000000000000 : ℚ))
        (r' := (11579447202387303 / 10000000000000000 : ℚ))
        (U := (-(5465005395609099705269 / 10000000000000000000000 : ℚ)))
        (U' := (1466466407390900294731 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (5785124341929803 / 10000000000000000 : ℚ))
      (q := (11579447202387303 / 20000000000000000 : ℚ))
      (U := (-(5465005395609099705269 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_6 :
    Uω (aρ 6) (bρ 6) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(1442343826234602812091 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5616156663407157 / 10000000000000000 : ℝ) ≤
      (-(1442343826234602812091 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5616156663407157 / 10000000000000000 : ℚ))
        (r' := (5616156663407157 / 5000000000000000 : ℚ))
        (U := (-(1442343826234602812091 / 2500000000000000000000 : ℚ)))
        (U' := (290524124515397187909 / 2500000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (2802615420748407 / 5000000000000000 : ℚ))
      (q := (5616156663407157 / 10000000000000000 : ℚ))
      (U := (-(1442343826234602812091 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_7 :
    Uω (aρ 7) (bρ 7) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(620024083077386747109 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10758629645066451 / 20000000000000000 : ℝ) ≤
      (-(620024083077386747109 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10758629645066451 / 20000000000000000 : ℚ))
        (r' := (10758629645066451 / 10000000000000000 : ℚ))
        (U := (-(620024083077386747109 / 1000000000000000000000 : ℚ)))
        (U' := (73123097222613252891 / 1000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (5355208540508951 / 10000000000000000 : ℚ))
      (q := (10758629645066451 / 20000000000000000 : ℚ))
      (U := (-(620024083077386747109 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_8 :
    Uω (aρ 8) (bρ 8) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(6792187399728591460427 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1267532366226191 / 2500000000000000 : ℝ) ≤
      (-(6792187399728591460427 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1267532366226191 / 2500000000000000 : ℚ))
        (r' := (1267532366226191 / 1250000000000000 : ℚ))
        (U := (-(6792187399728591460427 / 10000000000000000000000 : ℚ)))
        (U' := (139284403271408539573 / 10000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (1255094869148007 / 2500000000000000 : ℚ))
      (q := (1267532366226191 / 2500000000000000 : ℚ))
      (U := (-(6792187399728591460427 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_9 :
    Uω (aρ 9) (bρ 9) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(7588184633861080601369 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9364386366791683 / 20000000000000000 : ℝ) ≤
      (-(7588184633861080601369 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9364386366791683 / 20000000000000000 : ℚ))
        (r' := (9364386366791683 / 5000000000000000 : ℚ))
        (U := (-(7588184633861080601369 / 10000000000000000000000 : ℚ)))
        (U' := (6274758972138919398631 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (4585472541934183 / 10000000000000000 : ℚ))
      (q := (9364386366791683 / 20000000000000000 : ℚ))
      (U := (-(7588184633861080601369 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_10 :
    Uω (aρ 10) (bρ 10) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(1080892956124258428013 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (105292959172209 / 250000000000000 : ℝ) ≤
      (-(1080892956124258428013 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (105292959172209 / 250000000000000 : ℚ))
        (r' := (105292959172209 / 62500000000000 : ℚ))
        (U := (-(1080892956124258428013 / 1250000000000000000000 : ℚ)))
        (U' := (651974994625741571987 / 1250000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (201654097120711 / 500000000000000 : ℚ))
      (q := (105292959172209 / 250000000000000 : ℚ))
      (U := (-(1080892956124258428013 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_11 :
    Uω (aρ 11) (bρ 11) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(314557910422104071209 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3654647988995821 / 10000000000000000 : ℝ) ≤
      (-(314557910422104071209 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3654647988995821 / 10000000000000000 : ℚ))
        (r' := (3654647988995821 / 2500000000000000 : ℚ))
        (U := (-(314557910422104071209 / 312500000000000000000 : ℚ)))
        (U' := (118659077265395928791 / 312500000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (1668708906417071 / 5000000000000000 : ℚ))
      (q := (3654647988995821 / 10000000000000000 : ℚ))
      (U := (-(314557910422104071209 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_12 :
    Uω (aρ 12) (bρ 12) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(6030863735264409501953 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2993407424564263 / 10000000000000000 : ℝ) ≤
      (-(6030863735264409501953 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2993407424564263 / 10000000000000000 : ℚ))
        (r' := (2993407424564263 / 2500000000000000 : ℚ))
        (U := (-(6030863735264409501953 / 5000000000000000000000 : ℚ)))
        (U' := (900608067735590498047 / 5000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (1219318390328013 / 5000000000000000 : ℚ))
      (q := (2993407424564263 / 10000000000000000 : ℚ))
      (U := (-(6030863735264409501953 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_13 :
    Uω (aρ 13) (bρ 13) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(3133142970538085451271 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (521899230802451 / 2500000000000000 : ℝ) ≤
      (-(3133142970538085451271 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (521899230802451 / 2500000000000000 : ℚ))
        (r' := (521899230802451 / 312500000000000 : ℚ))
        (U := (-(3133142970538085451271 / 2000000000000000000000 : ℚ)))
        (U' := (1025740111261914548729 / 2000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (2450587719121 / 4000000000000 : ℚ))
      (s := (256599379885527 / 2500000000000000 : ℚ))
      (q := (521899230802451 / 2500000000000000 : ℚ))
      (U := (-(3133142970538085451271 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_536_14 :
    Uω (aρ 14) (bρ 14) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_536_15 :
    Uω (aρ 15) (bρ 15) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_536_16 :
    Uω (aρ 16) (bρ 16) (2450587719121 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_536 :
    Uρ (2450587719121 / 4000000000000 : ℝ) ≤
      (-(252550364807948996239 / 312500000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_536_1 U_536_2 U_536_3 U_536_4 U_536_5 U_536_6 U_536_7 U_536_8 U_536_9 U_536_10
    U_536_11 U_536_12 U_536_13 U_536_14 U_536_15 U_536_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_537_1 :
    Uω (aρ 1) (bρ 1) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(2493913571466764627649 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48581554417099593 / 80000000000000000 : ℝ) ≤
      (-(2493913571466764627649 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48581554417099593 / 80000000000000000 : ℚ))
        (r' := (48581554417099593 / 40000000000000000 : ℚ))
        (U := (-(2493913571466764627649 / 5000000000000000000000 : ℚ)))
        (U' := (971822330033235372351 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (759083460004499 / 1250000000000000 : ℚ))
      (q := (48581554417099593 / 80000000000000000 : ℚ))
      (U := (-(2493913571466764627649 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_2 :
    Uω (aρ 2) (bρ 2) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(1005458139663677673063 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48390212131427721 / 80000000000000000 : ℝ) ≤
      (-(1005458139663677673063 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48390212131427721 / 80000000000000000 : ℚ))
        (r' := (48390212131427721 / 40000000000000000 : ℚ))
        (U := (-(1005458139663677673063 / 2000000000000000000000 : ℚ)))
        (U' := (380836220936322326937 / 2000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (756075140141003 / 1250000000000000 : ℚ))
      (q := (48390212131427721 / 80000000000000000 : ℚ))
      (U := (-(1005458139663677673063 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_3 :
    Uω (aρ 3) (bρ 3) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(5106690698961235973153 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48007515161523729 / 80000000000000000 : ℝ) ≤
      (-(5106690698961235973153 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48007515161523729 / 80000000000000000 : ℚ))
        (r' := (48007515161523729 / 40000000000000000 : ℚ))
        (U := (-(5106690698961235973153 / 10000000000000000000000 : ℚ)))
        (U' := (1824781104038764026847 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (3000161492501013 / 5000000000000000 : ℚ))
      (q := (48007515161523729 / 80000000000000000 : ℚ))
      (U := (-(5106690698961235973153 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_4 :
    Uω (aρ 4) (bρ 4) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(5239978385515379585033 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47371879628050141 / 80000000000000000 : ℝ) ≤
      (-(5239978385515379585033 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47371879628050141 / 80000000000000000 : ℚ))
        (r' := (47371879628050141 / 40000000000000000 : ℚ))
        (U := (-(5239978385515379585033 / 10000000000000000000000 : ℚ)))
        (U' := (1691493417484620414967 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (5919708282698629 / 10000000000000000 : ℚ))
      (q := (47371879628050141 / 80000000000000000 : ℚ))
      (U := (-(5239978385515379585033 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_5 :
    Uω (aρ 5) (bρ 5) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(5446442518364453498131 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46403847802755189 / 80000000000000000 : ℝ) ≤
      (-(5446442518364453498131 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46403847802755189 / 80000000000000000 : ℚ))
        (r' := (46403847802755189 / 40000000000000000 : ℚ))
        (U := (-(5446442518364453498131 / 10000000000000000000000 : ℚ)))
        (U' := (1485029284635546501869 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (5795890245709891 / 10000000000000000 : ℚ))
      (q := (46403847802755189 / 80000000000000000 : ℚ))
      (U := (-(5446442518364453498131 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_6 :
    Uω (aρ 6) (bρ 6) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(5750217286790455522099 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (45015411356802417 / 80000000000000000 : ℝ) ≤
      (-(5750217286790455522099 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (45015411356802417 / 80000000000000000 : ℚ))
        (r' := (45015411356802417 / 40000000000000000 : ℚ))
        (U := (-(5750217286790455522099 / 10000000000000000000000 : ℚ)))
        (U' := (1181254516209544477901 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (2808010754680849 / 5000000000000000 : ℚ))
      (q := (45015411356802417 / 80000000000000000 : ℚ))
      (U := (-(5750217286790455522099 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_7 :
    Uω (aρ 7) (bρ 7) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(6180189371123662487857 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43120895641921241 / 80000000000000000 : ℝ) ≤
      (-(6180189371123662487857 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43120895641921241 / 80000000000000000 : ℚ))
        (r' := (43120895641921241 / 40000000000000000 : ℚ))
        (U := (-(6180189371123662487857 / 10000000000000000000000 : ℚ)))
        (U' := (751282431876337512143 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (1341513490350351 / 2500000000000000 : ℚ))
      (q := (43120895641921241 / 80000000000000000 : ℚ))
      (U := (-(6180189371123662487857 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_8 :
    Uω (aρ 8) (bρ 8) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(1692700079319226165529 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40647876771499233 / 80000000000000000 : ℝ) ≤
      (-(1692700079319226165529 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (40647876771499233 / 80000000000000000 : ℚ))
        (r' := (40647876771499233 / 40000000000000000 : ℚ))
        (U := (-(1692700079319226165529 / 2500000000000000000000 : ℚ)))
        (U' := (40167871430773834471 / 2500000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (2515670447567951 / 5000000000000000 : ℚ))
      (q := (40647876771499233 / 80000000000000000 : ℚ))
      (U := (-(1692700079319226165529 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_9 :
    Uω (aρ 9) (bρ 9) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(3782386067554484225809 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1501813827273289 / 3200000000000000 : ℝ) ≤
      (-(3782386067554484225809 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1501813827273289 / 3200000000000000 : ℚ))
        (r' := (1501813827273289 / 800000000000000 : ℚ))
        (U := (-(3782386067554484225809 / 5000000000000000000000 : ℚ)))
        (U' := (3149085735445515774191 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (91933475021583 / 200000000000000 : ℚ))
      (q := (1501813827273289 / 3200000000000000 : ℚ))
      (U := (-(3782386067554484225809 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_10 :
    Uω (aρ 10) (bρ 10) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(8620530541481646251921 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33783535891237313 / 80000000000000000 : ℝ) ≤
      (-(8620530541481646251921 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (33783535891237313 / 80000000000000000 : ℚ))
        (r' := (33783535891237313 / 20000000000000000 : ℚ))
        (U := (-(8620530541481646251921 / 10000000000000000000000 : ℚ)))
        (U' := (5242413064518353748079 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (2022390168462711 / 5000000000000000 : ℚ))
      (q := (33783535891237313 / 80000000000000000 : ℚ))
      (U := (-(8620530541481646251921 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_11 :
    Uω (aρ 11) (bρ 11) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(2508426902235644193011 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29331319594314289 / 80000000000000000 : ℝ) ≤
      (-(2508426902235644193011 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (29331319594314289 / 80000000000000000 : ℚ))
        (r' := (29331319594314289 / 20000000000000000 : ℚ))
        (U := (-(2508426902235644193011 / 2500000000000000000000 : ℚ)))
        (U' := (957308999264355806989 / 2500000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (1675101444449833 / 5000000000000000 : ℚ))
      (q := (29331319594314289 / 80000000000000000 : ℚ))
      (U := (-(2508426902235644193011 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_12 :
    Uω (aρ 12) (bρ 12) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(1502223847783784689383 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4810541441066241 / 16000000000000000 : ℝ) ≤
      (-(1502223847783784689383 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4810541441066241 / 16000000000000000 : ℚ))
        (r' := (4810541441066241 / 4000000000000000 : ℚ))
        (U := (-(1502223847783784689383 / 1250000000000000000000 : ℚ)))
        (U' := (230644102966215310617 / 1250000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (490849977667779 / 2000000000000000 : ℚ))
      (q := (4810541441066241 / 16000000000000000 : ℚ))
      (U := (-(1502223847783784689383 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_13 :
    Uω (aρ 13) (bρ 13) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(15562622929320063846659 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (674953496939277 / 3200000000000000 : ℝ) ≤
      (-(15562622929320063846659 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (674953496939277 / 3200000000000000 : ℚ))
        (r' := (674953496939277 / 400000000000000 : ℚ))
        (U := (-(15562622929320063846659 / 10000000000000000000000 : ℚ)))
        (U' := (5231792479679936153341 / 10000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (39278196110873 / 64000000000000 : ℚ))
      (s := (42356567378863 / 400000000000000 : ℚ))
      (q := (674953496939277 / 3200000000000000 : ℚ))
      (U := (-(15562622929320063846659 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_537_14 :
    Uω (aρ 14) (bρ 14) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_537_15 :
    Uω (aρ 15) (bρ 15) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_537_16 :
    Uω (aρ 16) (bρ 16) (39278196110873 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_537 :
    Uρ (39278196110873 / 64000000000000 : ℝ) ≤
      (-(4028326837852990601667 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_537_1 U_537_2 U_537_3 U_537_4 U_537_5 U_537_6 U_537_7 U_537_8 U_537_9 U_537_10
    U_537_11 U_537_12 U_537_13 U_537_14 U_537_15 U_537_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_538_1 :
    Uω (aρ 1) (bρ 1) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(4970142422987990689033 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24333772774790763 / 40000000000000000 : ℝ) ≤
      (-(4970142422987990689033 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24333772774790763 / 40000000000000000 : ℚ))
        (r' := (24333772774790763 / 20000000000000000 : ℚ))
        (U := (-(4970142422987990689033 / 10000000000000000000000 : ℚ)))
        (U' := (1961329380012009310967 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (6083416618635069 / 10000000000000000 : ℚ))
      (q := (24333772774790763 / 40000000000000000 : ℚ))
      (U := (-(4970142422987990689033 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_2 :
    Uω (aρ 2) (bρ 2) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(626191959561132738727 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24238102688353259 / 40000000000000000 : ℝ) ≤
      (-(626191959561132738727 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24238102688353259 / 40000000000000000 : ℚ))
        (r' := (24238102688353259 / 20000000000000000 : ℚ))
        (U := (-(626191959561132738727 / 1250000000000000000000 : ℚ)))
        (U' := (240242015813867261273 / 1250000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (6059350587926317 / 10000000000000000 : ℚ))
      (q := (24238102688353259 / 40000000000000000 : ℚ))
      (U := (-(626191959561132738727 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_3 :
    Uω (aρ 3) (bρ 3) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(5088792951723855824927 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24046757367842257 / 40000000000000000 : ℝ) ≤
      (-(5088792951723855824927 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24046757367842257 / 40000000000000000 : ℚ))
        (r' := (24046757367842257 / 20000000000000000 : ℚ))
        (U := (-(5088792951723855824927 / 10000000000000000000000 : ℚ)))
        (U' := (1842678851276144175073 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (375692127126301 / 625000000000000 : ℚ))
      (q := (24046757367842257 / 40000000000000000 : ℚ))
      (U := (-(5088792951723855824927 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_4 :
    Uω (aρ 4) (bρ 4) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(1305459283471519444757 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23728948072836411 / 40000000000000000 : ℝ) ≤
      (-(1305459283471519444757 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23728948072836411 / 40000000000000000 : ℚ))
        (r' := (23728948072836411 / 20000000000000000 : ℚ))
        (U := (-(1305459283471519444757 / 2500000000000000000000 : ℚ)))
        (U' := (427408667278480555243 / 2500000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (5930463567582893 / 10000000000000000 : ℚ))
      (q := (23728948072836411 / 40000000000000000 : ℚ))
      (U := (-(1305459283471519444757 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_5 :
    Uω (aρ 5) (bρ 5) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(339244630606834053439 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23244953271565087 / 40000000000000000 : ℝ) ≤
      (-(339244630606834053439 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23244953271565087 / 40000000000000000 : ℚ))
        (r' := (23244953271565087 / 20000000000000000 : ℚ))
        (U := (-(339244630606834053439 / 625000000000000000000 : ℚ)))
        (U' := (93972357080665946561 / 625000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (5806656086282231 / 10000000000000000 : ℚ))
      (q := (23244953271565087 / 40000000000000000 : ℚ))
      (U := (-(339244630606834053439 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_6 :
    Uω (aρ 6) (bρ 6) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(2865548021714676276341 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4510156876594629 / 8000000000000000 : ℝ) ≤
      (-(2865548021714676276341 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4510156876594629 / 8000000000000000 : ℚ))
        (r' := (4510156876594629 / 4000000000000000 : ℚ))
        (U := (-(2865548021714676276341 / 5000000000000000000000 : ℚ)))
        (U' := (600187879785323723659 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (281340600856313 / 500000000000000 : ℚ))
      (q := (4510156876594629 / 8000000000000000 : ℚ))
      (U := (-(2865548021714676276341 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_7 :
    Uω (aρ 7) (bρ 7) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(24640713584814710663 / 40000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21603635576063999 / 40000000000000000 : ℝ) ≤
      (-(24640713584814710663 / 40000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21603635576063999 / 40000000000000000 : ℚ))
        (r' := (21603635576063999 / 20000000000000000 : ℚ))
        (U := (-(24640713584814710663 / 40000000000000000000 : ℚ)))
        (U' := (3085173627185289337 / 40000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (5376898994431687 / 10000000000000000 : ℚ))
      (q := (21603635576063999 / 40000000000000000 : ℚ))
      (U := (-(24640713584814710663 / 40000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_8 :
    Uω (aρ 8) (bρ 8) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(6749459776710677993977 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20367357081351947 / 40000000000000000 : ℝ) ≤
      (-(6749459776710677993977 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20367357081351947 / 40000000000000000 : ℚ))
        (r' := (20367357081351947 / 20000000000000000 : ℚ))
        (U := (-(6749459776710677993977 / 10000000000000000000000 : ℚ)))
        (U' := (182012026289322006023 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (5042301398415661 / 10000000000000000 : ℚ))
      (q := (20367357081351947 / 40000000000000000 : ℚ))
      (U := (-(6749459776710677993977 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_9 :
    Uω (aρ 9) (bρ 9) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(3770708306633194469347 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18816568638483439 / 40000000000000000 : ℝ) ≤
      (-(3770708306633194469347 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18816568638483439 / 40000000000000000 : ℚ))
        (r' := (18816568638483439 / 10000000000000000 : ℚ))
        (U := (-(3770708306633194469347 / 5000000000000000000000 : ℚ)))
        (U' := (3160763496366805530653 / 5000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (4607872805341407 / 10000000000000000 : ℚ))
      (q := (18816568638483439 / 40000000000000000 : ℚ))
      (U := (-(3770708306633194469347 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_10 :
    Uω (aρ 10) (bρ 10) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(8593994276661595780249 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (677466076586923 / 1600000000000000 : ℝ) ≤
      (-(8593994276661595780249 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (677466076586923 / 1600000000000000 : ℚ))
        (r' := (677466076586923 / 400000000000000 : ℚ))
        (U := (-(8593994276661595780249 / 10000000000000000000000 : ℚ)))
        (U' := (5268949329338404219751 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (162258939077249 / 400000000000000 : ℚ))
      (q := (677466076586923 / 1600000000000000 : ℚ))
      (U := (-(8593994276661595780249 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_11 :
    Uω (aρ 11) (bρ 11) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(10001684457041864999147 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14712699139499919 / 40000000000000000 : ℝ) ≤
      (-(10001684457041864999147 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (14712699139499919 / 40000000000000000 : ℚ))
        (r' := (14712699139499919 / 10000000000000000 : ℚ))
        (U := (-(10001684457041864999147 / 10000000000000000000000 : ℚ)))
        (U' := (3861259148958135000853 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (3362973715549647 / 10000000000000000 : ℚ))
      (q := (14712699139499919 / 40000000000000000 : ℚ))
      (U := (-(10001684457041864999147 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_12 :
    Uω (aρ 12) (bρ 12) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(5987066129331995198681 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12078973669071019 / 40000000000000000 : ℝ) ≤
      (-(5987066129331995198681 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12078973669071019 / 40000000000000000 : ℚ))
        (r' := (12078973669071019 / 10000000000000000 : ℚ))
        (U := (-(5987066129331995198681 / 5000000000000000000000 : ℚ)))
        (U' := (944405673668004801319 / 5000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (2469811077020197 / 10000000000000000 : ℚ))
      (q := (12078973669071019 / 40000000000000000 : ℚ))
      (U := (-(5987066129331995198681 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_13 :
    Uω (aρ 13) (bρ 13) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(3092521747675457896549 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8521723247589617 / 40000000000000000 : ℝ) ≤
      (-(3092521747675457896549 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8521723247589617 / 40000000000000000 : ℚ))
        (r' := (8521723247589617 / 5000000000000000 : ℚ))
        (U := (-(3092521747675457896549 / 2000000000000000000000 : ℚ)))
        (U' := (1066361334124542103451 / 2000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (3934698871581 / 6400000000000 : ℚ))
      (s := (17040118873039 / 156250000000000 : ℚ))
      (q := (8521723247589617 / 40000000000000000 : ℚ))
      (U := (-(3092521747675457896549 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_538_14 :
    Uω (aρ 14) (bρ 14) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_538_15 :
    Uω (aρ 15) (bρ 15) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_538_16 :
    Uω (aρ 16) (bρ 16) (3934698871581 / 6400000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_538 :
    Uρ (3934698871581 / 6400000000000 : ℝ) ≤
      (-(1003991872383418357177 / 1250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_538_1 U_538_2 U_538_3 U_538_4 U_538_5 U_538_6 U_538_7 U_538_8 U_538_9 U_538_10
    U_538_11 U_538_12 U_538_13 U_538_14 U_538_15 U_538_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_539_1 :
    Uω (aρ 1) (bρ 1) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(39619911384348771533 / 80000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48753536680735983 / 80000000000000000 : ℝ) ≤
      (-(39619911384348771533 / 80000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48753536680735983 / 80000000000000000 : ℚ))
        (r' := (48753536680735983 / 40000000000000000 : ℚ))
        (U := (-(39619911384348771533 / 80000000000000000000 : ℚ)))
        (U' := (15831863039651228467 / 80000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (6094165556902277 / 10000000000000000 : ℚ))
      (q := (48753536680735983 / 80000000000000000 : ℚ))
      (U := (-(39619911384348771533 / 80000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_2 :
    Uω (aρ 2) (bρ 2) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(4991812124691438887987 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48562198613169711 / 80000000000000000 : ℝ) ≤
      (-(4991812124691438887987 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48562198613169711 / 80000000000000000 : ℚ))
        (r' := (48562198613169711 / 40000000000000000 : ℚ))
        (U := (-(4991812124691438887987 / 10000000000000000000000 : ℚ)))
        (U' := (1939659678308561112013 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (6070100052520709 / 10000000000000000 : ℚ))
      (q := (48562198613169711 / 80000000000000000 : ℚ))
      (U := (-(4991812124691438887987 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_3 :
    Uω (aρ 3) (bρ 3) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(2535463593367915656409 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48179514278362183 / 80000000000000000 : ℝ) ≤
      (-(2535463593367915656409 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48179514278362183 / 80000000000000000 : ℚ))
        (r' := (48179514278362183 / 40000000000000000 : ℚ))
        (U := (-(2535463593367915656409 / 5000000000000000000000 : ℚ)))
        (U' := (930272308132084343591 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (6021825075168827 / 10000000000000000 : ℚ))
      (q := (48179514278362183 / 80000000000000000 : ℚ))
      (U := (-(2535463593367915656409 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_4 :
    Uω (aρ 4) (bρ 4) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(162616523524473707163 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47543912570052419 / 80000000000000000 : ℝ) ≤
      (-(162616523524473707163 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47543912570052419 / 80000000000000000 : ℚ))
        (r' := (47543912570052419 / 40000000000000000 : ℚ))
        (U := (-(162616523524473707163 / 312500000000000000000 : ℚ)))
        (U' := (53991970319276292837 / 312500000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (2970609414578193 / 5000000000000000 : ℚ))
      (q := (47543912570052419 / 80000000000000000 : ℚ))
      (U := (-(162616523524473707163 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_5 :
    Uω (aρ 5) (bρ 5) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(5409419981822095878167 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46575965032077847 / 80000000000000000 : ℝ) ≤
      (-(5409419981822095878167 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46575965032077847 / 80000000000000000 : ℚ))
        (r' := (46575965032077847 / 40000000000000000 : ℚ))
        (U := (-(5409419981822095878167 / 10000000000000000000000 : ℚ)))
        (U' := (1522051821177904121833 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (5817421863997743 / 10000000000000000 : ℚ))
      (q := (46575965032077847 / 80000000000000000 : ℚ))
      (U := (-(5409419981822095878167 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_6 :
    Uω (aρ 6) (bρ 6) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(2856005716701236298161 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (45187725538366107 / 80000000000000000 : ℝ) ≤
      (-(2856005716701236298161 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (45187725538366107 / 80000000000000000 : ℚ))
        (r' := (45187725538366107 / 40000000000000000 : ℚ))
        (U := (-(2856005716701236298161 / 5000000000000000000000 : ℚ)))
        (U' := (609730184798763701839 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (352350147856863 / 625000000000000 : ℚ))
      (q := (45187725538366107 / 80000000000000000 : ℚ))
      (U := (-(2856005716701236298161 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_7 :
    Uω (aρ 7) (bρ 7) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(614020774142777776231 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43293645120254843 / 80000000000000000 : ℝ) ≤
      (-(614020774142777776231 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43293645120254843 / 80000000000000000 : ℚ))
        (r' := (43293645120254843 / 40000000000000000 : ℚ))
        (U := (-(614020774142777776231 / 1000000000000000000000 : ℚ)))
        (U' := (79126406157222223769 / 1000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (673467955242749 / 1250000000000000 : ℚ))
      (q := (43293645120254843 / 80000000000000000 : ℚ))
      (U := (-(614020774142777776231 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_8 :
    Uω (aρ 8) (bρ 8) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(6728165572055259940237 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40821547916674547 / 80000000000000000 : ℝ) ≤
      (-(6728165572055259940237 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (40821547916674547 / 80000000000000000 : ℚ))
        (r' := (40821547916674547 / 40000000000000000 : ℚ))
        (U := (-(6728165572055259940237 / 10000000000000000000000 : ℚ)))
        (U' := (203306230944740059763 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (2526630496193459 / 5000000000000000 : ℚ))
      (q := (40821547916674547 / 80000000000000000 : ℚ))
      (U := (-(6728165572055259940237 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_9 :
    Uω (aρ 9) (bρ 9) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(7518117780844264344539 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (37720920315265511 / 80000000000000000 : ℝ) ≤
      (-(7518117780844264344539 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (37720920315265511 / 80000000000000000 : ℚ))
        (r' := (37720920315265511 / 20000000000000000 : ℚ))
        (U := (-(7518117780844264344539 / 10000000000000000000000 : ℚ)))
        (U' := (6344825825155735655461 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (4619069720394659 / 10000000000000000 : ℚ))
      (q := (37720920315265511 / 80000000000000000 : ℚ))
      (U := (-(7518117780844264344539 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_10 :
    Uω (aρ 10) (bρ 10) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(8567534377982396619123 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33963050930670051 / 80000000000000000 : ℝ) ≤
      (-(8567534377982396619123 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (33963050930670051 / 80000000000000000 : ℚ))
        (r' := (33963050930670051 / 20000000000000000 : ℚ))
        (U := (-(8567534377982396619123 / 10000000000000000000000 : ℚ)))
        (U' := (5295409228017603380877 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (2034080703870397 / 5000000000000000 : ℚ))
      (q := (33963050930670051 / 80000000000000000 : ℚ))
      (U := (-(8567534377982396619123 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_11 :
    Uω (aρ 11) (bρ 11) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(1993956523096417586819 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29519420612911899 / 80000000000000000 : ℝ) ≤
      (-(1993956523096417586819 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (29519420612911899 / 80000000000000000 : ℚ))
        (r' := (29519420612911899 / 20000000000000000 : ℚ))
        (U := (-(1993956523096417586819 / 2000000000000000000000 : ℚ)))
        (U' := (778632198103582413181 / 2000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (210983153406641 / 625000000000000 : ℚ))
      (q := (29519420612911899 / 80000000000000000 : ℚ))
      (U := (-(1993956523096417586819 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_12 :
    Uω (aρ 12) (bρ 12) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(745671718695141265711 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24262983695874167 / 80000000000000000 : ℝ) ≤
      (-(745671718695141265711 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24262983695874167 / 80000000000000000 : ℚ))
        (r' := (24262983695874167 / 20000000000000000 : ℚ))
        (U := (-(745671718695141265711 / 625000000000000000000 : ℚ)))
        (U' := (120762256679858734289 / 625000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (2485321321931823 / 10000000000000000 : ℚ))
      (q := (24262983695874167 / 80000000000000000 : ℚ))
      (U := (-(745671718695141265711 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_13 :
    Uω (aρ 13) (bρ 13) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(7682710624029974679527 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17209894999780123 / 80000000000000000 : ℝ) ≤
      (-(7682710624029974679527 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17209894999780123 / 80000000000000000 : ℚ))
        (r' := (17209894999780123 / 10000000000000000 : ℚ))
        (U := (-(7682710624029974679527 / 5000000000000000000000 : ℚ)))
        (U' := (2714497080470025320473 / 5000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (39415781320747 / 64000000000000 : ℚ))
      (s := (70089430593957 / 625000000000000 : ℚ))
      (q := (17209894999780123 / 80000000000000000 : ℚ))
      (U := (-(7682710624029974679527 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_539_14 :
    Uω (aρ 14) (bρ 14) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_539_15 :
    Uω (aρ 15) (bρ 15) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_539_16 :
    Uω (aρ 16) (bρ 16) (39415781320747 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_539 :
    Uρ (39415781320747 / 64000000000000 : ℝ) ≤
      (-(8007440285446487712989 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_539_1 U_539_2 U_539_3 U_539_4 U_539_5 U_539_6 U_539_7 U_539_8 U_539_9 U_539_10
    U_539_11 U_539_12 U_539_13 U_539_14 U_539_15 U_539_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_540_1 :
    Uω (aρ 1) (bρ 1) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(4934866533064163862467 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2441976390528499 / 4000000000000000 : ℝ) ≤
      (-(4934866533064163862467 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2441976390528499 / 4000000000000000 : ℚ))
        (r' := (2441976390528499 / 2000000000000000 : ℚ))
        (U := (-(4934866533064163862467 / 10000000000000000000000 : ℚ)))
        (U' := (1996605269935836137533 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (610491449483937 / 1000000000000000 : ℚ))
      (q := (2441976390528499 / 4000000000000000 : ℚ))
      (U := (-(4934866533064163862467 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_2 :
    Uω (aρ 2) (bρ 2) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(497411993155784997629 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3040511990054003 / 5000000000000000 : ℝ) ≤
      (-(497411993155784997629 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3040511990054003 / 5000000000000000 : ℚ))
        (r' := (3040511990054003 / 2500000000000000 : ℚ))
        (U := (-(497411993155784997629 / 1000000000000000000000 : ℚ)))
        (U' := (195735187144215002371 / 1000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (6080849514922887 / 10000000000000000 : ℚ))
      (q := (3040511990054003 / 5000000000000000 : ℚ))
      (U := (-(497411993155784997629 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_3 :
    Uω (aρ 3) (bρ 3) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(631636661234611895621 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (377074326482227 / 625000000000000 : ℝ) ≤
      (-(631636661234611895621 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (377074326482227 / 625000000000000 : ℚ))
        (r' := (377074326482227 / 312500000000000 : ℚ))
        (U := (-(631636661234611895621 / 1250000000000000000000 : ℚ)))
        (U' := (234797314140388104379 / 1250000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (6032576108488139 / 10000000000000000 : ℚ))
      (q := (377074326482227 / 625000000000000 : ℚ))
      (U := (-(631636661234611895621 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_4 :
    Uω (aρ 4) (bρ 4) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(648206640404216422783 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29768705563559 / 50000000000000 : ℝ) ≤
      (-(648206640404216422783 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (29768705563559 / 50000000000000 : ℚ))
        (r' := (29768705563559 / 25000000000000 : ℚ))
        (U := (-(648206640404216422783 / 1250000000000000000000 : ℚ)))
        (U' := (218227334970783577217 / 1250000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (238078962701819 / 400000000000000 : ℚ))
      (q := (29768705563559 / 50000000000000 : ℚ))
      (U := (-(648206640404216422783 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_5 :
    Uω (aρ 5) (bρ 5) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(5390960067592240995977 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11665505817747879 / 20000000000000000 : ℝ) ≤
      (-(5390960067592240995977 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11665505817747879 / 20000000000000000 : ℚ))
        (r' := (11665505817747879 / 10000000000000000 : ℚ))
        (U := (-(5390960067592240995977 / 10000000000000000000000 : ℚ)))
        (U' := (1540511735407759004023 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (2914093789602377 / 5000000000000000 : ℚ))
      (q := (11665505817747879 / 20000000000000000 : ℚ))
      (U := (-(5390960067592240995977 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_6 :
    Uω (aρ 6) (bρ 6) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(2846481658037417445579 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5659235209713869 / 10000000000000000 : ℝ) ≤
      (-(2846481658037417445579 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5659235209713869 / 10000000000000000 : ℚ))
        (r' := (5659235209713869 / 5000000000000000 : ℚ))
        (U := (-(2846481658037417445579 / 5000000000000000000000 : ℚ)))
        (U' := (619254243462582554421 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (5648392556024613 / 10000000000000000 : ℚ))
      (q := (5659235209713869 / 10000000000000000 : ℚ))
      (U := (-(2846481658037417445579 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_7 :
    Uω (aρ 7) (bρ 7) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(6120277243219995072763 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5422502194449367 / 10000000000000000 : ℝ) ≤
      (-(6120277243219995072763 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5422502194449367 / 10000000000000000 : ℚ))
        (r' := (5422502194449367 / 5000000000000000 : ℚ))
        (U := (-(6120277243219995072763 / 10000000000000000000000 : ℚ)))
        (U' := (811194559780004927237 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (5398587906255609 / 10000000000000000 : ℚ))
      (q := (5422502194449367 / 10000000000000000 : ℚ))
      (U := (-(6120277243219995072763 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_8 :
    Uω (aρ 8) (bρ 8) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(670691749872474504841 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5113547257128181 / 10000000000000000 : ℝ) ≤
      (-(670691749872474504841 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5113547257128181 / 10000000000000000 : ℚ))
        (r' := (5113547257128181 / 5000000000000000 : ℚ))
        (U := (-(670691749872474504841 / 1000000000000000000000 : ℚ)))
        (U' := (22455430427525495159 / 1000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (5064219682953237 / 10000000000000000 : ℚ))
      (q := (5113547257128181 / 10000000000000000 : ℚ))
      (U := (-(670691749872474504841 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_9 :
    Uω (aρ 9) (bρ 9) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(7494875352599199835211 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (295380428584411 / 625000000000000 : ℝ) ≤
      (-(7494875352599199835211 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (295380428584411 / 625000000000000 : ℚ))
        (r' := (295380428584411 / 156250000000000 : ℚ))
        (U := (-(7494875352599199835211 / 10000000000000000000000 : ℚ)))
        (U' := (6368068253400800164789 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (4630264511758027 / 10000000000000000 : ℚ))
      (q := (295380428584411 / 625000000000000 : ℚ))
      (U := (-(7494875352599199835211 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_10 :
    Uω (aρ 10) (bρ 10) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(8541150373580887895981 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4256597171786073 / 10000000000000000 : ℝ) ≤
      (-(8541150373580887895981 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4256597171786073 / 10000000000000000 : ℚ))
        (r' := (4256597171786073 / 2500000000000000 : ℚ))
        (U := (-(8541150373580887895981 / 10000000000000000000000 : ℚ)))
        (U' := (5321793232419112104019 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (4079844174124021 / 10000000000000000 : ℚ))
      (q := (4256597171786073 / 10000000000000000 : ℚ))
      (U := (-(8541150373580887895981 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_11 :
    Uω (aρ 11) (bρ 11) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(397520041479983402797 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7403346808122357 / 20000000000000000 : ℝ) ≤
      (-(397520041479983402797 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7403346808122357 / 20000000000000000 : ℚ))
        (r' := (7403346808122357 / 5000000000000000 : ℚ))
        (U := (-(397520041479983402797 / 400000000000000000000 : ℚ)))
        (U' := (156997702760016597203 / 400000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (26472447381869 / 78125000000000 : ℚ))
      (q := (7403346808122357 / 20000000000000000 : ℚ))
      (U := (-(397520041479983402797 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_12 :
    Uω (aρ 12) (bρ 12) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(475505288755951282507 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3045977508758077 / 10000000000000000 : ℝ) ≤
      (-(475505288755951282507 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3045977508758077 / 10000000000000000 : ℚ))
        (r' := (3045977508758077 / 2500000000000000 : ℚ))
        (U := (-(475505288755951282507 / 400000000000000000000 : ℚ)))
        (U' := (79012455484048717493 / 400000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (2500781570958029 / 10000000000000000 : ℚ))
      (q := (3045977508758077 / 10000000000000000 : ℚ))
      (U := (-(475505288755951282507 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_13 :
    Uω (aρ 13) (bρ 13) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(7635420998099539770937 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2171679633044277 / 10000000000000000 : ℝ) ≤
      (-(7635420998099539770937 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2171679633044277 / 10000000000000000 : ℚ))
        (r' := (2171679633044277 / 1250000000000000 : ℚ))
        (U := (-(7635420998099539770937 / 5000000000000000000000 : ℚ)))
        (U' := (2761786706400460229063 / 5000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (9871143481421 / 16000000000000 : ℚ))
      (s := (1151567561125429 / 10000000000000000 : ℚ))
      (q := (2171679633044277 / 10000000000000000 : ℚ))
      (U := (-(7635420998099539770937 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_540_14 :
    Uω (aρ 14) (bρ 14) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_540_15 :
    Uω (aρ 15) (bρ 15) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_540_16 :
    Uω (aρ 16) (bρ 16) (9871143481421 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_540 :
    Uρ (9871143481421 / 16000000000000 : ℝ) ≤
      (-(1596631244612458406567 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_540_1 U_540_2 U_540_3 U_540_4 U_540_5 U_540_6 U_540_7 U_540_8 U_540_9 U_540_10
    U_540_11 U_540_12 U_540_13 U_540_14 U_540_15 U_540_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_541_1 :
    Uω (aρ 1) (bρ 1) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(4917275143594234884783 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48925518939090473 / 80000000000000000 : ℝ) ≤
      (-(4917275143594234884783 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48925518939090473 / 80000000000000000 : ℚ))
        (r' := (48925518939090473 / 40000000000000000 : ℚ))
        (U := (-(4917275143594234884783 / 10000000000000000000000 : ℚ)))
        (U' := (2014196659405765115217 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (6115663432448087 / 10000000000000000 : ℚ))
      (q := (48925518939090473 / 80000000000000000 : ℚ))
      (U := (-(4917275143594234884783 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_2 :
    Uω (aρ 2) (bρ 2) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(77444671661105992217 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48734185059835957 / 80000000000000000 : ℝ) ≤
      (-(77444671661105992217 / 156250000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48734185059835957 / 80000000000000000 : ℚ))
        (r' := (48734185059835957 / 40000000000000000 : ℚ))
        (U := (-(77444671661105992217 / 156250000000000000000 : ℚ)))
        (U' := (30859575260769007783 / 156250000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (3045799487572229 / 5000000000000000 : ℚ))
      (q := (48734185059835957 / 80000000000000000 : ℚ))
      (U := (-(77444671661105992217 / 156250000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_3 :
    Uω (aρ 3) (bρ 3) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(2517645573818314008889 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48351513269940257 / 80000000000000000 : ℝ) ≤
      (-(2517645573818314008889 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48351513269940257 / 80000000000000000 : ℚ))
        (r' := (48351513269940257 / 40000000000000000 : ℚ))
        (U := (-(2517645573818314008889 / 5000000000000000000000 : ℚ)))
        (U' := (948090327681685991111 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (6043327134020533 / 10000000000000000 : ℚ))
      (q := (48351513269940257 / 80000000000000000 : ℚ))
      (U := (-(2517645573818314008889 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_4 :
    Uω (aρ 4) (bρ 4) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(2583805063455020443923 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47715945141100593 / 80000000000000000 : ℝ) ≤
      (-(2583805063455020443923 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47715945141100593 / 80000000000000000 : ℚ))
        (r' := (47715945141100593 / 40000000000000000 : ℚ))
        (U := (-(2583805063455020443923 / 5000000000000000000000 : ℚ)))
        (U' := (881930838044979556077 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (5962729282875617 / 10000000000000000 : ℚ))
      (q := (47715945141100593 / 80000000000000000 : ℚ))
      (U := (-(2583805063455020443923 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_5 :
    Uω (aρ 5) (bρ 5) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(83945847197113369509 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46748081261254197 / 80000000000000000 : ℝ) ≤
      (-(83945847197113369509 / 156250000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46748081261254197 / 80000000000000000 : ℚ))
        (r' := (46748081261254197 / 40000000000000000 : ℚ))
        (U := (-(83945847197113369509 / 156250000000000000000 : ℚ)))
        (U' := (24358399724761630491 / 156250000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (2919476616124509 / 5000000000000000 : ℚ))
      (q := (46748081261254197 / 80000000000000000 : ℚ))
      (U := (-(83945847197113369509 / 156250000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_6 :
    Uω (aρ 6) (bρ 6) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(354621971976424965729 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (45360037187602009 / 80000000000000000 : ℝ) ≤
      (-(354621971976424965729 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (45360037187602009 / 80000000000000000 : ℚ))
        (r' := (45360037187602009 / 40000000000000000 : ℚ))
        (U := (-(354621971976424965729 / 625000000000000000000 : ℚ)))
        (U' := (78595015711075034271 / 625000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (5659182588975971 / 10000000000000000 : ℚ))
      (q := (45360037187602009 / 80000000000000000 : ℚ))
      (U := (-(354621971976424965729 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_7 :
    Uω (aρ 7) (bρ 7) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(3050193369503106150261 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43466388467366593 / 80000000000000000 : ℝ) ≤
      (-(3050193369503106150261 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43466388467366593 / 80000000000000000 : ℚ))
        (r' := (43466388467366593 / 40000000000000000 : ℚ))
        (U := (-(3050193369503106150261 / 5000000000000000000000 : ℚ)))
        (U' := (415542531996893849739 / 5000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (5409431789677117 / 10000000000000000 : ℚ))
      (q := (43466388467366593 / 80000000000000000 : ℚ))
      (U := (-(3050193369503106150261 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_8 :
    Uω (aρ 8) (bρ 8) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(3342857676754653328359 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40995204607164973 / 80000000000000000 : ℝ) ≤
      (-(3342857676754653328359 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (40995204607164973 / 80000000000000000 : ℚ))
        (r' := (40995204607164973 / 40000000000000000 : ℚ))
        (U := (-(3342857676754653328359 / 5000000000000000000000 : ℚ)))
        (U' := (122878224745346671641 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (634397184495839 / 1250000000000000 : ℚ))
      (q := (40995204607164973 / 80000000000000000 : ℚ))
      (U := (-(3342857676754653328359 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_9 :
    Uω (aρ 9) (bρ 9) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(116745141336085632999 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1515858438762001 / 3200000000000000 : ℝ) ≤
      (-(116745141336085632999 / 156250000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1515858438762001 / 3200000000000000 : ℚ))
        (r' := (1515858438762001 / 800000000000000 : ℚ))
        (U := (-(116745141336085632999 / 156250000000000000000 : ℚ)))
        (U' := (99863352507664367001 / 156250000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (185658287791919 / 400000000000000 : ℚ))
      (q := (1515858438762001 / 3200000000000000 : ℚ))
      (U := (-(116745141336085632999 / 156250000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_10 :
    Uω (aρ 10) (bρ 10) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(8514841796218230196619 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (34142483337157277 / 80000000000000000 : ℝ) ≤
      (-(8514841796218230196619 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (34142483337157277 / 80000000000000000 : ℚ))
        (r' := (34142483337157277 / 20000000000000000 : ℚ))
        (U := (-(8514841796218230196619 / 10000000000000000000000 : ℚ)))
        (U' := (5348101809781769803381 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (1022880455079947 / 2500000000000000 : ℚ))
      (q := (34142483337157277 / 80000000000000000 : ℚ))
      (U := (-(8514841796218230196619 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_11 :
    Uω (aρ 11) (bρ 11) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(9906338689090923457797 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1188291950557753 / 3200000000000000 : ℝ) ≤
      (-(9906338689090923457797 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1188291950557753 / 3200000000000000 : ℚ))
        (r' := (1188291950557753 / 800000000000000 : ℚ))
        (U := (-(9906338689090923457797 / 10000000000000000000000 : ℚ)))
        (U' := (3956604916909076542203 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (136048092128857 / 400000000000000 : ℚ))
      (q := (1188291950557753 / 3200000000000000 : ℚ))
      (U := (-(9906338689090923457797 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_12 :
    Uω (aρ 12) (bρ 12) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(2368956448966278179891 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24472460146992109 / 80000000000000000 : ℝ) ≤
      (-(2368956448966278179891 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24472460146992109 / 80000000000000000 : ℚ))
        (r' := (24472460146992109 / 20000000000000000 : ℚ))
        (U := (-(2368956448966278179891 / 2000000000000000000000 : ℚ)))
        (U' := (403632272233721820109 / 2000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (157262046604281 / 625000000000000 : ℚ))
      (q := (24472460146992109 / 80000000000000000 : ℚ))
      (U := (-(2368956448966278179891 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_13 :
    Uω (aρ 13) (bρ 13) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(15178679457575972544311 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17534295186849661 / 80000000000000000 : ℝ) ≤
      (-(15178679457575972544311 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17534295186849661 / 80000000000000000 : ℚ))
        (r' := (17534295186849661 / 10000000000000000 : ℚ))
        (U := (-(15178679457575972544311 / 10000000000000000000000 : ℚ)))
        (U' := (5615735951424027455689 / 10000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (39553366530621 / 64000000000000 : ℚ))
      (s := (295258311806971 / 2500000000000000 : ℚ))
      (q := (17534295186849661 / 80000000000000000 : ℚ))
      (U := (-(15178679457575972544311 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_541_14 :
    Uω (aρ 14) (bρ 14) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_541_15 :
    Uω (aρ 15) (bρ 15) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_541_16 :
    Uω (aρ 16) (bρ 16) (39553366530621 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_541 :
    Uρ (39553366530621 / 64000000000000 : ℝ) ≤
      (-(1591814203017836894719 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_541_1 U_541_2 U_541_3 U_541_4 U_541_5 U_541_6 U_541_7 U_541_8 U_541_9 U_541_10
    U_541_11 U_541_12 U_541_13 U_541_14 U_541_15 U_541_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_542_1 :
    Uω (aρ 1) (bρ 1) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(195988585830199645053 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24505755033152193 / 40000000000000000 : ℝ) ≤
      (-(195988585830199645053 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24505755033152193 / 40000000000000000 : ℚ))
        (r' := (24505755033152193 / 20000000000000000 : ℚ))
        (U := (-(195988585830199645053 / 400000000000000000000 : ℚ)))
        (U' := (81270286289800354947 / 400000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (6126412369730159 / 10000000000000000 : ℚ))
      (q := (24505755033152193 / 40000000000000000 : ℚ))
      (U := (-(195988585830199645053 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_2 :
    Uω (aρ 2) (bρ 2) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(617353647344841031591 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24410089135065761 / 40000000000000000 : ℝ) ≤
      (-(617353647344841031591 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24410089135065761 / 40000000000000000 : ℚ))
        (r' := (24410089135065761 / 20000000000000000 : ℚ))
        (U := (-(617353647344841031591 / 1250000000000000000000 : ℚ)))
        (U' := (249080328030158968409 / 1250000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (6102348433196943 / 10000000000000000 : ℚ))
      (q := (24410089135065761 / 40000000000000000 : ℚ))
      (U := (-(617353647344841031591 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_3 :
    Uω (aρ 3) (bρ 3) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(5017520647110118038431 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24218756359586867 / 40000000000000000 : ℝ) ≤
      (-(5017520647110118038431 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24218756359586867 / 40000000000000000 : ℚ))
        (r' := (24218756359586867 / 20000000000000000 : ℚ))
        (U := (-(5017520647110118038431 / 10000000000000000000000 : ℚ)))
        (U' := (1913951155889881961569 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (756759768975937 / 1250000000000000 : ℚ))
      (q := (24218756359586867 / 40000000000000000 : ℚ))
      (U := (-(5017520647110118038431 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_4 :
    Uω (aρ 4) (bρ 4) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(514959964612481159213 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23900980644384603 / 40000000000000000 : ℝ) ≤
      (-(514959964612481159213 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23900980644384603 / 40000000000000000 : ℚ))
        (r' := (23900980644384603 / 20000000000000000 : ℚ))
        (U := (-(514959964612481159213 / 1000000000000000000000 : ℚ)))
        (U' := (178187215687518840787 / 1000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (1493371118817841 / 2500000000000000 : ℚ))
      (q := (23900980644384603 / 40000000000000000 : ℚ))
      (U := (-(514959964612481159213 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_5 :
    Uω (aρ 5) (bρ 5) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(1070828463037465693711 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23417069502119359 / 40000000000000000 : ℝ) ≤
      (-(1070828463037465693711 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23417069502119359 / 40000000000000000 : ℚ))
        (r' := (23417069502119359 / 20000000000000000 : ℚ))
        (U := (-(1070828463037465693711 / 2000000000000000000000 : ℚ)))
        (U' := (315465897562534306289 / 2000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (2924859411736871 / 5000000000000000 : ℚ))
      (q := (23417069502119359 / 40000000000000000 : ℚ))
      (U := (-(1070828463037465693711 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_6 :
    Uω (aρ 6) (bρ 6) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(565497600102780771467 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22723096035816431 / 40000000000000000 : ℝ) ≤
      (-(565497600102780771467 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (22723096035816431 / 40000000000000000 : ℚ))
        (r' := (22723096035816431 / 20000000000000000 : ℚ))
        (U := (-(565497600102780771467 / 1000000000000000000000 : ℚ)))
        (U' := (127649580197219228533 / 1000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (2834986232731139 / 5000000000000000 : ℚ))
      (q := (22723096035816431 / 40000000000000000 : ℚ))
      (U := (-(565497600102780771467 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_7 :
    Uω (aρ 7) (bρ 7) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(6080536067205933051063 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21776378932357017 / 40000000000000000 : ℝ) ≤
      (-(6080536067205933051063 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21776378932357017 / 40000000000000000 : ℚ))
        (r' := (21776378932357017 / 20000000000000000 : ℚ))
        (U := (-(6080536067205933051063 / 10000000000000000000000 : ℚ)))
        (U' := (850935735794066948937 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (5420275294492571 / 10000000000000000 : ℚ))
      (q := (21776378932357017 / 40000000000000000 : ℚ))
      (U := (-(6080536067205933051063 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_8 :
    Uω (aρ 8) (bρ 8) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(6664558934562687843943 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20541013795148927 / 40000000000000000 : ℝ) ≤
      (-(6664558934562687843943 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20541013795148927 / 40000000000000000 : ℚ))
        (r' := (20541013795148927 / 20000000000000000 : ℚ))
        (U := (-(6664558934562687843943 / 10000000000000000000000 : ℚ)))
        (U' := (266912868437312156057 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (2543067188614263 / 5000000000000000 : ℚ))
      (q := (20541013795148927 / 40000000000000000 : ℚ))
      (U := (-(6664558934562687843943 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_9 :
    Uω (aρ 9) (bρ 9) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(1862139644687844223167 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18992109353432327 / 40000000000000000 : ℝ) ≤
      (-(1862139644687844223167 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18992109353432327 / 40000000000000000 : ℚ))
        (r' := (18992109353432327 / 10000000000000000 : ℚ))
        (U := (-(1862139644687844223167 / 2500000000000000000000 : ℚ)))
        (U' := (1603596256812155776833 / 2500000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (2326323892365113 / 5000000000000000 : ℚ))
      (q := (18992109353432327 / 40000000000000000 : ℚ))
      (U := (-(1862139644687844223167 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_10 :
    Uω (aρ 10) (bρ 10) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(8488608183216975225863 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17116084497070053 / 40000000000000000 : ℝ) ≤
      (-(8488608183216975225863 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17116084497070053 / 40000000000000000 : ℚ))
        (r' := (17116084497070053 / 10000000000000000 : ℚ))
        (U := (-(8488608183216975225863 / 10000000000000000000000 : ℚ)))
        (U' := (5374335422783024774137 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (4103194390044089 / 10000000000000000 : ℚ))
      (q := (17116084497070053 / 40000000000000000 : ℚ))
      (U := (-(8488608183216975225863 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_11 :
    Uω (aρ 11) (bρ 11) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(4937397276860661833359 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14900577911737607 / 40000000000000000 : ℝ) ≤
      (-(4937397276860661833359 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (14900577911737607 / 40000000000000000 : ℚ))
        (r' := (14900577911737607 / 10000000000000000 : ℚ))
        (U := (-(4937397276860661833359 / 5000000000000000000000 : ℚ)))
        (U' := (1994074526139338166641 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (1706958861791433 / 5000000000000000 : ℚ))
      (q := (14900577911737607 / 40000000000000000 : ℚ))
      (U := (-(4937397276860661833359 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_12 :
    Uω (aρ 12) (bρ 12) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(2950548377821138222619 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12288453755806303 / 40000000000000000 : ℝ) ≤
      (-(2950548377821138222619 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12288453755806303 / 40000000000000000 : ℚ))
        (r' := (12288453755806303 / 10000000000000000 : ℚ))
        (U := (-(2950548377821138222619 / 2500000000000000000000 : ℚ)))
        (U' := (515187523678861777381 / 2500000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (1265777871151107 / 5000000000000000 : ℚ))
      (q := (12288453755806303 / 40000000000000000 : ℚ))
      (U := (-(2950548377821138222619 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_13 :
    Uω (aρ 13) (bρ 13) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(15088764605498135512977 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8846332733846867 / 40000000000000000 : ℝ) ≤
      (-(15088764605498135512977 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8846332733846867 / 40000000000000000 : ℚ))
        (r' := (8846332733846867 / 5000000000000000 : ℚ))
        (U := (-(15088764605498135512977 / 10000000000000000000000 : ℚ)))
        (U' := (5705650803501864487023 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (19811079567779 / 32000000000000 : ℚ))
      (s := (151234621614687 / 1250000000000000 : ℚ))
      (q := (8846332733846867 / 40000000000000000 : ℚ))
      (U := (-(15088764605498135512977 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_542_14 :
    Uω (aρ 14) (bρ 14) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_542_15 :
    Uω (aρ 15) (bρ 15) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_542_16 :
    Uω (aρ 16) (bρ 16) (19811079567779 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_542 :
    Uρ (19811079567779 / 32000000000000 : ℝ) ≤
      (-(7935174218185580261567 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_542_1 U_542_2 U_542_3 U_542_4 U_542_5 U_542_6 U_542_7 U_542_8 U_542_9 U_542_10
    U_542_11 U_542_12 U_542_13 U_542_14 U_542_15 U_542_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_543_1 :
    Uω (aρ 1) (bρ 1) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(195287397249608713577 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1963900047688743 / 3200000000000000 : ℝ) ≤
      (-(195287397249608713577 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1963900047688743 / 3200000000000000 : ℚ))
        (r' := (1963900047688743 / 1600000000000000 : ℚ))
        (U := (-(195287397249608713577 / 400000000000000000000 : ℚ)))
        (U' := (81971474870391286423 / 400000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (61371613066873 / 100000000000000 : ℚ))
      (q := (1963900047688743 / 3200000000000000 : ℚ))
      (U := (-(195287397249608713577 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_2 :
    Uω (aρ 2) (bρ 2) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(492123039929203977663 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48906171471796523 / 80000000000000000 : ℝ) ≤
      (-(492123039929203977663 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48906171471796523 / 80000000000000000 : ℚ))
        (r' := (48906171471796523 / 40000000000000000 : ℚ))
        (U := (-(492123039929203977663 / 1000000000000000000000 : ℚ)))
        (U' := (201024140370796022337 / 1000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (6113097889091787 / 10000000000000000 : ℚ))
      (q := (48906171471796523 / 80000000000000000 : ℚ))
      (U := (-(492123039929203977663 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_3 :
    Uω (aρ 3) (bρ 3) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(4999781675993666482479 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48523512137590243 / 80000000000000000 : ℝ) ≤
      (-(4999781675993666482479 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48523512137590243 / 80000000000000000 : ℚ))
        (r' := (48523512137590243 / 40000000000000000 : ℚ))
        (U := (-(4999781675993666482479 / 10000000000000000000000 : ℚ)))
        (U' := (1931690127006333517521 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (6064829161890217 / 10000000000000000 : ℚ))
      (q := (48523512137590243 / 80000000000000000 : ℚ))
      (U := (-(4999781675993666482479 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_4 :
    Uω (aρ 4) (bρ 4) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(2565810781913314626317 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47887977345194867 / 80000000000000000 : ℝ) ≤
      (-(2565810781913314626317 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47887977345194867 / 80000000000000000 : ℚ))
        (r' := (47887977345194867 / 40000000000000000 : ℚ))
        (U := (-(2565810781913314626317 / 5000000000000000000000 : ℚ)))
        (U' := (899925119586685373683 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (5984239644856373 / 10000000000000000 : ℚ))
      (q := (47887977345194867 / 80000000000000000 : ℚ))
      (U := (-(2565810781913314626317 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_5 :
    Uω (aρ 5) (bρ 5) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(5335784226300181600677 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46920196501307823 / 80000000000000000 : ℝ) ≤
      (-(5335784226300181600677 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46920196501307823 / 80000000000000000 : ℚ))
        (r' := (46920196501307823 / 40000000000000000 : ℚ))
        (U := (-(5335784226300181600677 / 10000000000000000000000 : ℚ)))
        (U' := (1595687576699818399323 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (1465121088304903 / 2500000000000000 : ℚ))
      (q := (46920196501307823 / 80000000000000000 : ℚ))
      (U := (-(5335784226300181600677 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_6 :
    Uω (aρ 6) (bρ 6) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(2818018263035098048087 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9106469266673947 / 16000000000000000 : ℝ) ≤
      (-(2818018263035098048087 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9106469266673947 / 16000000000000000 : ℚ))
        (r' := (9106469266673947 / 8000000000000000 : ℚ))
        (U := (-(2818018263035098048087 / 5000000000000000000000 : ℚ)))
        (U' := (647717638464901951913 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (568076218637509 / 1000000000000000 : ℚ))
      (q := (9106469266673947 / 16000000000000000 : ℚ))
      (U := (-(2818018263035098048087 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_7 :
    Uω (aρ 7) (bρ 7) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(1515181266806033804241 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43639125756708131 / 80000000000000000 : ℝ) ≤
      (-(1515181266806033804241 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43639125756708131 / 80000000000000000 : ℚ))
        (r' := (43639125756708131 / 40000000000000000 : ℚ))
        (U := (-(1515181266806033804241 / 2500000000000000000000 : ℚ)))
        (U' := (217686683943966195759 / 2500000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (5431118422969689 / 10000000000000000 : ℚ))
      (q := (43639125756708131 / 80000000000000000 : ℚ))
      (U := (-(1515181266806033804241 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_8 :
    Uω (aρ 8) (bρ 8) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(830431005173728875531 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41168847029427407 / 80000000000000000 : ℝ) ≤
      (-(830431005173728875531 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41168847029427407 / 80000000000000000 : ℚ))
        (r' := (41168847029427407 / 40000000000000000 : ℚ))
        (U := (-(830431005173728875531 / 1250000000000000000000 : ℚ)))
        (U' := (36002970201271124469 / 1250000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (1274272598122377 / 2500000000000000 : ℚ))
      (q := (41168847029427407 / 80000000000000000 : ℚ))
      (U := (-(830431005173728875531 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_9 :
    Uω (aρ 9) (bρ 9) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(3712741836837896895691 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (38071968132515891 / 80000000000000000 : ℝ) ≤
      (-(3712741836837896895691 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (38071968132515891 / 80000000000000000 : ℚ))
        (r' := (38071968132515891 / 20000000000000000 : ℚ))
        (U := (-(3712741836837896895691 / 5000000000000000000000 : ℚ)))
        (U' := (3218729966162103104309 / 5000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (4663836296621629 / 10000000000000000 : ℚ))
      (q := (38071968132515891 / 80000000000000000 : ℚ))
      (U := (-(3712741836837896895691 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_10 :
    Uω (aρ 10) (bρ 10) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(2115612269099813192683 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6864366903608263 / 16000000000000000 : ℝ) ≤
      (-(2115612269099813192683 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6864366903608263 / 16000000000000000 : ℚ))
        (r' := (6864366903608263 / 4000000000000000 : ℚ))
        (U := (-(2115612269099813192683 / 2500000000000000000000 : ℚ)))
        (U' := (1350123632400186807317 / 2500000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (822972385299597 / 2000000000000000 : ℚ))
      (q := (6864366903608263 / 16000000000000000 : ℚ))
      (U := (-(2115612269099813192683 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_11 :
    Uω (aρ 11) (bρ 11) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(4921683813520243516333 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5978991803496607 / 16000000000000000 : ℝ) ≤
      (-(4921683813520243516333 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5978991803496607 / 16000000000000000 : ℚ))
        (r' := (5978991803496607 / 4000000000000000 : ℚ))
        (U := (-(4921683813520243516333 / 5000000000000000000000 : ℚ)))
        (U' := (2009787989479756483667 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (685323935512683 / 2000000000000000 : ℚ))
      (q := (5978991803496607 / 16000000000000000 : ℚ))
      (U := (-(4921683813520243516333 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_12 :
    Uω (aρ 12) (bρ 12) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(11759862056280220014139 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24681165651309479 / 80000000000000000 : ℝ) ≤
      (-(11759862056280220014139 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24681165651309479 / 80000000000000000 : ℚ))
        (r' := (24681165651309479 / 20000000000000000 : ℚ))
        (U := (-(11759862056280220014139 / 10000000000000000000000 : ℚ)))
        (U' := (2103081549719779985861 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (1273435716352513 / 5000000000000000 : ℚ))
      (q := (24681165651309479 / 80000000000000000 : ℚ))
      (U := (-(11759862056280220014139 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_13 :
    Uω (aρ 13) (bρ 13) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(7500473685979014998829 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17848721780004003 / 80000000000000000 : ℝ) ≤
      (-(7500473685979014998829 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17848721780004003 / 80000000000000000 : ℚ))
        (r' := (17848721780004003 / 10000000000000000 : ℚ))
        (U := (-(7500473685979014998829 / 5000000000000000000000 : ℚ)))
        (U' := (2896734018520985001171 / 5000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (7938190348099 / 12800000000000 : ℚ))
      (s := (1238142206473657 / 10000000000000000 : ℚ))
      (q := (17848721780004003 / 80000000000000000 : ℚ))
      (U := (-(7500473685979014998829 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_543_14 :
    Uω (aρ 14) (bρ 14) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_543_15 :
    Uω (aρ 15) (bρ 15) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_543_16 :
    Uω (aρ 16) (bρ 16) (7938190348099 / 12800000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_543 :
    Uρ (7938190348099 / 12800000000000 : ℝ) ≤
      (-(494466032119251637601 / 625000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_543_1 U_543_2 U_543_3 U_543_4 U_543_5 U_543_6 U_543_7 U_543_8 U_543_9 U_543_10
    U_543_11 U_543_12 U_543_13 U_543_14 U_543_15 U_543_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
