/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U24) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_292_1 :
    Uω (aρ 1) (bρ 1) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(3464788411850854761307 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2500947669219157 / 10000000000000000 : ℝ) ≤
      (-(3464788411850854761307 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2500947669219157 / 10000000000000000 : ℚ))
        (r' := (2500947669219157 / 2500000000000000 : ℚ))
        (U := (-(3464788411850854761307 / 2500000000000000000000 : ℚ)))
        (U' := (947489649145238693 / 2500000000000000000000 : ℚ))
        2 2 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2052407623963 / 8000000000000 : ℚ))
      (s := (625220756642391 / 2500000000000000 : ℚ))
      (q := (2500947669219157 / 10000000000000000 : ℚ))
      (U := (-(3464788411850854761307 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_292_2 :
    Uω (aρ 2) (bρ 2) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(3489029123349057418429 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2476814956106143 / 10000000000000000 : ℝ) ≤
      (-(3489029123349057418429 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2476814956106143 / 10000000000000000 : ℚ))
        (r' := (2476814956106143 / 1250000000000000 : ℚ))
        (U := (-(3489029123349057418429 / 2500000000000000000000 : ℚ)))
        (U' := (1709574728900942581571 / 2500000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2052407623963 / 8000000000000 : ℚ))
      (s := (77387081651673 / 312500000000000 : ℚ))
      (q := (2476814956106143 / 10000000000000000 : ℚ))
      (U := (-(3489029123349057418429 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_292_3 :
    Uω (aρ 3) (bρ 3) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(14153838244717469109831 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (303540487944847 / 1250000000000000 : ℝ) ≤
      (-(14153838244717469109831 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (303540487944847 / 1250000000000000 : ℚ))
        (r' := (303540487944847 / 156250000000000 : ℚ))
        (U := (-(14153838244717469109831 / 10000000000000000000000 : ℚ)))
        (U' := (6640577164282530890169 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2052407623963 / 8000000000000 : ℚ))
      (s := (1213400307054401 / 5000000000000000 : ℚ))
      (q := (303540487944847 / 1250000000000000 : ℚ))
      (U := (-(14153838244717469109831 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_292_4 :
    Uω (aρ 4) (bρ 4) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(3623542733545598920361 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (938828241337921 / 4000000000000000 : ℝ) ≤
      (-(3623542733545598920361 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (938828241337921 / 4000000000000000 : ℚ))
        (r' := (938828241337921 / 500000000000000 : ℚ))
        (U := (-(3623542733545598920361 / 2500000000000000000000 : ℚ)))
        (U' := (1575061118704401079639 / 2500000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2052407623963 / 8000000000000 : ℚ))
      (s := (468517638949171 / 2000000000000000 : ℚ))
      (q := (938828241337921 / 4000000000000000 : ℚ))
      (U := (-(3623542733545598920361 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_292_5 :
    Uω (aρ 5) (bρ 5) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(3761145976967960412099 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (138835983024799 / 625000000000000 : ℝ) ≤
      (-(3761145976967960412099 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (138835983024799 / 625000000000000 : ℚ))
        (r' := (138835983024799 / 78125000000000 : ℚ))
        (U := (-(3761145976967960412099 / 2500000000000000000000 : ℚ)))
        (U' := (1437457875282039587901 / 2500000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2052407623963 / 8000000000000 : ℚ))
      (s := (1104694182092409 / 5000000000000000 : ℚ))
      (q := (138835983024799 / 625000000000000 : ℚ))
      (U := (-(3761145976967960412099 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_292_6 :
    Uω (aρ 6) (bρ 6) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(1989507064440686596057 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2035984408317511 / 10000000000000000 : ℝ) ≤
      (-(1989507064440686596057 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2035984408317511 / 10000000000000000 : ℚ))
        (r' := (2035984408317511 / 1250000000000000 : ℚ))
        (U := (-(1989507064440686596057 / 1250000000000000000000 : ℚ)))
        (U' := (609794861684313403943 / 1250000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (2052407623963 / 8000000000000 : ℚ))
      (s := (31341345299473 / 156250000000000 : ℚ))
      (q := (2035984408317511 / 10000000000000000 : ℚ))
      (U := (-(1989507064440686596057 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_292_7 :
    Uω (aρ 7) (bρ 7) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(8660390319253113093879 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3538327680625391 / 20000000000000000 : ℝ) ≤
      (-(8660390319253113093879 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3538327680625391 / 20000000000000000 : ℚ))
        (r' := (3538327680625391 / 2500000000000000 : ℚ))
        (U := (-(8660390319253113093879 / 5000000000000000000000 : ℚ)))
        (U' := (1736817385246886906121 / 5000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (2052407623963 / 8000000000000 : ℚ))
      (s := (1695866343916641 / 10000000000000000 : ℚ))
      (q := (3538327680625391 / 20000000000000000 : ℚ))
      (U := (-(8660390319253113093879 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_292_8 :
    Uω (aρ 8) (bρ 8) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(3967468627530778132021 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2751092096951029 / 20000000000000000 : ℝ) ≤
      (-(3967468627530778132021 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2751092096951029 / 20000000000000000 : ℚ))
        (r' := (2751092096951029 / 2500000000000000 : ℚ))
        (U := (-(3967468627530778132021 / 2000000000000000000000 : ℚ)))
        (U' := (191414454269221867979 / 2000000000000000000000 : ℚ))
        3 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (2052407623963 / 8000000000000 : ℚ))
      (s := (1192172411582279 / 10000000000000000 : ℚ))
      (q := (2751092096951029 / 20000000000000000 : ℚ))
      (U := (-(3967468627530778132021 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_292_9 :
    Uω (aρ 9) (bρ 9) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_292_10 :
    Uω (aρ 10) (bρ 10) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_292_11 :
    Uω (aρ 11) (bρ 11) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_292_12 :
    Uω (aρ 12) (bρ 12) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_292_13 :
    Uω (aρ 13) (bρ 13) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_292_14 :
    Uω (aρ 14) (bρ 14) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_292_15 :
    Uω (aρ 15) (bρ 15) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_292_16 :
    Uω (aρ 16) (bρ 16) (2052407623963 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_292 :
    Uρ (2052407623963 / 8000000000000 : ℝ) ≤
      (-(17740742306804529030479 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_292_1 U_292_2 U_292_3 U_292_4 U_292_5 U_292_6 U_292_7 U_292_8 U_292_9 U_292_10
    U_292_11 U_292_12 U_292_13 U_292_14 U_292_15 U_292_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_293_1 :
    Uω (aρ 1) (bρ 1) (41730554821 / 160000000000 : ℝ) ≤
      (-(13690051247136983319469 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1271799449755011 / 5000000000000000 : ℝ) ≤
      (-(13690051247136983319469 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1271799449755011 / 5000000000000000 : ℚ))
        (r' := (1271799449755011 / 1250000000000000 : ℚ))
        (U := (-(13690051247136983319469 / 10000000000000000000000 : ℚ)))
        (U' := (172892358863016680531 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (41730554821 / 160000000000 : ℚ))
      (s := (79485479399767 / 312500000000000 : ℚ))
      (q := (1271799449755011 / 5000000000000000 : ℚ))
      (U := (-(13690051247136983319469 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_293_2 :
    Uω (aρ 2) (bρ 2) (41730554821 / 160000000000 : ℝ) ≤
      (-(13785355958980859419847 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5038944709561171 / 20000000000000000 : ℝ) ≤
      (-(13785355958980859419847 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5038944709561171 / 20000000000000000 : ℚ))
        (r' := (5038944709561171 / 5000000000000000 : ℚ))
        (U := (-(13785355958980859419847 / 10000000000000000000000 : ℚ)))
        (U' := (77587647019140580153 / 10000000000000000000000 : ℚ))
        2 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (41730554821 / 160000000000 : ℚ))
      (s := (2519051263843671 / 10000000000000000 : ℚ))
      (q := (5038944709561171 / 20000000000000000 : ℚ))
      (U := (-(13785355958980859419847 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_293_3 :
    Uω (aρ 3) (bρ 3) (41730554821 / 160000000000 : ℝ) ≤
      (-(13979620201121910036697 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4942000717062239 / 20000000000000000 : ℝ) ≤
      (-(13979620201121910036697 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4942000717062239 / 20000000000000000 : ℚ))
        (r' := (4942000717062239 / 2500000000000000 : ℚ))
        (U := (-(13979620201121910036697 / 10000000000000000000000 : ℚ)))
        (U' := (6814795207878089963303 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (41730554821 / 160000000000 : ℚ))
      (s := (2469503377694739 / 10000000000000000 : ℚ))
      (q := (4942000717062239 / 20000000000000000 : ℚ))
      (U := (-(13979620201121910036697 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_293_4 :
    Uω (aρ 4) (bρ 4) (41730554821 / 160000000000 : ℝ) ≤
      (-(2862750073378134468569 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (298725112049267 / 1250000000000000 : ℝ) ≤
      (-(2862750073378134468569 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (298725112049267 / 1250000000000000 : ℚ))
        (r' := (298725112049267 / 156250000000000 : ℚ))
        (U := (-(2862750073378134468569 / 2000000000000000000000 : ℚ)))
        (U' := (1296133008421865531431 / 2000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (41730554821 / 160000000000 : ℚ))
      (s := (596349658621443 / 2500000000000000 : ℚ))
      (q := (298725112049267 / 1250000000000000 : ℚ))
      (U := (-(2862750073378134468569 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_293_5 :
    Uω (aρ 5) (bρ 5) (41730554821 / 160000000000 : ℝ) ≤
      (-(14853402445948760473001 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4528505748238879 / 20000000000000000 : ℝ) ≤
      (-(14853402445948760473001 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4528505748238879 / 20000000000000000 : ℚ))
        (r' := (4528505748238879 / 2500000000000000 : ℚ))
        (U := (-(14853402445948760473001 / 10000000000000000000000 : ℚ)))
        (U' := (5941012963051239526999 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (41730554821 / 160000000000 : ℚ))
      (s := (2252492509271379 / 10000000000000000 : ℚ))
      (q := (4528505748238879 / 20000000000000000 : ℚ))
      (U := (-(14853402445948760473001 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_293_6 :
    Uω (aρ 6) (bρ 6) (41730554821 / 160000000000 : ℝ) ≤
      (-(15705721418374445952343 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (831704739547529 / 4000000000000000 : ℝ) ≤
      (-(15705721418374445952343 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (831704739547529 / 4000000000000000 : ℚ))
        (r' := (831704739547529 / 500000000000000 : ℚ))
        (U := (-(15705721418374445952343 / 10000000000000000000000 : ℚ)))
        (U' := (5088693990625554047657 / 10000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (41730554821 / 160000000000 : ℚ))
      (s := (409950166782029 / 2000000000000000 : ℚ))
      (q := (831704739547529 / 4000000000000000 : ℚ))
      (U := (-(15705721418374445952343 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_293_7 :
    Uω (aρ 7) (bρ 7) (41730554821 / 160000000000 : ℝ) ≤
      (-(2134081990146632886253 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3627220602139997 / 20000000000000000 : ℝ) ≤
      (-(2134081990146632886253 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3627220602139997 / 20000000000000000 : ℚ))
        (r' := (3627220602139997 / 2500000000000000 : ℚ))
        (U := (-(2134081990146632886253 / 1250000000000000000000 : ℚ)))
        (U' := (465219935978367113747 / 1250000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (41730554821 / 160000000000 : ℚ))
      (s := (1742109119072497 / 10000000000000000 : ℚ))
      (q := (3627220602139997 / 20000000000000000 : ℚ))
      (U := (-(2134081990146632886253 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_293_8 :
    Uω (aρ 8) (bρ 8) (41730554821 / 160000000000 : ℝ) ≤
      (-(19487658528202780408503 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1424497670143987 / 10000000000000000 : ℝ) ≤
      (-(19487658528202780408503 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1424497670143987 / 10000000000000000 : ℚ))
        (r' := (1424497670143987 / 1250000000000000 : ℚ))
        (U := (-(19487658528202780408503 / 10000000000000000000000 : ℚ)))
        (U' := (1306756880797219591497 / 10000000000000000000000 : ℚ))
        3 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (41730554821 / 160000000000 : ℚ))
      (s := (623712754280237 / 5000000000000000 : ℚ))
      (q := (1424497670143987 / 10000000000000000 : ℚ))
      (U := (-(19487658528202780408503 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_293_9 :
    Uω (aρ 9) (bρ 9) (41730554821 / 160000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_293_10 :
    Uω (aρ 10) (bρ 10) (41730554821 / 160000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_293_11 :
    Uω (aρ 11) (bρ 11) (41730554821 / 160000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_293_12 :
    Uω (aρ 12) (bρ 12) (41730554821 / 160000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_293_13 :
    Uω (aρ 13) (bρ 13) (41730554821 / 160000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_293_14 :
    Uω (aρ 14) (bρ 14) (41730554821 / 160000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_293_15 :
    Uω (aρ 15) (bρ 15) (41730554821 / 160000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_293_16 :
    Uω (aρ 16) (bρ 16) (41730554821 / 160000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_293 :
    Uρ (41730554821 / 160000000000 : ℝ) ≤
      (-(881709807907133594019 / 500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_293_1 U_293_2 U_293_3 U_293_4 U_293_5 U_293_6 U_293_7 U_293_8 U_293_9 U_293_10
    U_293_11 U_293_12 U_293_13 U_293_14 U_293_15 U_293_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_294_1 :
    Uω (aρ 1) (bρ 1) (269345996903 / 1000000000000 : ℝ) ≤
      (-(13360191075021170630243 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1051560501830063 / 4000000000000000 : ℝ) ≤
      (-(13360191075021170630243 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1051560501830063 / 4000000000000000 : ℚ))
        (r' := (1051560501830063 / 1000000000000000 : ℚ))
        (U := (-(13360191075021170630243 / 10000000000000000000000 : ℚ)))
        (U' := (502752530978829369757 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (269345996903 / 1000000000000 : ℚ))
      (s := (525767951641063 / 2000000000000000 : ℚ))
      (q := (1051560501830063 / 4000000000000000 : ℚ))
      (U := (-(13360191075021170630243 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_294_2 :
    Uω (aρ 2) (bρ 2) (269345996903 / 1000000000000 : ℝ) ≤
      (-(26904688033233695969 / 20000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2604786439411037 / 10000000000000000 : ℝ) ≤
      (-(26904688033233695969 / 20000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2604786439411037 / 10000000000000000 : ℚ))
        (r' := (2604786439411037 / 2500000000000000 : ℚ))
        (U := (-(26904688033233695969 / 20000000000000000000 : ℚ)))
        (U' := (821199178766304031 / 20000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (269345996903 / 1000000000000 : ℚ))
      (s := (1302189570193537 / 5000000000000000 : ℚ))
      (q := (2604786439411037 / 10000000000000000 : ℚ))
      (U := (-(26904688033233695969 / 20000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_294_3 :
    Uω (aρ 3) (bρ 3) (269345996903 / 1000000000000 : ℝ) ≤
      (-(3410010963726477067487 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (102254025270581 / 400000000000000 : ℝ) ≤
      (-(3410010963726477067487 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (102254025270581 / 400000000000000 : ℚ))
        (r' := (102254025270581 / 100000000000000 : ℚ))
        (U := (-(3410010963726477067487 / 2500000000000000000000 : ℚ)))
        (U' := (55724937773522932513 / 2500000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (269345996903 / 1000000000000 : ℚ))
      (s := (51098072628881 / 200000000000000 : ℚ))
      (q := (102254025270581 / 400000000000000 : ℚ))
      (U := (-(3410010963726477067487 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_294_4 :
    Uω (aρ 4) (bρ 4) (269345996903 / 1000000000000 : ℝ) ≤
      (-(13962424118052550522617 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4950506333616661 / 20000000000000000 : ℝ) ≤
      (-(13962424118052550522617 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4950506333616661 / 20000000000000000 : ℚ))
        (r' := (4950506333616661 / 2500000000000000 : ℚ))
        (U := (-(13962424118052550522617 / 10000000000000000000000 : ℚ)))
        (U' := (6831991290947449477383 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (269345996903 / 1000000000000 : ℚ))
      (s := (2471002882596661 / 10000000000000000 : ℚ))
      (q := (4950506333616661 / 20000000000000000 : ℚ))
      (U := (-(13962424118052550522617 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_294_5 :
    Uω (aρ 5) (bρ 5) (269345996903 / 1000000000000 : ℝ) ≤
      (-(14481773407649457578313 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36718471793851 / 156250000000000 : ℝ) ≤
      (-(14481773407649457578313 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (36718471793851 / 156250000000000 : ℚ))
        (r' := (36718471793851 / 19531250000000 : ℚ))
        (U := (-(14481773407649457578313 / 10000000000000000000000 : ℚ)))
        (U' := (6312642001350542421687 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (269345996903 / 1000000000000 : ℚ))
      (s := (292331357240991 / 1250000000000000 : ℚ))
      (q := (36718471793851 / 156250000000000 : ℚ))
      (U := (-(14481773407649457578313 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_294_6 :
    Uω (aρ 6) (bρ 6) (269345996903 / 1000000000000 : ℝ) ≤
      (-(1529822745192444888481 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2165740525370507 / 10000000000000000 : ℝ) ≤
      (-(1529822745192444888481 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2165740525370507 / 10000000000000000 : ℚ))
        (r' := (2165740525370507 / 1250000000000000 : ℚ))
        (U := (-(1529822745192444888481 / 1000000000000000000000 : ℚ)))
        (U' := (549618795707555111519 / 1000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (269345996903 / 1000000000000 : ℚ))
      (s := (1068703947098007 / 5000000000000000 : ℚ))
      (q := (2165740525370507 / 10000000000000000 : ℚ))
      (U := (-(1529822745192444888481 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_294_7 :
    Uω (aρ 7) (bρ 7) (269345996903 / 1000000000000 : ℝ) ≤
      (-(16595518643128249441507 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3804484142218451 / 20000000000000000 : ℝ) ≤
      (-(16595518643128249441507 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3804484142218451 / 20000000000000000 : ℚ))
        (r' := (3804484142218451 / 2500000000000000 : ℚ))
        (U := (-(16595518643128249441507 / 10000000000000000000000 : ℚ)))
        (U' := (4198896765871750558493 / 10000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (269345996903 / 1000000000000 : ℚ))
      (s := (1834072366433451 / 10000000000000000 : ℚ))
      (q := (3804484142218451 / 20000000000000000 : ℚ))
      (U := (-(16595518643128249441507 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_294_8 :
    Uω (aρ 8) (bρ 8) (269345996903 / 1000000000000 : ℝ) ≤
      (-(18831930265090184175181 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3042073168366019 / 20000000000000000 : ℝ) ≤
      (-(18831930265090184175181 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3042073168366019 / 20000000000000000 : ℚ))
        (r' := (3042073168366019 / 2500000000000000 : ℚ))
        (U := (-(18831930265090184175181 / 10000000000000000000000 : ℚ)))
        (U' := (1962485143909815824819 / 10000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (269345996903 / 1000000000000 : ℚ))
      (s := (1355203043921019 / 10000000000000000 : ℚ))
      (q := (3042073168366019 / 20000000000000000 : ℚ))
      (U := (-(18831930265090184175181 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_294_9 :
    Uω (aρ 9) (bρ 9) (269345996903 / 1000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_294_10 :
    Uω (aρ 10) (bρ 10) (269345996903 / 1000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_294_11 :
    Uω (aρ 11) (bρ 11) (269345996903 / 1000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_294_12 :
    Uω (aρ 12) (bρ 12) (269345996903 / 1000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_294_13 :
    Uω (aρ 13) (bρ 13) (269345996903 / 1000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_294_14 :
    Uω (aρ 14) (bρ 14) (269345996903 / 1000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_294_15 :
    Uω (aρ 15) (bρ 15) (269345996903 / 1000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_294_16 :
    Uω (aρ 16) (bρ 16) (269345996903 / 1000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_294 :
    Uρ (269345996903 / 1000000000000 : ℝ) ≤
      (-(4357409086777446195519 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_294_1 U_294_2 U_294_3 U_294_4 U_294_5 U_294_6 U_294_7 U_294_8 U_294_9 U_294_10
    U_294_11 U_294_12 U_294_13 U_294_14 U_294_15 U_294_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_295_1 :
    Uω (aρ 1) (bρ 1) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(265363977074615904323 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10612786717365443 / 40000000000000000 : ℝ) ≤
      (-(265363977074615904323 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10612786717365443 / 40000000000000000 : ℚ))
        (r' := (10612786717365443 / 10000000000000000 : ℚ))
        (U := (-(265363977074615904323 / 200000000000000000000 : ℚ)))
        (U' := (11894895045384095677 / 200000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (8696815458149 / 32000000000000 : ℚ))
      (s := (2653135746096159 / 10000000000000000 : ℚ))
      (q := (10612786717365443 / 40000000000000000 : ℚ))
      (U := (-(265363977074615904323 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_295_2 :
    Uω (aρ 2) (bρ 2) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(6679745953429830672479 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10516340261626047 / 40000000000000000 : ℝ) ≤
      (-(6679745953429830672479 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10516340261626047 / 40000000000000000 : ℚ))
        (r' := (10516340261626047 / 10000000000000000 : ℚ))
        (U := (-(6679745953429830672479 / 5000000000000000000000 : ℚ)))
        (U' := (251725849570169327521 / 5000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (8696815458149 / 32000000000000 : ℚ))
      (s := (2628681530736461 / 10000000000000000 : ℚ))
      (q := (10516340261626047 / 40000000000000000 : ℚ))
      (U := (-(6679745953429830672479 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_295_3 :
    Uω (aρ 3) (bρ 3) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(13545402519784924013857 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10322636493641941 / 40000000000000000 : ℝ) ≤
      (-(13545402519784924013857 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10322636493641941 / 40000000000000000 : ℚ))
        (r' := (10322636493641941 / 10000000000000000 : ℚ))
        (U := (-(13545402519784924013857 / 10000000000000000000000 : ℚ)))
        (U' := (317541086215075986143 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (8696815458149 / 32000000000000 : ℚ))
      (s := (322403219136801 / 1250000000000000 : ℚ))
      (q := (10322636493641941 / 40000000000000000 : ℚ))
      (U := (-(13545402519784924013857 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_295_4 :
    Uω (aρ 4) (bρ 4) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(6932293049890189446321 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9998357638502501 / 40000000000000000 : ℝ) ≤
      (-(6932293049890189446321 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9998357638502501 / 40000000000000000 : ℚ))
        (r' := (9998357638502501 / 5000000000000000 : ℚ))
        (U := (-(6932293049890189446321 / 5000000000000000000000 : ℚ)))
        (U' := (3464914654609810553679 / 5000000000000000000000 : ℚ))
        3 15 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (8696815458149 / 32000000000000 : ℚ))
      (s := (311922563323711 / 1250000000000000 : ℚ))
      (q := (9998357638502501 / 40000000000000000 : ℚ))
      (U := (-(6932293049890189446321 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_295_5 :
    Uω (aρ 5) (bρ 5) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(1437843032608491819939 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9497574219890053 / 40000000000000000 : ℝ) ≤
      (-(1437843032608491819939 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9497574219890053 / 40000000000000000 : ℚ))
        (r' := (9497574219890053 / 5000000000000000 : ℚ))
        (U := (-(1437843032608491819939 / 1000000000000000000000 : ℚ)))
        (U' := (641598508291508180061 / 1000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (8696815458149 / 32000000000000 : ℚ))
      (s := (73849334894327 / 312500000000000 : ℚ))
      (q := (9497574219890053 / 40000000000000000 : ℚ))
      (U := (-(1437843032608491819939 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_295_6 :
    Uω (aρ 6) (bρ 6) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(15185220254473415163101 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8761415055219761 / 40000000000000000 : ℝ) ≤
      (-(15185220254473415163101 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8761415055219761 / 40000000000000000 : ℚ))
        (r' := (8761415055219761 / 5000000000000000 : ℚ))
        (U := (-(15185220254473415163101 / 10000000000000000000000 : ℚ)))
        (U' := (5609195154526584836899 / 10000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (8696815458149 / 32000000000000 : ℚ))
      (s := (1081169754711659 / 5000000000000000 : ℚ))
      (q := (8761415055219761 / 40000000000000000 : ℚ))
      (U := (-(15185220254473415163101 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_295_7 :
    Uω (aρ 7) (bρ 7) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(3292797548244679441269 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7709710815941033 / 40000000000000000 : ℝ) ≤
      (-(3292797548244679441269 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7709710815941033 / 40000000000000000 : ℚ))
        (r' := (7709710815941033 / 5000000000000000 : ℚ))
        (U := (-(3292797548244679441269 / 2000000000000000000000 : ℚ)))
        (U' := (866085533555320558731 / 2000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (8696815458149 / 32000000000000 : ℚ))
      (s := (930074385271977 / 5000000000000000 : ℚ))
      (q := (7709710815941033 / 40000000000000000 : ℚ))
      (U := (-(3292797548244679441269 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_295_8 :
    Uω (aρ 8) (bρ 8) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(18654625142945181295753 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1238596676944277 / 8000000000000000 : ℝ) ≤
      (-(18654625142945181295753 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1238596676944277 / 8000000000000000 : ℚ))
        (r' := (1238596676944277 / 1000000000000000 : ℚ))
        (U := (-(18654625142945181295753 / 10000000000000000000000 : ℚ)))
        (U' := (2139790266054818704247 / 10000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (8696815458149 / 32000000000000 : ℚ))
      (s := (138532670627413 / 1000000000000000 : ℚ))
      (q := (1238596676944277 / 8000000000000000 : ℚ))
      (U := (-(18654625142945181295753 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_295_9 :
    Uω (aρ 9) (bρ 9) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(12544728152889271956379 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3254158843654867 / 40000000000000000 : ℝ) ≤
      (-(12544728152889271956379 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3254158843654867 / 40000000000000000 : ℚ))
        (r' := (3254158843654867 / 2500000000000000 : ℚ))
        (U := (-(12544728152889271956379 / 5000000000000000000000 : ℚ)))
        (U' := (1318215453110728043621 / 5000000000000000000000 : ℚ))
        4 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (8696815458149 / 32000000000000 : ℚ))
      (s := (256880064100871 / 10000000000000000 : ℚ))
      (q := (3254158843654867 / 40000000000000000 : ℚ))
      (U := (-(12544728152889271956379 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_295_10 :
    Uω (aρ 10) (bρ 10) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_295_11 :
    Uω (aρ 11) (bρ 11) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_295_12 :
    Uω (aρ 12) (bρ 12) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_295_13 :
    Uω (aρ 13) (bρ 13) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_295_14 :
    Uω (aρ 14) (bρ 14) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_295_15 :
    Uω (aρ 15) (bρ 15) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_295_16 :
    Uω (aρ 16) (bρ 16) (8696815458149 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_295 :
    Uρ (8696815458149 / 32000000000000 : ℝ) ≤
      (-(4301440739823679509847 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_295_1 U_295_2 U_295_3 U_295_4 U_295_5 U_295_6 U_295_7 U_295_8 U_295_9 U_295_10
    U_295_11 U_295_12 U_295_13 U_295_14 U_295_15 U_295_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_296_1 :
    Uω (aρ 1) (bρ 1) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(6588522609675428053601 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5354984187775611 / 20000000000000000 : ℝ) ≤
      (-(6588522609675428053601 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5354984187775611 / 20000000000000000 : ℚ))
        (r' := (5354984187775611 / 5000000000000000 : ℚ))
        (U := (-(6588522609675428053601 / 5000000000000000000000 : ℚ)))
        (U' := (342949193324571946399 / 5000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4387279507701 / 16000000000000 : ℚ))
      (s := (1338715856773743 / 5000000000000000 : ℚ))
      (q := (5354984187775611 / 20000000000000000 : ℚ))
      (U := (-(6588522609675428053601 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_296_2 :
    Uω (aρ 2) (bρ 2) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(1326749428282152019991 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1326691811223351 / 5000000000000000 : ℝ) ≤
      (-(1326749428282152019991 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1326691811223351 / 5000000000000000 : ℚ))
        (r' := (1326691811223351 / 1250000000000000 : ℚ))
        (U := (-(1326749428282152019991 / 1000000000000000000000 : ℚ)))
        (U' := (59544932317847980009 / 1000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4387279507701 / 16000000000000 : ℚ))
      (s := (2652983783175279 / 10000000000000000 : ℚ))
      (q := (1326691811223351 / 5000000000000000 : ℚ))
      (U := (-(1326749428282152019991 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_296_3 :
    Uω (aρ 3) (bρ 3) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(6725824734455487825467 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (130248368026923 / 500000000000000 : ℝ) ≤
      (-(6725824734455487825467 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (130248368026923 / 500000000000000 : ℚ))
        (r' := (130248368026923 / 125000000000000 : ℚ))
        (U := (-(6725824734455487825467 / 5000000000000000000000 : ℚ)))
        (U' := (205647068544512174533 / 5000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4387279507701 / 16000000000000 : ℚ))
      (s := (520709473141759 / 2000000000000000 : ℚ))
      (q := (130248368026923 / 500000000000000 : ℚ))
      (U := (-(6725824734455487825467 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_296_4 :
    Uω (aρ 4) (bρ 4) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(3441924802935448534447 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5047849706220241 / 20000000000000000 : ℝ) ≤
      (-(3441924802935448534447 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5047849706220241 / 20000000000000000 : ℚ))
        (r' := (5047849706220241 / 5000000000000000 : ℚ))
        (U := (-(3441924802935448534447 / 2500000000000000000000 : ℚ)))
        (U' := (23811098564551465553 / 2500000000000000000000 : ℚ))
        2 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4387279507701 / 16000000000000 : ℚ))
      (s := (629939132979279 / 2500000000000000 : ℚ))
      (q := (5047849706220241 / 20000000000000000 : ℚ))
      (U := (-(3441924802935448534447 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_296_5 :
    Uω (aρ 5) (bρ 5) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(1784519279932689038239 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4797605066056417 / 20000000000000000 : ℝ) ≤
      (-(1784519279932689038239 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4797605066056417 / 20000000000000000 : ℚ))
        (r' := (4797605066056417 / 2500000000000000 : ℚ))
        (U := (-(1784519279932689038239 / 1250000000000000000000 : ℚ)))
        (U' := (814782646192310961761 / 1250000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4387279507701 / 16000000000000 : ℚ))
      (s := (596925452772073 / 2500000000000000 : ℚ))
      (q := (4797605066056417 / 20000000000000000 : ℚ))
      (U := (-(1784519279932689038239 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_296_6 :
    Uω (aρ 6) (bρ 6) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(3768377053057300971997 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1107479918431881 / 5000000000000000 : ℝ) ≤
      (-(3768377053057300971997 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1107479918431881 / 5000000000000000 : ℚ))
        (r' := (1107479918431881 / 625000000000000 : ℚ))
        (U := (-(3768377053057300971997 / 2500000000000000000000 : ℚ)))
        (U' := (1430226799192699028003 / 2500000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (4387279507701 / 16000000000000 : ℚ))
      (s := (2187256793899399 / 10000000000000000 : ℚ))
      (q := (1107479918431881 / 5000000000000000 : ℚ))
      (U := (-(3768377053057300971997 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_296_7 :
    Uω (aρ 7) (bρ 7) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(16334286269266483063657 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (976294774346881 / 5000000000000000 : ℝ) ≤
      (-(16334286269266483063657 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (976294774346881 / 5000000000000000 : ℚ))
        (r' := (976294774346881 / 625000000000000 : ℚ))
        (U := (-(16334286269266483063657 / 10000000000000000000000 : ℚ)))
        (U' := (4460129139733516936343 / 10000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (4387279507701 / 16000000000000 : ℚ))
      (s := (1886177598319399 / 10000000000000000 : ℚ))
      (q := (976294774346881 / 5000000000000000 : ℚ))
      (U := (-(16334286269266483063657 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_296_8 :
    Uω (aρ 8) (bρ 8) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(4620280082110656607647 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (49229470375789 / 312500000000000 : ℝ) ≤
      (-(4620280082110656607647 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (49229470375789 / 312500000000000 : ℚ))
        (r' := (49229470375789 / 39062500000000 : ℚ))
        (U := (-(4620280082110656607647 / 2500000000000000000000 : ℚ)))
        (U' := (578323770139343392353 / 2500000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (4387279507701 / 16000000000000 : ℚ))
      (s := (1415226256322371 / 10000000000000000 : ℚ))
      (q := (49229470375789 / 312500000000000 : ℚ))
      (U := (-(4620280082110656607647 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_296_9 :
    Uω (aρ 9) (bρ 9) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(24307602199671372227129 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43984965283121 / 500000000000000 : ℝ) ≤
      (-(24307602199671372227129 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43984965283121 / 500000000000000 : ℚ))
        (r' := (43984965283121 / 31250000000000 : ℚ))
        (U := (-(24307602199671372227129 / 10000000000000000000000 : ℚ)))
        (U' := (3418285012328627772871 / 10000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (4387279507701 / 16000000000000 : ℚ))
      (s := (72980878391343 / 2000000000000000 : ℚ))
      (q := (43984965283121 / 500000000000000 : ℚ))
      (U := (-(24307602199671372227129 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_296_10 :
    Uω (aρ 10) (bρ 10) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_296_11 :
    Uω (aρ 11) (bρ 11) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_296_12 :
    Uω (aρ 12) (bρ 12) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_296_13 :
    Uω (aρ 13) (bρ 13) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_296_14 :
    Uω (aρ 14) (bρ 14) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_296_15 :
    Uω (aρ 15) (bρ 15) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_296_16 :
    Uω (aρ 16) (bρ 16) (4387279507701 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_296 :
    Uρ (4387279507701 / 16000000000000 : ℝ) ≤
      (-(17081173195794320474823 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_296_1 U_296_2 U_296_3 U_296_4 U_296_5 U_296_6 U_296_7 U_296_8 U_296_9 U_296_10
    U_296_11 U_296_12 U_296_13 U_296_14 U_296_15 U_296_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_297_1 :
    Uω (aρ 1) (bρ 1) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(13086715020354936082899 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2161429998792163 / 8000000000000000 : ℝ) ≤
      (-(13086715020354936082899 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2161429998792163 / 8000000000000000 : ℚ))
        (r' := (2161429998792163 / 2000000000000000 : ℚ))
        (U := (-(13086715020354936082899 / 10000000000000000000000 : ℚ)))
        (U' := (776228585645063917101 / 10000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1770460514531 / 6400000000000 : ℚ))
      (s := (8442898940971 / 31250000000000 : ℚ))
      (q := (2161429998792163 / 8000000000000000 : ℚ))
      (U := (-(13086715020354936082899 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_297_2 :
    Uω (aρ 2) (bρ 2) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(3294083889020482951309 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10710728449637483 / 40000000000000000 : ℝ) ≤
      (-(3294083889020482951309 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10710728449637483 / 40000000000000000 : ℚ))
        (r' := (10710728449637483 / 10000000000000000 : ℚ))
        (U := (-(3294083889020482951309 / 2500000000000000000000 : ℚ)))
        (U' := (171652012479517048691 / 2500000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1770460514531 / 6400000000000 : ℚ))
      (s := (1338642950729527 / 5000000000000000 : ℚ))
      (q := (10710728449637483 / 40000000000000000 : ℚ))
      (U := (-(3294083889020482951309 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_297_3 :
    Uω (aρ 3) (bρ 3) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(13358768164879755402591 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10517101400861367 / 40000000000000000 : ℝ) ≤
      (-(13358768164879755402591 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10517101400861367 / 40000000000000000 : ℚ))
        (r' := (10517101400861367 / 10000000000000000 : ℚ))
        (U := (-(13358768164879755402591 / 10000000000000000000000 : ℚ)))
        (U' := (504175441120244597409 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1770460514531 / 6400000000000 : ℚ))
      (s := (656967120855249 / 2500000000000000 : ℚ))
      (q := (10517101400861367 / 40000000000000000 : ℚ))
      (U := (-(13358768164879755402591 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_297_4 :
    Uω (aρ 4) (bρ 4) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(13671745074242828367393 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10193038080950819 / 40000000000000000 : ℝ) ≤
      (-(13671745074242828367393 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10193038080950819 / 40000000000000000 : ℚ))
        (r' := (10193038080950819 / 10000000000000000 : ℚ))
        (U := (-(13671745074242828367393 / 10000000000000000000000 : ℚ)))
        (U' := (191198531757171632607 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1770460514531 / 6400000000000 : ℚ))
      (s := (1272065502265361 / 5000000000000000 : ℚ))
      (q := (10193038080950819 / 40000000000000000 : ℚ))
      (U := (-(13671745074242828367393 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_297_5 :
    Uω (aρ 5) (bρ 5) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(14174923141875718530619 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9692836806498103 / 40000000000000000 : ℝ) ≤
      (-(14174923141875718530619 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9692836806498103 / 40000000000000000 : ℚ))
        (r' := (9692836806498103 / 5000000000000000 : ℚ))
        (U := (-(14174923141875718530619 / 10000000000000000000000 : ℚ)))
        (U' := (6619492267124281469381 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1770460514531 / 6400000000000 : ℚ))
      (s := (603055071659841 / 2500000000000000 : ℚ))
      (q := (9692836806498103 / 40000000000000000 : ℚ))
      (U := (-(14174923141875718530619 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_297_6 :
    Uω (aρ 6) (bρ 6) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(14963061266796872825393 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8958235946698503 / 40000000000000000 : ℝ) ≤
      (-(14963061266796872825393 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8958235946698503 / 40000000000000000 : ℚ))
        (r' := (8958235946698503 / 5000000000000000 : ℚ))
        (U := (-(14963061266796872825393 / 10000000000000000000000 : ℚ)))
        (U' := (5831354142203127174607 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1770460514531 / 6400000000000 : ℚ))
      (s := (553040057969891 / 2500000000000000 : ℚ))
      (q := (8958235946698503 / 40000000000000000 : ℚ))
      (U := (-(14963061266796872825393 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_297_7 :
    Uω (aρ 7) (bρ 7) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(1620636089527790470651 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7910914306669263 / 40000000000000000 : ℝ) ≤
      (-(1620636089527790470651 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7910914306669263 / 40000000000000000 : ℚ))
        (r' := (7910914306669263 / 5000000000000000 : ℚ))
        (U := (-(1620636089527790470651 / 1000000000000000000000 : ℚ)))
        (U' := (458805451372209529349 / 1000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (1770460514531 / 6400000000000 : ℚ))
      (s := (119510049539059 / 625000000000000 : ℚ))
      (q := (7910914306669263 / 40000000000000000 : ℚ))
      (U := (-(1620636089527790470651 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_297_8 :
    Uω (aρ 8) (bρ 8) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(4577807632937310211223 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6409340632257907 / 40000000000000000 : ℝ) ≤
      (-(4577807632937310211223 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6409340632257907 / 40000000000000000 : ℚ))
        (r' := (6409340632257907 / 5000000000000000 : ℚ))
        (U := (-(4577807632937310211223 / 2500000000000000000000 : ℚ)))
        (U' := (620796219312689788777 / 2500000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (1770460514531 / 6400000000000 : ℚ))
      (s := (722457803379633 / 5000000000000000 : ℚ))
      (q := (6409340632257907 / 40000000000000000 : ℚ))
      (U := (-(4577807632937310211223 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_297_9 :
    Uω (aρ 9) (bρ 9) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(23710349633563607825731 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3735361084134731 / 40000000000000000 : ℝ) ≤
      (-(23710349633563607825731 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3735361084134731 / 40000000000000000 : ℚ))
        (r' := (3735361084134731 / 2500000000000000 : ℚ))
        (U := (-(23710349633563607825731 / 10000000000000000000000 : ℚ)))
        (U' := (4015537578436392174269 / 10000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (1770460514531 / 6400000000000 : ℚ))
      (s := (224445730528839 / 5000000000000000 : ℚ))
      (q := (3735361084134731 / 40000000000000000 : ℚ))
      (U := (-(23710349633563607825731 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_297_10 :
    Uω (aρ 10) (bρ 10) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_297_11 :
    Uω (aρ 11) (bρ 11) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_297_12 :
    Uω (aρ 12) (bρ 12) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_297_13 :
    Uω (aρ 13) (bρ 13) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_297_14 :
    Uω (aρ 14) (bρ 14) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_297_15 :
    Uω (aρ 15) (bρ 15) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_297_16 :
    Uω (aρ 16) (bρ 16) (1770460514531 / 6400000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_297 :
    Uρ (1770460514531 / 6400000000000 : ℝ) ≤
      (-(16973651665081069339969 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_297_1 U_297_2 U_297_3 U_297_4 U_297_5 U_297_6 U_297_7 U_297_8 U_297_9 U_297_10
    U_297_11 U_297_12 U_297_13 U_297_14 U_297_15 U_297_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_298_1 :
    Uω (aρ 1) (bρ 1) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(6520927042978397703819 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21711481577166763 / 80000000000000000 : ℝ) ≤
      (-(6520927042978397703819 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21711481577166763 / 80000000000000000 : ℚ))
        (r' := (21711481577166763 / 20000000000000000 : ℚ))
        (U := (-(6520927042978397703819 / 5000000000000000000000 : ℚ)))
        (U' := (410544760021602296181 / 5000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (17782348702563 / 64000000000000 : ℚ))
      (s := (1356937813800611 / 5000000000000000 : ℚ))
      (q := (21711481577166763 / 80000000000000000 : ℚ))
      (U := (-(6520927042978397703819 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_298_2 :
    Uω (aρ 2) (bρ 2) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(13131066023857589108797 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21518650662438987 / 80000000000000000 : ℝ) ≤
      (-(13131066023857589108797 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21518650662438987 / 80000000000000000 : ℚ))
        (r' := (21518650662438987 / 20000000000000000 : ℚ))
        (U := (-(13131066023857589108797 / 10000000000000000000000 : ℚ)))
        (U' := (731877582142410891203 / 10000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (17782348702563 / 64000000000000 : ℚ))
      (s := (1344718455714639 / 5000000000000000 : ℚ))
      (q := (21518650662438987 / 80000000000000000 : ℚ))
      (U := (-(13131066023857589108797 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_298_3 :
    Uω (aρ 3) (bρ 3) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(13312649375703026812221 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21131434035174243 / 80000000000000000 : ℝ) ≤
      (-(13312649375703026812221 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21131434035174243 / 80000000000000000 : ℚ))
        (r' := (21131434035174243 / 20000000000000000 : ℚ))
        (U := (-(13312649375703026812221 / 10000000000000000000000 : ℚ)))
        (U' := (550294230296973187779 / 10000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (17782348702563 / 64000000000000 : ℚ))
      (s := (660007215240773 / 2500000000000000 : ℚ))
      (q := (21131434035174243 / 80000000000000000 : ℚ))
      (U := (-(13312649375703026812221 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_298_4 :
    Uω (aρ 4) (bρ 4) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(13624112191107404353649 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20483412556860871 / 80000000000000000 : ℝ) ≤
      (-(13624112191107404353649 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20483412556860871 / 80000000000000000 : ℚ))
        (r' := (20483412556860871 / 20000000000000000 : ℚ))
        (U := (-(13624112191107404353649 / 10000000000000000000000 : ℚ)))
        (U' := (238831414892595646351 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (17782348702563 / 64000000000000 : ℚ))
      (s := (2556317672449749 / 10000000000000000 : ℚ))
      (q := (20483412556860871 / 80000000000000000 : ℚ))
      (U := (-(13624112191107404353649 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_298_5 :
    Uω (aρ 5) (bρ 5) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(2824938554749409884513 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19483293534172267 / 80000000000000000 : ℝ) ≤
      (-(2824938554749409884513 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19483293534172267 / 80000000000000000 : ℚ))
        (r' := (19483293534172267 / 10000000000000000 : ℚ))
        (U := (-(2824938554749409884513 / 2000000000000000000000 : ℚ)))
        (U' := (1333944527050590115487 / 2000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (17782348702563 / 64000000000000 : ℚ))
      (s := (1212238918056299 / 5000000000000000 : ℚ))
      (q := (19483293534172267 / 80000000000000000 : ℚ))
      (U := (-(2824938554749409884513 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_298_6 :
    Uω (aρ 6) (bρ 6) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(14908303102564459612481 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18014848304206023 / 80000000000000000 : ℝ) ≤
      (-(14908303102564459612481 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18014848304206023 / 80000000000000000 : ℚ))
        (r' := (18014848304206023 / 10000000000000000 : ℚ))
        (U := (-(14908303102564459612481 / 10000000000000000000000 : ℚ)))
        (U' := (5886112306435540387519 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (17782348702563 / 64000000000000 : ℚ))
      (s := (2224606903761037 / 10000000000000000 : ℚ))
      (q := (18014848304206023 / 80000000000000000 : ℚ))
      (U := (-(14908303102564459612481 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_298_7 :
    Uω (aρ 7) (bρ 7) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(16143048243093906018401 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3184463717036787 / 16000000000000000 : ℝ) ≤
      (-(16143048243093906018401 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3184463717036787 / 16000000000000000 : ℚ))
        (r' := (3184463717036787 / 2000000000000000 : ℚ))
        (U := (-(16143048243093906018401 / 10000000000000000000000 : ℚ)))
        (U' := (4651367165906093981599 / 10000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (17782348702563 / 64000000000000 : ℚ))
      (s := (385027170953103 / 2000000000000000 : ℚ))
      (q := (3184463717036787 / 16000000000000000 : ℚ))
      (U := (-(16143048243093906018401 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_298_8 :
    Uω (aρ 8) (bρ 8) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(18227587364746944480603 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12926350436089839 / 80000000000000000 : ℝ) ≤
      (-(18227587364746944480603 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12926350436089839 / 80000000000000000 : ℚ))
        (r' := (12926350436089839 / 10000000000000000 : ℚ))
        (U := (-(18227587364746944480603 / 10000000000000000000000 : ℚ)))
        (U' := (2566828044253055519397 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (17782348702563 / 64000000000000 : ℚ))
      (s := (1459685468831991 / 10000000000000000 : ℚ))
      (q := (12926350436089839 / 80000000000000000 : ℚ))
      (U := (-(18227587364746944480603 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_298_9 :
    Uω (aρ 9) (bρ 9) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(2345044511846416428901 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7667434863188171 / 80000000000000000 : ℝ) ≤
      (-(2345044511846416428901 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7667434863188171 / 80000000000000000 : ℚ))
        (r' := (7667434863188171 / 5000000000000000 : ℚ))
        (U := (-(2345044511846416428901 / 1000000000000000000000 : ℚ)))
        (U' := (427544209353583571099 / 1000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (17782348702563 / 64000000000000 : ℚ))
      (s := (242961101983287 / 5000000000000000 : ℚ))
      (q := (7667434863188171 / 80000000000000000 : ℚ))
      (U := (-(2345044511846416428901 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_298_10 :
    Uω (aρ 10) (bρ 10) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_298_11 :
    Uω (aρ 11) (bρ 11) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_298_12 :
    Uω (aρ 12) (bρ 12) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_298_13 :
    Uω (aρ 13) (bρ 13) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_298_14 :
    Uω (aρ 14) (bρ 14) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_298_15 :
    Uω (aρ 15) (bρ 15) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_298_16 :
    Uω (aρ 16) (bρ 16) (17782348702563 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_298 :
    Uρ (17782348702563 / 64000000000000 : ℝ) ≤
      (-(16923589864234457423761 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_298_1 U_298_2 U_298_3 U_298_4 U_298_5 U_298_6 U_298_7 U_298_8 U_298_9 U_298_10
    U_298_11 U_298_12 U_298_13 U_298_14 U_298_15 U_298_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_299_1 :
    Uω (aρ 1) (bρ 1) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(6498596756097873732649 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2726082893414437 / 10000000000000000 : ℝ) ≤
      (-(6498596756097873732649 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2726082893414437 / 10000000000000000 : ℚ))
        (r' := (2726082893414437 / 2500000000000000 : ℚ))
        (U := (-(6498596756097873732649 / 5000000000000000000000 : ℚ)))
        (U' := (432875046902126267351 / 5000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2232511532477 / 8000000000000 : ℚ))
      (s := (340752948664703 / 1250000000000000 : ℚ))
      (q := (2726082893414437 / 10000000000000000 : ℚ))
      (U := (-(6498596756097873732649 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_299_2 :
    Uω (aρ 2) (bρ 2) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(327150014026541970697 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5403961074209407 / 20000000000000000 : ℝ) ≤
      (-(327150014026541970697 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5403961074209407 / 20000000000000000 : ℚ))
        (r' := (5403961074209407 / 5000000000000000 : ℚ))
        (U := (-(327150014026541970697 / 250000000000000000000 : ℚ)))
        (U' := (19423576123458029303 / 250000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2232511532477 / 8000000000000 : ℚ))
      (s := (2701587889208157 / 10000000000000000 : ℚ))
      (q := (5403961074209407 / 20000000000000000 : ℚ))
      (U := (-(327150014026541970697 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_299_3 :
    Uω (aρ 3) (bρ 3) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(1658342816041916903219 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5307166198497323 / 20000000000000000 : ℝ) ≤
      (-(1658342816041916903219 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5307166198497323 / 20000000000000000 : ℚ))
        (r' := (5307166198497323 / 5000000000000000 : ℚ))
        (U := (-(1658342816041916903219 / 1250000000000000000000 : ℚ)))
        (U' := (74525134708083096781 / 1250000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2232511532477 / 8000000000000 : ℚ))
      (s := (2652189119846073 / 10000000000000000 : ℚ))
      (q := (5307166198497323 / 20000000000000000 : ℚ))
      (U := (-(1658342816041916903219 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_299_4 :
    Uω (aρ 4) (bρ 4) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(2715341168884718786139 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (80393544784709 / 312500000000000 : ℝ) ≤
      (-(2715341168884718786139 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (80393544784709 / 312500000000000 : ℚ))
        (r' := (80393544784709 / 78125000000000 : ℚ))
        (U := (-(2715341168884718786139 / 2000000000000000000000 : ℚ)))
        (U' := (57247552315281213861 / 2000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2232511532477 / 8000000000000 : ℚ))
      (s := (1284251984317563 / 5000000000000000 : ℚ))
      (q := (80393544784709 / 312500000000000 : ℚ))
      (U := (-(2715341168884718786139 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_299_5 :
    Uω (aρ 5) (bρ 5) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(14074715707090353918203 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4895227260949929 / 20000000000000000 : ℝ) ≤
      (-(14074715707090353918203 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4895227260949929 / 20000000000000000 : ℚ))
        (r' := (4895227260949929 / 2500000000000000 : ℚ))
        (U := (-(14074715707090353918203 / 10000000000000000000000 : ℚ)))
        (U' := (6719699701909646081797 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2232511532477 / 8000000000000 : ℚ))
      (s := (2436734282698679 / 10000000000000000 : ℚ))
      (q := (4895227260949929 / 20000000000000000 : ℚ))
      (U := (-(14074715707090353918203 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_299_6 :
    Uω (aρ 6) (bρ 6) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(7426925208423690697017 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2264151444451861 / 10000000000000000 : ℝ) ≤
      (-(7426925208423690697017 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2264151444451861 / 10000000000000000 : ℚ))
        (r' := (2264151444451861 / 1250000000000000 : ℚ))
        (U := (-(7426925208423690697017 / 5000000000000000000000 : ℚ)))
        (U' := (2970282496076309302983 / 5000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (2232511532477 / 8000000000000 : ℚ))
      (s := (279631285724059 / 1250000000000000 : ℚ))
      (q := (2264151444451861 / 10000000000000000 : ℚ))
      (U := (-(7426925208423690697017 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_299_7 :
    Uω (aρ 7) (bρ 7) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(3216032140314322800777 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2002845705585937 / 10000000000000000 : ℝ) ≤
      (-(3216032140314322800777 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2002845705585937 / 10000000000000000 : ℚ))
        (r' := (2002845705585937 / 1250000000000000 : ℚ))
        (U := (-(3216032140314322800777 / 2000000000000000000000 : ℚ)))
        (U' := (942850941485677199223 / 2000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (2232511532477 / 8000000000000 : ℚ))
      (s := (121131261801289 / 625000000000000 : ℚ))
      (q := (2002845705585937 / 10000000000000000 : ℚ))
      (U := (-(3216032140314322800777 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_299_8 :
    Uω (aρ 8) (bρ 8) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(18144784941387903088781 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (81461425667013 / 500000000000000 : ℝ) ≤
      (-(18144784941387903088781 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (81461425667013 / 500000000000000 : ℚ))
        (r' := (81461425667013 / 62500000000000 : ℚ))
        (U := (-(18144784941387903088781 / 10000000000000000000000 : ℚ)))
        (U' := (2649630467612096911219 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (2232511532477 / 8000000000000 : ℚ))
      (s := (147440745566927 / 1000000000000000 : ℚ))
      (q := (81461425667013 / 500000000000000 : ℚ))
      (U := (-(18144784941387903088781 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_299_9 :
    Uω (aρ 9) (bρ 9) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(11604530457872435747047 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (98184580963581 / 1000000000000000 : ℝ) ≤
      (-(11604530457872435747047 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (98184580963581 / 1000000000000000 : ℚ))
        (r' := (98184580963581 / 62500000000000 : ℚ))
        (U := (-(11604530457872435747047 / 5000000000000000000000 : ℚ)))
        (U' := (2258413148127564252953 / 5000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (2232511532477 / 8000000000000 : ℚ))
      (s := (52060767662037 / 1000000000000000 : ℚ))
      (q := (98184580963581 / 1000000000000000 : ℚ))
      (U := (-(11604530457872435747047 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_299_10 :
    Uω (aρ 10) (bρ 10) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_299_11 :
    Uω (aρ 11) (bρ 11) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_299_12 :
    Uω (aρ 12) (bρ 12) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_299_13 :
    Uω (aρ 13) (bρ 13) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_299_14 :
    Uω (aρ 14) (bρ 14) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_299_15 :
    Uω (aρ 15) (bρ 15) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_299_16 :
    Uω (aρ 16) (bρ 16) (2232511532477 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_299 :
    Uρ (2232511532477 / 8000000000000 : ℝ) ≤
      (-(16875345848822549837269 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_299_1 U_299_2 U_299_3 U_299_4 U_299_5 U_299_6 U_299_7 U_299_8 U_299_9 U_299_10
    U_299_11 U_299_12 U_299_13 U_299_14 U_299_15 U_299_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_300_1 :
    Uω (aρ 1) (bρ 1) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(12952731517223761911667 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21905844698621997 / 80000000000000000 : ℝ) ≤
      (-(12952731517223761911667 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21905844698621997 / 80000000000000000 : ℚ))
        (r' := (21905844698621997 / 20000000000000000 : ℚ))
        (U := (-(12952731517223761911667 / 10000000000000000000000 : ℚ)))
        (U' := (910212088776238088333 / 10000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (17937835817069 / 64000000000000 : ℚ))
      (s := (684542886580867 / 2500000000000000 : ℚ))
      (q := (21905844698621997 / 80000000000000000 : ℚ))
      (U := (-(12952731517223761911667 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_300_2 :
    Uω (aρ 2) (bρ 2) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(1630142166947326220879 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21713037804200553 / 80000000000000000 : ℝ) ≤
      (-(1630142166947326220879 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21713037804200553 / 80000000000000000 : ℚ))
        (r' := (21713037804200553 / 20000000000000000 : ℚ))
        (U := (-(1630142166947326220879 / 1250000000000000000000 : ℚ)))
        (U' := (102725783802673779121 / 1250000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (17937835817069 / 64000000000000 : ℚ))
      (s := (2713738835228107 / 10000000000000000 : ℚ))
      (q := (21713037804200553 / 80000000000000000 : ℚ))
      (U := (-(1630142166947326220879 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_300_3 :
    Uω (aρ 3) (bρ 3) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(13221045681674648191651 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21325895084666693 / 80000000000000000 : ℝ) ≤
      (-(13221045681674648191651 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21325895084666693 / 80000000000000000 : ℚ))
        (r' := (21325895084666693 / 20000000000000000 : ℚ))
        (U := (-(13221045681674648191651 / 10000000000000000000000 : ℚ)))
        (U' := (641897924325351808349 / 10000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (17937835817069 / 64000000000000 : ℚ))
      (s := (1332174630847321 / 5000000000000000 : ℚ))
      (q := (21325895084666693 / 80000000000000000 : ℚ))
      (U := (-(13221045681674648191651 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_300_4 :
    Uω (aρ 4) (bρ 4) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(3382380970715133003067 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20678080907039941 / 80000000000000000 : ℝ) ≤
      (-(3382380970715133003067 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20678080907039941 / 80000000000000000 : ℚ))
        (r' := (20678080907039941 / 20000000000000000 : ℚ))
        (U := (-(3382380970715133003067 / 2500000000000000000000 : ℚ)))
        (U' := (83354930784866996933 / 2500000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (17937835817069 / 64000000000000 : ℚ))
      (s := (1290344949176477 / 5000000000000000 : ℚ))
      (q := (20678080907039941 / 80000000000000000 : ℚ))
      (U := (-(3382380970715133003067 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_300_5 :
    Uω (aρ 5) (bρ 5) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(1753123672217734173881 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (787140808324557 / 3200000000000000 : ℝ) ≤
      (-(1753123672217734173881 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (787140808324557 / 3200000000000000 : ℚ))
        (r' := (787140808324557 / 400000000000000 : ℚ))
        (U := (-(1753123672217734173881 / 1250000000000000000000 : ℚ)))
        (U' := (846178253907265826119 / 1250000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (17937835817069 / 64000000000000 : ℚ))
      (s := (48979792859129 / 200000000000000 : ℚ))
      (q := (787140808324557 / 3200000000000000 : ℚ))
      (U := (-(1753123672217734173881 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_300_6 :
    Uω (aρ 6) (bρ 6) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(14799699741453893134069 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3642312373200597 / 16000000000000000 : ℝ) ≤
      (-(14799699741453893134069 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3642312373200597 / 16000000000000000 : ℚ))
        (r' := (3642312373200597 / 2000000000000000 : ℚ))
        (U := (-(14799699741453893134069 / 10000000000000000000000 : ℚ)))
        (U' := (5994715667546106865931 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (17937835817069 / 64000000000000 : ℚ))
      (s := (449898086513743 / 2000000000000000 : ℚ))
      (q := (3642312373200597 / 16000000000000000 : ℚ))
      (U := (-(14799699741453893134069 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_300_7 :
    Uω (aρ 7) (bρ 7) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(320353845175740239713 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3224634129455817 / 16000000000000000 : ℝ) ≤
      (-(320353845175740239713 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3224634129455817 / 16000000000000000 : ℚ))
        (r' := (3224634129455817 / 2000000000000000 : ℚ))
        (U := (-(320353845175740239713 / 200000000000000000000 : ℚ)))
        (U' := (95534463004259760287 / 200000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (17937835817069 / 64000000000000 : ℚ))
      (s := (97552700432387 / 500000000000000 : ℚ))
      (q := (3224634129455817 / 16000000000000000 : ℚ))
      (U := (-(320353845175740239713 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_300_8 :
    Uω (aρ 8) (bρ 8) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(18062803918743756208487 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13141119956302201 / 80000000000000000 : ℝ) ≤
      (-(18062803918743756208487 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13141119956302201 / 80000000000000000 : ℚ))
        (r' := (13141119956302201 / 10000000000000000 : ℚ))
        (U := (-(18062803918743756208487 / 10000000000000000000000 : ℚ)))
        (U' := (2731611490256243791513 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (17937835817069 / 64000000000000 : ℚ))
      (s := (1489082987243519 / 10000000000000000 : ℚ))
      (q := (13141119956302201 / 80000000000000000 : ℚ))
      (U := (-(18062803918743756208487 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_300_9 :
    Uω (aρ 9) (bρ 9) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(22982841438817210519433 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1606896336678253 / 16000000000000000 : ℝ) ≤
      (-(22982841438817210519433 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1606896336678253 / 16000000000000000 : ℚ))
        (r' := (1606896336678253 / 1000000000000000 : ℚ))
        (U := (-(22982841438817210519433 / 10000000000000000000000 : ℚ)))
        (U' := (4743045773182789480567 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (17937835817069 / 64000000000000 : ℚ))
      (s := (110677809475157 / 2000000000000000 : ℚ))
      (q := (1606896336678253 / 16000000000000000 : ℚ))
      (U := (-(22982841438817210519433 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_300_10 :
    Uω (aρ 10) (bρ 10) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_300_11 :
    Uω (aρ 11) (bρ 11) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_300_12 :
    Uω (aρ 12) (bρ 12) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_300_13 :
    Uω (aρ 13) (bρ 13) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_300_14 :
    Uω (aρ 14) (bρ 14) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_300_15 :
    Uω (aρ 15) (bρ 15) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_300_16 :
    Uω (aρ 16) (bρ 16) (17937835817069 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_300 :
    Uρ (17937835817069 / 64000000000000 : ℝ) ≤
      (-(8414310178676383152373 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_300_1 U_300_2 U_300_3 U_300_4 U_300_5 U_300_6 U_300_7 U_300_8 U_300_9 U_300_10
    U_300_11 U_300_12 U_300_13 U_300_14 U_300_15 U_300_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_301_1 :
    Uω (aρ 1) (bρ 1) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(12908466342858148682791 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11001513115667967 / 40000000000000000 : ℝ) ≤
      (-(12908466342858148682791 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11001513115667967 / 40000000000000000 : ℚ))
        (r' := (11001513115667967 / 10000000000000000 : ℚ))
        (U := (-(12908466342858148682791 / 10000000000000000000000 : ℚ)))
        (U' := (954477263141851317209 / 10000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (9007789687161 / 32000000000000 : ℚ))
      (s := (2750319498681171 / 10000000000000000 : ℚ))
      (q := (11001513115667967 / 40000000000000000 : ℚ))
      (U := (-(12908466342858148682791 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_301_2 :
    Uω (aρ 2) (bρ 2) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(12996474539862435628569 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10905115593113297 / 40000000000000000 : ℝ) ≤
      (-(12996474539862435628569 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10905115593113297 / 40000000000000000 : ℚ))
        (r' := (10905115593113297 / 10000000000000000 : ℚ))
        (U := (-(12996474539862435628569 / 10000000000000000000000 : ℚ)))
        (U' := (866469066137564371431 / 10000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (9007789687161 / 32000000000000 : ℚ))
      (s := (681472437478459 / 2500000000000000 : ℚ))
      (q := (10905115593113297 / 40000000000000000 : ℚ))
      (U := (-(12996474539862435628569 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_301_3 :
    Uω (aρ 3) (bρ 3) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(1646944615148955121397 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10711562456793547 / 40000000000000000 : ℝ) ≤
      (-(1646944615148955121397 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10711562456793547 / 40000000000000000 : ℚ))
        (r' := (10711562456793547 / 10000000000000000 : ℚ))
        (U := (-(1646944615148955121397 / 1250000000000000000000 : ℚ)))
        (U' := (85923335601044878603 / 1250000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (9007789687161 / 32000000000000 : ℚ))
      (s := (2676509288103961 / 10000000000000000 : ℚ))
      (q := (10711562456793547 / 40000000000000000 : ℚ))
      (U := (-(1646944615148955121397 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_301_4 :
    Uω (aρ 4) (bρ 4) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(1348256418568254684709 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (415508258079839 / 1600000000000000 : ℝ) ≤
      (-(1348256418568254684709 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (415508258079839 / 1600000000000000 : ℚ))
        (r' := (415508258079839 / 400000000000000 : ℚ))
        (U := (-(1348256418568254684709 / 1000000000000000000000 : ℚ)))
        (U' := (38037942031745315291 / 1000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (9007789687161 / 32000000000000 : ℚ))
      (s := (103715018670807 / 400000000000000 : ℚ))
      (q := (415508258079839 / 1600000000000000 : ℚ))
      (U := (-(1348256418568254684709 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_301_5 :
    Uω (aρ 5) (bρ 5) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(3493877815151177753499 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1977612709202521 / 8000000000000000 : ℝ) ≤
      (-(3493877815151177753499 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1977612709202521 / 8000000000000000 : ℚ))
        (r' := (1977612709202521 / 1000000000000000 : ℚ))
        (U := (-(3493877815151177753499 / 2500000000000000000000 : ℚ)))
        (U' := (1704726037098822246501 / 2500000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (9007789687161 / 32000000000000 : ℚ))
      (s := (246124393311349 / 1000000000000000 : ℚ))
      (q := (1977612709202521 / 8000000000000000 : ℚ))
      (U := (-(3493877815151177753499 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_301_6 :
    Uω (aρ 6) (bρ 6) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(737292383409021471139 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9154949724444683 / 40000000000000000 : ℝ) ≤
      (-(737292383409021471139 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9154949724444683 / 40000000000000000 : ℚ))
        (r' := (9154949724444683 / 5000000000000000 : ℚ))
        (U := (-(737292383409021471139 / 500000000000000000000 : ℚ)))
        (U' := (302428387040978528861 / 500000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (9007789687161 / 32000000000000 : ℚ))
      (s := (2261927397469529 / 10000000000000000 : ℚ))
      (q := (9154949724444683 / 40000000000000000 : ℚ))
      (U := (-(737292383409021471139 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_301_7 :
    Uω (aρ 7) (bρ 7) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(7977818517863032778631 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8111767212567727 / 40000000000000000 : ℝ) ≤
      (-(7977818517863032778631 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8111767212567727 / 40000000000000000 : ℚ))
        (r' := (8111767212567727 / 5000000000000000 : ℚ))
        (U := (-(7977818517863032778631 / 5000000000000000000000 : ℚ)))
        (U' := (2419389186636967221369 / 5000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (9007789687161 / 32000000000000 : ℚ))
      (s := (1963997522291051 / 10000000000000000 : ℚ))
      (q := (8111767212567727 / 40000000000000000 : ℚ))
      (U := (-(7977818517863032778631 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_301_8 :
    Uω (aρ 8) (bρ 8) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(3596325135396607525091 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6624115712704663 / 40000000000000000 : ℝ) ≤
      (-(3596325135396607525091 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6624115712704663 / 40000000000000000 : ℚ))
        (r' := (6624115712704663 / 5000000000000000 : ℚ))
        (U := (-(3596325135396607525091 / 2000000000000000000000 : ℚ)))
        (U' := (562557946403392474909 / 2000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (9007789687161 / 32000000000000 : ℚ))
      (s := (1503713423699519 / 10000000000000000 : ℚ))
      (q := (6624115712704663 / 40000000000000000 : ℚ))
      (U := (-(3596325135396607525091 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_301_9 :
    Uω (aρ 9) (bρ 9) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(2276934142411561312073 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4103931064846051 / 40000000000000000 : ℝ) ≤
      (-(2276934142411561312073 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4103931064846051 / 40000000000000000 : ℚ))
        (r' := (4103931064846051 / 2500000000000000 : ℚ))
        (U := (-(2276934142411561312073 / 1000000000000000000000 : ℚ)))
        (U' := (495654578788438687927 / 1000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (9007789687161 / 32000000000000 : ℚ))
      (s := (584586728130213 / 10000000000000000 : ℚ))
      (q := (4103931064846051 / 40000000000000000 : ℚ))
      (U := (-(2276934142411561312073 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_301_10 :
    Uω (aρ 10) (bρ 10) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_301_11 :
    Uω (aρ 11) (bρ 11) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_301_12 :
    Uω (aρ 12) (bρ 12) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_301_13 :
    Uω (aρ 13) (bρ 13) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_301_14 :
    Uω (aρ 14) (bρ 14) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_301_15 :
    Uω (aρ 15) (bρ 15) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_301_16 :
    Uω (aρ 16) (bρ 16) (9007789687161 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_301 :
    Uρ (9007789687161 / 32000000000000 : ℝ) ≤
      (-(3356638919890918301819 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_301_1 U_301_2 U_301_3 U_301_4 U_301_5 U_301_6 U_301_7 U_301_8 U_301_9 U_301_10
    U_301_11 U_301_12 U_301_13 U_301_14 U_301_15 U_301_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_302_1 :
    Uω (aρ 1) (bρ 1) (723732917263 / 2560000000000 : ℝ) ≤
      (-(6432198127082150183279 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4420041549140519 / 16000000000000000 : ℝ) ≤
      (-(6432198127082150183279 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4420041549140519 / 16000000000000000 : ℚ))
        (r' := (4420041549140519 / 4000000000000000 : ℚ))
        (U := (-(6432198127082150183279 / 5000000000000000000000 : ℚ)))
        (U' := (499273675917849816721 / 5000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (723732917263 / 2560000000000 : ℚ))
      (s := (552493489290411 / 2000000000000000 : ℚ))
      (q := (4420041549140519 / 16000000000000000 : ℚ))
      (U := (-(6432198127082150183279 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_302_2 :
    Uω (aρ 2) (bρ 2) (723732917263 / 2560000000000 : ℝ) ≤
      (-(1619001298812421734721 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21907424444584411 / 80000000000000000 : ℝ) ≤
      (-(1619001298812421734721 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21907424444584411 / 80000000000000000 : ℚ))
        (r' := (21907424444584411 / 20000000000000000 : ℚ))
        (U := (-(1619001298812421734721 / 1250000000000000000000 : ℚ)))
        (U' := (113866651937578265279 / 1250000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (723732917263 / 2560000000000 : ℚ))
      (s := (2738040633682509 / 10000000000000000 : ℚ))
      (q := (21907424444584411 / 80000000000000000 : ℚ))
      (U := (-(1619001298812421734721 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_302_3 :
    Uω (aρ 3) (bρ 3) (723732917263 / 2560000000000 : ℝ) ≤
      (-(6565137179223193084959 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21520354287015651 / 80000000000000000 : ℝ) ≤
      (-(6565137179223193084959 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21520354287015651 / 80000000000000000 : ℚ))
        (r' := (21520354287015651 / 20000000000000000 : ℚ))
        (U := (-(6565137179223193084959 / 5000000000000000000000 : ℚ)))
        (U' := (366334623776806915041 / 5000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (723732917263 / 2560000000000 : ℚ))
      (s := (2688669200640319 / 10000000000000000 : ℚ))
      (q := (21520354287015651 / 80000000000000000 : ℚ))
      (U := (-(6565137179223193084959 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_302_4 :
    Uω (aρ 4) (bρ 4) (723732917263 / 2560000000000 : ℝ) ≤
      (-(335895616554249685107 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20872743476022003 / 80000000000000000 : ℝ) ≤
      (-(335895616554249685107 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20872743476022003 / 80000000000000000 : ℚ))
        (r' := (20872743476022003 / 20000000000000000 : ℚ))
        (U := (-(335895616554249685107 / 250000000000000000000 : ℚ)))
        (U' := (10677973595750314893 / 250000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (723732917263 / 2560000000000 : ℚ))
      (s := (2605060678956907 / 10000000000000000 : ℚ))
      (q := (20872743476022003 / 80000000000000000 : ℚ))
      (U := (-(335895616554249685107 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_302_5 :
    Uω (aρ 5) (bρ 5) (723732917263 / 2560000000000 : ℝ) ≤
      (-(6963139434426427686679 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19873729759151967 / 80000000000000000 : ℝ) ≤
      (-(6963139434426427686679 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19873729759151967 / 80000000000000000 : ℚ))
        (r' := (19873729759151967 / 10000000000000000 : ℚ))
        (U := (-(6963139434426427686679 / 5000000000000000000000 : ℚ)))
        (U' := (3434068270073572313321 / 5000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (723732917263 / 2560000000000 : ℚ))
      (s := (1236748584537199 / 5000000000000000 : ℚ))
      (q := (19873729759151967 / 80000000000000000 : ℚ))
      (U := (-(6963139434426427686679 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_302_6 :
    Uω (aρ 6) (bρ 6) (723732917263 / 2560000000000 : ℝ) ≤
      (-(14692290847409693047619 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18408224513068699 / 80000000000000000 : ℝ) ≤
      (-(14692290847409693047619 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18408224513068699 / 80000000000000000 : ℚ))
        (r' := (18408224513068699 / 10000000000000000 : ℚ))
        (U := (-(14692290847409693047619 / 10000000000000000000000 : ℚ)))
        (U' := (6102124561590306952381 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (723732917263 / 2560000000000 : ℚ))
      (s := (2274361232693581 / 10000000000000000 : ℚ))
      (q := (18408224513068699 / 80000000000000000 : ℚ))
      (U := (-(14692290847409693047619 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_302_7 :
    Uω (aρ 7) (bρ 7) (723732917263 / 2560000000000 : ℝ) ≤
      (-(7946994641123173545093 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16323857787985871 / 80000000000000000 : ℝ) ≤
      (-(7946994641123173545093 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16323857787985871 / 80000000000000000 : ℚ))
        (r' := (16323857787985871 / 10000000000000000 : ℚ))
        (U := (-(7946994641123173545093 / 5000000000000000000000 : ℚ)))
        (U' := (2450213063376826454907 / 5000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (723732917263 / 2560000000000 : ℚ))
      (s := (988465466091437 / 5000000000000000 : ℚ))
      (q := (16323857787985871 / 80000000000000000 : ℚ))
      (U := (-(7946994641123173545093 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_302_8 :
    Uω (aρ 8) (bρ 8) (723732917263 / 2560000000000 : ℝ) ≤
      (-(3580246456361628938953 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13355167728518967 / 80000000000000000 : ℝ) ≤
      (-(3580246456361628938953 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13355167728518967 / 80000000000000000 : ℚ))
        (r' := (13355167728518967 / 10000000000000000 : ℚ))
        (U := (-(3580246456361628938953 / 2000000000000000000000 : ℚ)))
        (U' := (578636625438371061047 / 2000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (723732917263 / 2560000000000 : ℚ))
      (s := (379575017164037 / 2500000000000000 : ℚ))
      (q := (13355167728518967 / 80000000000000000 : ℚ))
      (U := (-(3580246456361628938953 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_302_9 :
    Uω (aρ 9) (bρ 9) (723732917263 / 2560000000000 : ℝ) ≤
      (-(11283356655203721398811 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8375872928878307 / 80000000000000000 : ℝ) ≤
      (-(11283356655203721398811 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8375872928878307 / 80000000000000000 : ℚ))
        (r' := (8375872928878307 / 5000000000000000 : ℚ))
        (U := (-(11283356655203721398811 / 5000000000000000000000 : ℚ)))
        (U' := (2579586950796278601189 / 5000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (723732917263 / 2560000000000 : ℚ))
      (s := (614441997105983 / 10000000000000000 : ℚ))
      (q := (8375872928878307 / 80000000000000000 : ℚ))
      (U := (-(11283356655203721398811 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_302_10 :
    Uω (aρ 10) (bρ 10) (723732917263 / 2560000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_302_11 :
    Uω (aρ 11) (bρ 11) (723732917263 / 2560000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_302_12 :
    Uω (aρ 12) (bρ 12) (723732917263 / 2560000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_302_13 :
    Uω (aρ 13) (bρ 13) (723732917263 / 2560000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_302_14 :
    Uω (aρ 14) (bρ 14) (723732917263 / 2560000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_302_15 :
    Uω (aρ 15) (bρ 15) (723732917263 / 2560000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_302_16 :
    Uω (aρ 16) (bρ 16) (723732917263 / 2560000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_302 :
    Uρ (723732917263 / 2560000000000 : ℝ) ≤
      (-(2092362830814368895911 / 1250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_302_1 U_302_2 U_302_3 U_302_4 U_302_5 U_302_6 U_302_7 U_302_8 U_302_9 U_302_10
    U_302_11 U_302_12 U_302_13 U_302_14 U_302_15 U_302_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_303_1 :
    Uω (aρ 1) (bρ 1) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(12820519539047609253381 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5549347310490741 / 20000000000000000 : ℝ) ≤
      (-(12820519539047609253381 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5549347310490741 / 20000000000000000 : ℚ))
        (r' := (5549347310490741 / 5000000000000000 : ℚ))
        (U := (-(12820519539047609253381 / 10000000000000000000000 : ℚ)))
        (U' := (1042424066952390746619 / 10000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4542766622207 / 16000000000000 : ℚ))
      (s := (1387307694848183 / 5000000000000000 : ℚ))
      (q := (5549347310490741 / 20000000000000000 : ℚ))
      (U := (-(12820519539047609253381 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_303_2 :
    Uω (aρ 2) (bρ 2) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(12907743127780000518383 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1100230879045659 / 4000000000000000 : ℝ) ≤
      (-(12907743127780000518383 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1100230879045659 / 4000000000000000 : ℚ))
        (r' := (1100230879045659 / 1000000000000000 : ℚ))
        (U := (-(12907743127780000518383 / 10000000000000000000000 : ℚ)))
        (U' := (955200478219999481617 / 10000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4542766622207 / 16000000000000 : ℚ))
      (s := (34377393586799 / 125000000000000 : ℚ))
      (q := (1100230879045659 / 4000000000000000 : ℚ))
      (U := (-(12907743127780000518383 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_303_3 :
    Uω (aρ 3) (bρ 3) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(6542598065307995406991 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2702197901388079 / 10000000000000000 : ℝ) ≤
      (-(6542598065307995406991 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2702197901388079 / 10000000000000000 : ℚ))
        (r' := (2702197901388079 / 2500000000000000 : ℚ))
        (U := (-(6542598065307995406991 / 5000000000000000000000 : ℚ)))
        (U' := (388873737692004593009 / 5000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4542766622207 / 16000000000000 : ℚ))
      (s := (2700829000841783 / 10000000000000000 : ℚ))
      (q := (2702197901388079 / 10000000000000000 : ℚ))
      (U := (-(6542598065307995406991 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_303_4 :
    Uω (aρ 4) (bρ 4) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(13389303251053762690677 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (655314770094759 / 2500000000000000 : ℝ) ≤
      (-(13389303251053762690677 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (655314770094759 / 2500000000000000 : ℚ))
        (r' := (655314770094759 / 625000000000000 : ℚ))
        (U := (-(13389303251053762690677 / 10000000000000000000000 : ℚ)))
        (U' := (473640354946237309323 / 10000000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4542766622207 / 16000000000000 : ℚ))
      (s := (2617245539888697 / 10000000000000000 : ℚ))
      (q := (655314770094759 / 2500000000000000 : ℚ))
      (U := (-(13389303251053762690677 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_303_5 :
    Uω (aρ 5) (bρ 5) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(13877289753155558398313 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1248208016990797 / 5000000000000000 : ℝ) ≤
      (-(13877289753155558398313 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1248208016990797 / 5000000000000000 : ℚ))
        (r' := (1248208016990797 / 625000000000000 : ℚ))
        (U := (-(13877289753155558398313 / 10000000000000000000000 : ℚ)))
        (U' := (6917125655844441601687 / 10000000000000000000000 : ℚ))
        3 15 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4542766622207 / 16000000000000 : ℚ))
      (s := (2485749366428813 / 10000000000000000 : ℚ))
      (q := (1248208016990797 / 5000000000000000 : ℚ))
      (U := (-(13877289753155558398313 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_303_6 :
    Uω (aρ 6) (bρ 6) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(7319512993375079674599 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4626634315685649 / 20000000000000000 : ℝ) ≤
      (-(7319512993375079674599 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4626634315685649 / 20000000000000000 : ℚ))
        (r' := (4626634315685649 / 2500000000000000 : ℚ))
        (U := (-(7319512993375079674599 / 5000000000000000000000 : ℚ)))
        (U' := (3077694711124920325401 / 5000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (4542766622207 / 16000000000000 : ℚ))
      (s := (1143395994645637 / 5000000000000000 : ℚ))
      (q := (4626634315685649 / 20000000000000000 : ℚ))
      (U := (-(7319512993375079674599 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_303_7 :
    Uω (aρ 7) (bρ 7) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(15832743373195214114231 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (205301769048547 / 1000000000000000 : ℝ) ≤
      (-(15832743373195214114231 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (205301769048547 / 1000000000000000 : ℚ))
        (r' := (205301769048547 / 125000000000000 : ℚ))
        (U := (-(15832743373195214114231 / 10000000000000000000000 : ℚ)))
        (U' := (4961672035804785885769 / 10000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (4542766622207 / 16000000000000 : ℚ))
      (s := (397970887067313 / 2000000000000000 : ℚ))
      (q := (205301769048547 / 1000000000000000 : ℚ))
      (U := (-(15832743373195214114231 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_303_8 :
    Uω (aρ 8) (bρ 8) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(8910803224689173136883 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3365483466576571 / 20000000000000000 : ℝ) ≤
      (-(8910803224689173136883 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3365483466576571 / 20000000000000000 : ℚ))
        (r' := (3365483466576571 / 2500000000000000 : ℚ))
        (U := (-(8910803224689173136883 / 5000000000000000000000 : ℚ)))
        (U' := (1486404479810826863117 / 5000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (4542766622207 / 16000000000000 : ℚ))
      (s := (383211043070549 / 2500000000000000 : ℚ))
      (q := (3365483466576571 / 20000000000000000 : ℚ))
      (U := (-(8910803224689173136883 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_303_9 :
    Uω (aρ 9) (bρ 9) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(11186760242463115104121 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (533703873898957 / 5000000000000000 : ℝ) ≤
      (-(11186760242463115104121 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (533703873898957 / 5000000000000000 : ℚ))
        (r' := (533703873898957 / 312500000000000 : ℚ))
        (U := (-(11186760242463115104121 / 5000000000000000000000 : ℚ)))
        (U' := (2676183363536884895879 / 5000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (4542766622207 / 16000000000000 : ℚ))
      (s := (643141829661453 / 10000000000000000 : ℚ))
      (q := (533703873898957 / 5000000000000000 : ℚ))
      (U := (-(11186760242463115104121 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_303_10 :
    Uω (aρ 10) (bρ 10) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_303_11 :
    Uω (aρ 11) (bρ 11) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_303_12 :
    Uω (aρ 12) (bρ 12) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_303_13 :
    Uω (aρ 13) (bρ 13) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_303_14 :
    Uω (aρ 14) (bρ 14) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_303_15 :
    Uω (aρ 15) (bρ 15) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_303_16 :
    Uω (aρ 16) (bρ 16) (4542766622207 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_303 :
    Uρ (4542766622207 / 16000000000000 : ℝ) ≤
      (-(8347807468509570491919 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_303_1 U_303_2 U_303_3 U_303_4 U_303_5 U_303_6 U_303_7 U_303_8 U_303_9 U_303_10
    U_303_11 U_303_12 U_303_13 U_303_14 U_303_15 U_303_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
