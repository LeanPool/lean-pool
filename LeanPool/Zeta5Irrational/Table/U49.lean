/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U49) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_592_1 :
    Uω (aρ 1) (bρ 1) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(3861145048423655657401 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10875083087087007 / 16000000000000000 : ℝ) ≤
      (-(3861145048423655657401 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10875083087087007 / 16000000000000000 : ℚ))
        (r' := (10875083087087007 / 8000000000000000 : ℚ))
        (U := (-(3861145048423655657401 / 10000000000000000000000 : ℚ)))
        (U' := (3070326754576344342599 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (1359380628798283 / 2000000000000000 : ℚ))
      (q := (10875083087087007 / 16000000000000000 : ℚ))
      (U := (-(3861145048423655657401 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_2 :
    Uω (aρ 2) (bρ 2) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(243523295113786450747 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2167368019938823 / 3200000000000000 : ℝ) ≤
      (-(243523295113786450747 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2167368019938823 / 3200000000000000 : ℚ))
        (r' := (2167368019938823 / 1600000000000000 : ℚ))
        (U := (-(243523295113786450747 / 625000000000000000000 : ℚ)))
        (U' := (189693692573713549253 / 625000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (67728684222603 / 100000000000000 : ℚ))
      (q := (2167368019938823 / 3200000000000000 : ℚ))
      (U := (-(243523295113786450747 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_3 :
    Uω (aρ 3) (bρ 3) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(991795346368845415999 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53801884576994823 / 80000000000000000 : ℝ) ≤
      (-(991795346368845415999 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53801884576994823 / 80000000000000000 : ℚ))
        (r' := (53801884576994823 / 40000000000000000 : ℚ))
        (U := (-(991795346368845415999 / 2500000000000000000000 : ℚ)))
        (U' := (741072604381154584001 / 2500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (3362342774120681 / 5000000000000000 : ℚ))
      (q := (53801884576994823 / 80000000000000000 : ℚ))
      (U := (-(991795346368845415999 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_4 :
    Uω (aρ 4) (bρ 4) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(51072963081599011411 / 125000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53167267251590347 / 80000000000000000 : ℝ) ≤
      (-(51072963081599011411 / 125000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53167267251590347 / 80000000000000000 : ℚ))
        (r' := (53167267251590347 / 40000000000000000 : ℚ))
        (U := (-(51072963081599011411 / 125000000000000000000 : ℚ)))
        (U' := (35570434455900988589 / 125000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (6644325397955243 / 10000000000000000 : ℚ))
      (q := (53167267251590347 / 80000000000000000 : ℚ))
      (U := (-(51072963081599011411 / 125000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_5 :
    Uω (aρ 5) (bρ 5) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(4269103245193693824213 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (52201765173156339 / 80000000000000000 : ℝ) ≤
      (-(4269103245193693824213 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (52201765173156339 / 80000000000000000 : ℚ))
        (r' := (52201765173156339 / 40000000000000000 : ℚ))
        (U := (-(4269103245193693824213 / 10000000000000000000000 : ℚ)))
        (U' := (2662368557806306175787 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (6521139797681741 / 10000000000000000 : ℚ))
      (q := (52201765173156339 / 80000000000000000 : ℚ))
      (U := (-(4269103245193693824213 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_6 :
    Uω (aρ 6) (bρ 6) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(4537521459674536368377 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (50819212832474303 / 80000000000000000 : ℝ) ≤
      (-(4537521459674536368377 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (50819212832474303 / 80000000000000000 : ℚ))
        (r' := (50819212832474303 / 40000000000000000 : ℚ))
        (U := (-(4537521459674536368377 / 10000000000000000000000 : ℚ)))
        (U' := (2393950343325463631623 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (198210690239101 / 312500000000000 : ℚ))
      (q := (50819212832474303 / 80000000000000000 : ℚ))
      (U := (-(4537521459674536368377 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_7 :
    Uω (aρ 7) (bρ 7) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(614350511180361655339 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48937610193604279 / 80000000000000000 : ℝ) ≤
      (-(614350511180361655339 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (48937610193604279 / 80000000000000000 : ℚ))
        (r' := (48937610193604279 / 40000000000000000 : ℚ))
        (U := (-(614350511180361655339 / 1250000000000000000000 : ℚ)))
        (U' := (252083464194638344661 / 1250000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (3048001404346863 / 5000000000000000 : ℚ))
      (q := (48937610193604279 / 80000000000000000 : ℚ))
      (U := (-(614350511180361655339 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_8 :
    Uω (aρ 8) (bρ 8) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(1356885589740886941109 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46491634748014451 / 80000000000000000 : ℝ) ≤
      (-(1356885589740886941109 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46491634748014451 / 80000000000000000 : ℚ))
        (r' := (46491634748014451 / 40000000000000000 : ℚ))
        (U := (-(1356885589740886941109 / 2500000000000000000000 : ℚ)))
        (U' := (375982361009113058891 / 2500000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (5768050598636269 / 10000000000000000 : ℚ))
      (q := (46491634748014451 / 80000000000000000 : ℚ))
      (U := (-(1356885589740886941109 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_9 :
    Uω (aρ 9) (bρ 9) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(6105539499798913087489 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43443997046514299 / 80000000000000000 : ℝ) ≤
      (-(6105539499798913087489 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43443997046514299 / 80000000000000000 : ℚ))
        (r' := (43443997046514299 / 40000000000000000 : ℚ))
        (U := (-(6105539499798913087489 / 10000000000000000000000 : ℚ)))
        (U' := (825932303201086912511 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (5347106801621231 / 10000000000000000 : ℚ))
      (q := (43443997046514299 / 80000000000000000 : ℚ))
      (U := (-(6105539499798913087489 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_10 :
    Uω (aρ 10) (bρ 10) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(43646592711571477181 / 62500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (39792607378096127 / 80000000000000000 : ℝ) ≤
      (-(43646592711571477181 / 62500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (39792607378096127 / 80000000000000000 : ℚ))
        (r' := (39792607378096127 / 20000000000000000 : ℚ))
        (U := (-(43646592711571477181 / 62500000000000000000 : ℚ)))
        (U' := (42996804825928522819 / 62500000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (602852302251461 / 1250000000000000 : ℚ))
      (q := (39792607378096127 / 80000000000000000 : ℚ))
      (U := (-(43646592711571477181 / 62500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_11 :
    Uω (aρ 11) (bρ 11) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(253299539840680361623 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (35568773592564671 / 80000000000000000 : ℝ) ≤
      (-(253299539840680361623 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35568773592564671 / 80000000000000000 : ℚ))
        (r' := (35568773592564671 / 20000000000000000 : ℚ))
        (U := (-(253299539840680361623 / 312500000000000000000 : ℚ)))
        (U' := (179917447846819638377 / 312500000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (130791768682307 / 312500000000000 : ℚ))
      (q := (35568773592564671 / 80000000000000000 : ℚ))
      (U := (-(253299539840680361623 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_12 :
    Uω (aρ 12) (bρ 12) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(9539803762064064091603 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30816376645680631 / 80000000000000000 : ℝ) ≤
      (-(9539803762064064091603 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30816376645680631 / 80000000000000000 : ℚ))
        (r' := (30816376645680631 / 20000000000000000 : ℚ))
        (U := (-(9539803762064064091603 / 10000000000000000000000 : ℚ)))
        (U' := (4323139843935935908397 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (1710468728898907 / 5000000000000000 : ℚ))
      (q := (30816376645680631 / 80000000000000000 : ℚ))
      (U := (-(9539803762064064091603 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_13 :
    Uω (aρ 13) (bρ 13) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(11428424110941748224189 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25512900419887071 / 80000000000000000 : ℝ) ≤
      (-(11428424110941748224189 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25512900419887071 / 80000000000000000 : ℚ))
        (r' := (25512900419887071 / 20000000000000000 : ℚ))
        (U := (-(11428424110941748224189 / 10000000000000000000000 : ℚ)))
        (U' := (2434519495058251775811 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (311806267868053 / 1250000000000000 : ℚ))
      (q := (25512900419887071 / 80000000000000000 : ℚ))
      (U := (-(11428424110941748224189 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_14 :
    Uω (aρ 14) (bρ 14) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(7171437141596351498281 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19062807884872551 / 80000000000000000 : ℝ) ≤
      (-(7171437141596351498281 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19062807884872551 / 80000000000000000 : ℚ))
        (r' := (19062807884872551 / 10000000000000000 : ℚ))
        (U := (-(7171437141596351498281 / 5000000000000000000000 : ℚ)))
        (U' := (3225770562903648501719 / 5000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (8782653354179 / 12800000000000 : ℚ))
      (s := (612927147117897 / 5000000000000000 : ℚ))
      (q := (19062807884872551 / 80000000000000000 : ℚ))
      (U := (-(7171437141596351498281 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_592_15 :
    Uω (aρ 15) (bρ 15) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_592_16 :
    Uω (aρ 16) (bρ 16) (8782653354179 / 12800000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_592 :
    Uρ (8782653354179 / 12800000000000 : ℝ) ≤
      (-(6493372085490171878343 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_592_1 U_592_2 U_592_3 U_592_4 U_592_5 U_592_6 U_592_7 U_592_8 U_592_9 U_592_10
    U_592_11 U_592_12 U_592_13 U_592_14 U_592_15 U_592_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_593_1 :
    Uω (aρ 1) (bρ 1) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(76984335362129264989 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6805039331788933 / 10000000000000000 : ℝ) ≤
      (-(76984335362129264989 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6805039331788933 / 10000000000000000 : ℚ))
        (r' := (6805039331788933 / 5000000000000000 : ℚ))
        (U := (-(76984335362129264989 / 200000000000000000000 : ℚ)))
        (U' := (61645100697870735011 / 200000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (6805015574705991 / 10000000000000000 : ℚ))
      (q := (6805039331788933 / 10000000000000000 : ℚ))
      (U := (-(76984335362129264989 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_2 :
    Uω (aρ 2) (bρ 2) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(9711005343742677657 / 25000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (339056881185423 / 500000000000000 : ℝ) ≤
      (-(9711005343742677657 / 25000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (339056881185423 / 500000000000000 : ℚ))
        (r' := (339056881185423 / 250000000000000 : ℚ))
        (U := (-(9711005343742677657 / 25000000000000000000 : ℚ)))
        (U' := (7617674163757322343 / 25000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (1356196234211009 / 2000000000000000 : ℚ))
      (q := (339056881185423 / 500000000000000 : ℚ))
      (U := (-(9711005343742677657 / 25000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_3 :
    Uω (aρ 3) (bρ 3) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(31641000668466948117 / 80000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2693339443541881 / 4000000000000000 : ℝ) ≤
      (-(31641000668466948117 / 80000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2693339443541881 / 4000000000000000 : ℚ))
        (r' := (2693339443541881 / 2000000000000000 : ℚ))
        (U := (-(31641000668466948117 / 80000000000000000000 : ℚ)))
        (U' := (23810773755533051883 / 80000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (673279924769753 / 1000000000000000 : ℚ))
      (q := (2693339443541881 / 4000000000000000 : ℚ))
      (U := (-(31641000668466948117 / 80000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_4 :
    Uω (aρ 4) (bρ 4) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(4073635020287535188957 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1330804542173291 / 2000000000000000 : ℝ) ≤
      (-(4073635020287535188957 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1330804542173291 / 2000000000000000 : ℚ))
        (r' := (1330804542173291 / 1000000000000000 : ℚ))
        (U := (-(4073635020287535188957 / 10000000000000000000000 : ℚ)))
        (U' := (2857836782712464811043 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (1330488326557207 / 2000000000000000 : ℚ))
      (q := (1330804542173291 / 2000000000000000 : ℚ))
      (U := (-(4073635020287535188957 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_5 :
    Uω (aρ 5) (bρ 5) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(4256670869576362918179 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13066676181922667 / 20000000000000000 : ℝ) ≤
      (-(4256670869576362918179 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13066676181922667 / 20000000000000000 : ℚ))
        (r' := (13066676181922667 / 10000000000000000 : ℚ))
        (U := (-(4256670869576362918179 / 10000000000000000000000 : ℚ)))
        (U' := (2674800933423637081821 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (816157789038849 / 1250000000000000 : ℚ))
      (q := (13066676181922667 / 20000000000000000 : ℚ))
      (U := (-(4256670869576362918179 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_6 :
    Uω (aρ 6) (bρ 6) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(452473964593663599121 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12721052633581053 / 20000000000000000 : ℝ) ≤
      (-(452473964593663599121 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12721052633581053 / 20000000000000000 : ℚ))
        (r' := (12721052633581053 / 10000000000000000 : ℚ))
        (U := (-(452473964593663599121 / 1000000000000000000000 : ℚ)))
        (U' := (240673215706336400879 / 1000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (3175439569554589 / 5000000000000000 : ℚ))
      (q := (12721052633581053 / 20000000000000000 : ℚ))
      (U := (-(452473964593663599121 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_7 :
    Uω (aρ 7) (bρ 7) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(4901505303743168612503 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2450136728341123 / 4000000000000000 : ℝ) ≤
      (-(4901505303743168612503 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2450136728341123 / 4000000000000000 : ℚ))
        (r' := (2450136728341123 / 2000000000000000 : ℚ))
        (U := (-(4901505303743168612503 / 10000000000000000000000 : ℚ)))
        (U' := (2029966499256831387497 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (305208576399687 / 500000000000000 : ℚ))
      (q := (2450136728341123 / 4000000000000000 : ℚ))
      (U := (-(4901505303743168612503 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_8 :
    Uω (aρ 8) (bρ 8) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(2706744031536615135693 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11639255351134963 / 20000000000000000 : ℝ) ≤
      (-(2706744031536615135693 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11639255351134963 / 20000000000000000 : ℚ))
        (r' := (11639255351134963 / 10000000000000000 : ℚ))
        (U := (-(2706744031536615135693 / 5000000000000000000000 : ℚ)))
        (U' := (758991869963384864307 / 5000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (361017805547693 / 625000000000000 : ℚ))
      (q := (11639255351134963 / 20000000000000000 : ℚ))
      (U := (-(2706744031536615135693 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_9 :
    Uω (aρ 9) (bρ 9) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(1522594958593701806993 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10877476659562703 / 20000000000000000 : ℝ) ≤
      (-(1522594958593701806993 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10877476659562703 / 20000000000000000 : ℚ))
        (r' := (10877476659562703 / 10000000000000000 : ℚ))
        (U := (-(1522594958593701806993 / 2500000000000000000000 : ℚ)))
        (U' := (210272992156298193007 / 2500000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (1338867956387707 / 2500000000000000 : ℚ))
      (q := (10877476659562703 / 20000000000000000 : ℚ))
      (U := (-(1522594958593701806993 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_10 :
    Uω (aρ 10) (bρ 10) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(6966649033551154060933 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2491221141562591 / 5000000000000000 : ℝ) ≤
      (-(6966649033551154060933 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2491221141562591 / 5000000000000000 : ℚ))
        (r' := (2491221141562591 / 1250000000000000 : ℚ))
        (U := (-(6966649033551154060933 / 10000000000000000000000 : ℚ)))
        (U' := (6896294572448845939067 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (4831438765733489 / 10000000000000000 : ℚ))
      (q := (2491221141562591 / 5000000000000000 : ℚ))
      (U := (-(6966649033551154060933 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_11 :
    Uω (aρ 11) (bρ 11) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(8086223519225050504341 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (556839182745233 / 1250000000000000 : ℝ) ≤
      (-(8086223519225050504341 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (556839182745233 / 1250000000000000 : ℚ))
        (r' := (556839182745233 / 312500000000000 : ℚ))
        (U := (-(8086223519225050504341 / 10000000000000000000000 : ℚ)))
        (U' := (5776720086774949495659 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (4194457749611853 / 10000000000000000 : ℚ))
      (q := (556839182745233 / 1250000000000000 : ℚ))
      (U := (-(8086223519225050504341 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_12 :
    Uω (aρ 12) (bρ 12) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(1903224998521094270931 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1544471624649439 / 4000000000000000 : ℝ) ≤
      (-(1903224998521094270931 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1544471624649439 / 4000000000000000 : ℚ))
        (r' := (1544471624649439 / 1000000000000000 : ℚ))
        (U := (-(1903224998521094270931 / 2000000000000000000000 : ℚ)))
        (U' := (869363722678905729069 / 2000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (21444306535127 / 62500000000000 : ℚ))
      (q := (1544471624649439 / 4000000000000000 : ℚ))
      (U := (-(1903224998521094270931 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_13 :
    Uω (aρ 13) (bρ 13) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(1424498049762649303159 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6398949480520967 / 20000000000000000 : ℝ) ≤
      (-(1424498049762649303159 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6398949480520967 / 20000000000000000 : ℚ))
        (r' := (6398949480520967 / 5000000000000000 : ℚ))
        (U := (-(1424498049762649303159 / 1250000000000000000000 : ℚ)))
        (U' := (308369900987350696841 / 1250000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (626765536122273 / 2500000000000000 : ℚ))
      (q := (6398949480520967 / 20000000000000000 : ℚ))
      (U := (-(1424498049762649303159 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_14 :
    Uω (aρ 14) (bρ 14) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(713865897465215119503 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1199261699129129 / 5000000000000000 : ℝ) ≤
      (-(713865897465215119503 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1199261699129129 / 5000000000000000 : ℚ))
        (r' := (1199261699129129 / 625000000000000 : ℚ))
        (U := (-(713865897465215119503 / 500000000000000000000 : ℚ)))
        (U' := (325854872984784880497 / 500000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (10991296491131 / 16000000000000 : ℚ))
      (s := (1249086745529641 / 10000000000000000 : ℚ))
      (q := (1199261699129129 / 5000000000000000 : ℚ))
      (U := (-(713865897465215119503 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_593_15 :
    Uω (aρ 15) (bρ 15) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_593_16 :
    Uω (aρ 16) (bρ 16) (10991296491131 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_593 :
    Uρ (10991296491131 / 16000000000000 : ℝ) ≤
      (-(6476639339068879338977 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_593_1 U_593_2 U_593_3 U_593_4 U_593_5 U_593_6 U_593_7 U_593_8 U_593_9 U_593_10
    U_593_11 U_593_12 U_593_13 U_593_14 U_593_15 U_593_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_594_1 :
    Uω (aρ 1) (bρ 1) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(3837302699325395042261 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54505213872647697 / 80000000000000000 : ℝ) ≤
      (-(3837302699325395042261 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54505213872647697 / 80000000000000000 : ℚ))
        (r' := (54505213872647697 / 40000000000000000 : ℚ))
        (U := (-(3837302699325395042261 / 10000000000000000000000 : ℚ)))
        (U' := (3094169103674604957739 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (3406564002642759 / 5000000000000000 : ℚ))
      (q := (54505213872647697 / 80000000000000000 : ℚ))
      (U := (-(3837302699325395042261 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_2 :
    Uω (aρ 2) (bρ 2) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(3872445866191089838999 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54314001477281973 / 80000000000000000 : ℝ) ≤
      (-(3872445866191089838999 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54314001477281973 / 80000000000000000 : ℚ))
        (r' := (54314001477281973 / 40000000000000000 : ℚ))
        (U := (-(3872445866191089838999 / 10000000000000000000000 : ℚ)))
        (U' := (3059025936808910161001 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (6789093918954087 / 10000000000000000 : ℚ))
      (q := (54314001477281973 / 80000000000000000 : ℚ))
      (U := (-(3872445866191089838999 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_3 :
    Uω (aρ 3) (bρ 3) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(1971541650973881459497 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53931693151918417 / 80000000000000000 : ℝ) ≤
      (-(1971541650973881459497 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53931693151918417 / 80000000000000000 : ℚ))
        (r' := (53931693151918417 / 40000000000000000 : ℚ))
        (U := (-(1971541650973881459497 / 5000000000000000000000 : ℚ)))
        (U' := (1494194250526118540503 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (3370456471981599 / 5000000000000000 : ℚ))
      (q := (53931693151918417 / 80000000000000000 : ℚ))
      (U := (-(1971541650973881459497 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_4 :
    Uω (aρ 4) (bρ 4) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(2030723935954041162807 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53297096084644953 / 80000000000000000 : ℝ) ≤
      (-(2030723935954041162807 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53297096084644953 / 80000000000000000 : ℚ))
        (r' := (53297096084644953 / 40000000000000000 : ℚ))
        (U := (-(2030723935954041162807 / 5000000000000000000000 : ℚ)))
        (U' := (1435011965545958837193 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (832569732276229 / 1250000000000000 : ℚ))
      (q := (53297096084644953 / 80000000000000000 : ℚ))
      (U := (-(2030723935954041162807 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_5 :
    Uω (aρ 5) (bρ 5) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(4244253950414137293169 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (52331644181492417 / 80000000000000000 : ℝ) ≤
      (-(4244253950414137293169 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (52331644181492417 / 80000000000000000 : ℚ))
        (r' := (52331644181492417 / 40000000000000000 : ℚ))
        (U := (-(4244253950414137293169 / 10000000000000000000000 : ℚ)))
        (U' := (2687217852585862706831 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (3268692400878349 / 5000000000000000 : ℚ))
      (q := (52331644181492417 / 80000000000000000 : ℚ))
      (U := (-(4244253950414137293169 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_6 :
    Uω (aρ 6) (bρ 6) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(4511974198329091467151 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (50949207983937341 / 80000000000000000 : ℝ) ≤
      (-(4511974198329091467151 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (50949207983937341 / 80000000000000000 : ℚ))
        (r' := (50949207983937341 / 40000000000000000 : ℚ))
        (U := (-(4511974198329091467151 / 10000000000000000000000 : ℚ)))
        (U' := (2419497604670908532849 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (6359016127507929 / 10000000000000000 : ℚ))
      (q := (50949207983937341 / 80000000000000000 : ℚ))
      (U := (-(4511974198329091467151 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_7 :
    Uω (aρ 7) (bρ 7) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(2444112151337690036797 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (49067858339705593 / 80000000000000000 : ℝ) ≤
      (-(2444112151337690036797 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (49067858339705593 / 80000000000000000 : ℚ))
        (r' := (49067858339705593 / 40000000000000000 : ℚ))
        (U := (-(2444112151337690036797 / 5000000000000000000000 : ℚ)))
        (U' := (1021623750162309963203 / 5000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (764042512151249 / 1250000000000000 : ℚ))
      (q := (49067858339705593 / 80000000000000000 : ℚ))
      (U := (-(2444112151337690036797 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_8 :
    Uω (aρ 8) (bρ 8) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(43195630299015583237 / 80000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46622406682957993 / 80000000000000000 : ℝ) ≤
      (-(43195630299015583237 / 80000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46622406682957993 / 80000000000000000 : ℚ))
        (r' := (46622406682957993 / 40000000000000000 : ℚ))
        (U := (-(43195630299015583237 / 80000000000000000000 : ℚ)))
        (U' := (12256144124984416763 / 80000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (1446129708590773 / 2500000000000000 : ℚ))
      (q := (46622406682957993 / 80000000000000000 : ℚ))
      (U := (-(43195630299015583237 / 80000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_9 :
    Uω (aρ 9) (bρ 9) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(1215048765630322143733 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43575813125483009 / 80000000000000000 : ℝ) ≤
      (-(1215048765630322143733 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43575813125483009 / 80000000000000000 : ℚ))
        (r' := (43575813125483009 / 40000000000000000 : ℚ))
        (U := (-(1215048765630322143733 / 2000000000000000000000 : ℚ)))
        (U' := (171245594969677856267 / 2000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (2681918036677173 / 5000000000000000 : ℚ))
      (q := (43575813125483009 / 80000000000000000 : ℚ))
      (U := (-(1215048765630322143733 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_10 :
    Uω (aρ 10) (bρ 10) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(1389974637746149243031 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (39926462127377373 / 80000000000000000 : ℝ) ≤
      (-(1389974637746149243031 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (39926462127377373 / 80000000000000000 : ℚ))
        (r' := (39926462127377373 / 20000000000000000 : ℚ))
        (U := (-(1389974637746149243031 / 2000000000000000000000 : ℚ)))
        (U' := (1382614083453850756969 / 2000000000000000000000 : ℚ))
        2 15 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (4840057357322937 / 10000000000000000 : ℚ))
      (q := (39926462127377373 / 80000000000000000 : ℚ))
      (U := (-(1389974637746149243031 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_11 :
    Uω (aρ 11) (bρ 11) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(8066903811869647594891 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (35706625255963241 / 80000000000000000 : ℝ) ≤
      (-(8066903811869647594891 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35706625255963241 / 80000000000000000 : ℚ))
        (r' := (35706625255963241 / 20000000000000000 : ℚ))
        (U := (-(8066903811869647594891 / 10000000000000000000000 : ℚ)))
        (U' := (5796039794130352405109 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (1050893691418601 / 2500000000000000 : ℚ))
      (q := (35706625255963241 / 80000000000000000 : ℚ))
      (U := (-(8066903811869647594891 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_12 :
    Uω (aρ 12) (bρ 12) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(4746258070544322986259 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30962445048721753 / 80000000000000000 : ℝ) ≤
      (-(4746258070544322986259 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30962445048721753 / 80000000000000000 : ℚ))
        (r' := (30962445048721753 / 20000000000000000 : ℚ))
        (U := (-(4746258070544322986259 / 5000000000000000000000 : ℚ)))
        (U' := (2185213732455677013741 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (430153726318629 / 1250000000000000 : ℚ))
      (q := (30962445048721753 / 80000000000000000 : ℚ))
      (U := (-(4746258070544322986259 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_13 :
    Uω (aρ 13) (bρ 13) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(2272741445869784425119 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25678547385049509 / 80000000000000000 : ℝ) ≤
      (-(2272741445869784425119 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25678547385049509 / 80000000000000000 : ℚ))
        (r' := (25678547385049509 / 20000000000000000 : ℚ))
        (U := (-(2272741445869784425119 / 2000000000000000000000 : ℚ)))
        (U' := (499847275330215574881 / 2000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (2519637136225971 / 10000000000000000 : ℚ))
      (q := (25678547385049509 / 80000000000000000 : ℚ))
      (U := (-(2272741445869784425119 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_14 :
    Uω (aρ 14) (bρ 14) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(14212960197935088470847 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19312076277633053 / 80000000000000000 : ℝ) ≤
      (-(14212960197935088470847 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19312076277633053 / 80000000000000000 : ℚ))
        (r' := (19312076277633053 / 10000000000000000 : ℚ))
        (U := (-(14212960197935088470847 / 10000000000000000000000 : ℚ)))
        (U' := (6581455211064911529153 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (44017105158153 / 64000000000000 : ℚ))
      (s := (1271946644416857 / 10000000000000000 : ℚ))
      (q := (19312076277633053 / 80000000000000000 : ℚ))
      (U := (-(14212960197935088470847 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_594_15 :
    Uω (aρ 15) (bρ 15) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_594_16 :
    Uω (aρ 16) (bρ 16) (44017105158153 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_594 :
    Uρ (44017105158153 / 64000000000000 : ℝ) ≤
      (-(3229994991353601011403 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_594_1 U_594_2 U_594_3 U_594_4 U_594_5 U_594_6 U_594_7 U_594_8 U_594_9 U_594_10
    U_594_11 U_594_12 U_594_13 U_594_14 U_594_15 U_594_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_595_1 :
    Uω (aρ 1) (bρ 1) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(3825402808256825816339 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27285056545222829 / 40000000000000000 : ℝ) ≤
      (-(3825402808256825816339 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27285056545222829 / 40000000000000000 : ℚ))
        (r' := (27285056545222829 / 20000000000000000 : ℚ))
        (U := (-(3825402808256825816339 / 10000000000000000000000 : ℚ)))
        (U' := (3106068994743174183661 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (6821240435730477 / 10000000000000000 : ℚ))
      (q := (27285056545222829 / 40000000000000000 : ℚ))
      (U := (-(3825402808256825816339 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_2 :
    Uω (aρ 2) (bρ 2) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(965125968428573373733 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27189450980663139 / 40000000000000000 : ℝ) ≤
      (-(965125968428573373733 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27189450980663139 / 40000000000000000 : ℚ))
        (r' := (27189450980663139 / 20000000000000000 : ℚ))
        (U := (-(965125968428573373733 / 2500000000000000000000 : ℚ)))
        (U' := (767741982321426626267 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (849650833245079 / 1250000000000000 : ℚ))
      (q := (27189450980663139 / 40000000000000000 : ℚ))
      (U := (-(965125968428573373733 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_3 :
    Uω (aρ 3) (bρ 3) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(786211201140834157933 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (215986389681133 / 320000000000000 : ℝ) ≤
      (-(786211201140834157933 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (215986389681133 / 320000000000000 : ℚ))
        (r' := (215986389681133 / 160000000000000 : ℚ))
        (U := (-(786211201140834157933 / 2000000000000000000000 : ℚ)))
        (U' := (600083159459165842067 / 2000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (53992213096399 / 80000000000000 : ℚ))
      (q := (215986389681133 / 320000000000000 : ℚ))
      (U := (-(786211201140834157933 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_4 :
    Uω (aρ 4) (bρ 4) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(2024637782567805178767 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5336201044486767 / 8000000000000000 : ℝ) ≤
      (-(2024637782567805178767 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5336201044486767 / 8000000000000000 : ℚ))
        (r' := (5336201044486767 / 4000000000000000 : ℚ))
        (U := (-(2024637782567805178767 / 5000000000000000000000 : ℚ)))
        (U' := (1441098118932194821233 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (333433703713049 / 500000000000000 : ℚ))
      (q := (5336201044486767 / 8000000000000000 : ℚ))
      (U := (-(2024637782567805178767 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_5 :
    Uω (aρ 5) (bρ 5) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(528981556159355254323 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5239658353493659 / 8000000000000000 : ℝ) ≤
      (-(528981556159355254323 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5239658353493659 / 8000000000000000 : ℚ))
        (r' := (5239658353493659 / 4000000000000000 : ℚ))
        (U := (-(528981556159355254323 / 1250000000000000000000 : ℚ)))
        (U' := (337452419215644745677 / 1250000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (654550726611321 / 1000000000000000 : ℚ))
      (q := (5239658353493659 / 8000000000000000 : ℚ))
      (U := (-(528981556159355254323 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_6 :
    Uω (aρ 6) (bρ 6) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(4499225074868244073119 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25507102591140369 / 40000000000000000 : ℝ) ≤
      (-(4499225074868244073119 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25507102591140369 / 40000000000000000 : ℚ))
        (r' := (25507102591140369 / 20000000000000000 : ℚ))
        (U := (-(4499225074868244073119 / 10000000000000000000000 : ℚ)))
        (U' := (2432246728131755926881 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (6367153053089247 / 10000000000000000 : ℚ))
      (q := (25507102591140369 / 40000000000000000 : ℚ))
      (U := (-(4499225074868244073119 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_7 :
    Uω (aρ 7) (bρ 7) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(97499220768220577801 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24566490757328667 / 40000000000000000 : ℝ) ≤
      (-(97499220768220577801 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24566490757328667 / 40000000000000000 : ℚ))
        (r' := (24566490757328667 / 20000000000000000 : ℚ))
        (U := (-(97499220768220577801 / 200000000000000000000 : ℚ)))
        (U' := (41130215291779422199 / 200000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (1530127129235849 / 2500000000000000 : ℚ))
      (q := (24566490757328667 / 40000000000000000 : ℚ))
      (U := (-(97499220768220577801 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_8 :
    Uω (aρ 8) (bρ 8) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(5385439474086395814851 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23343895294572749 / 40000000000000000 : ℝ) ≤
      (-(5385439474086395814851 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23343895294572749 / 40000000000000000 : ℚ))
        (r' := (23343895294572749 / 20000000000000000 : ℚ))
        (U := (-(5385439474086395814851 / 10000000000000000000000 : ℚ)))
        (U' := (1546032328913604185149 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (5792752436905437 / 10000000000000000 : ℚ))
      (q := (23343895294572749 / 40000000000000000 : ℚ))
      (U := (-(5385439474086395814851 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_9 :
    Uω (aρ 9) (bρ 9) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(94689553206502731041 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21820858261355787 / 40000000000000000 : ℝ) ≤
      (-(94689553206502731041 / 156250000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21820858261355787 / 40000000000000000 : ℚ))
        (r' := (21820858261355787 / 20000000000000000 : ℚ))
        (U := (-(94689553206502731041 / 156250000000000000000 : ℚ)))
        (U' := (13614693715372268959 / 156250000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (1343049887164239 / 2500000000000000 : ℚ))
      (q := (21820858261355787 / 40000000000000000 : ℚ))
      (U := (-(94689553206502731041 / 156250000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_10 :
    Uω (aρ 10) (bρ 10) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(3466563593368778755967 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19996689501341251 / 40000000000000000 : ℝ) ≤
      (-(3466563593368778755967 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19996689501341251 / 40000000000000000 : ℚ))
        (r' := (19996689501341251 / 10000000000000000 : ℚ))
        (U := (-(3466563593368778755967 / 5000000000000000000000 : ℚ)))
        (U' := (3464908209631221244033 / 5000000000000000000000 : ℚ))
        2 15 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (303042137634043 / 625000000000000 : ℚ))
      (q := (19996689501341251 / 40000000000000000 : ℚ))
      (U := (-(3466563593368778755967 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_11 :
    Uω (aρ 11) (bρ 11) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(502976621982016817177 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17887763190387439 / 40000000000000000 : ℝ) ≤
      (-(502976621982016817177 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17887763190387439 / 40000000000000000 : ℚ))
        (r' := (17887763190387439 / 10000000000000000 : ℚ))
        (U := (-(502976621982016817177 / 625000000000000000000 : ℚ)))
        (U' := (363457353392983182823 / 625000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (2106343836436391 / 5000000000000000 : ℚ))
      (q := (17887763190387439 / 40000000000000000 : ℚ))
      (U := (-(502976621982016817177 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_12 :
    Uω (aρ 12) (bρ 12) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(9468976722227678351319 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15517707347238349 / 40000000000000000 : ℝ) ≤
      (-(9468976722227678351319 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (15517707347238349 / 40000000000000000 : ℚ))
        (r' := (15517707347238349 / 10000000000000000 : ℚ))
        (U := (-(9468976722227678351319 / 10000000000000000000000 : ℚ)))
        (U' := (4393966883772321648681 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (3451359847983237 / 10000000000000000 : ℚ))
      (q := (15517707347238349 / 40000000000000000 : ℚ))
      (U := (-(9468976722227678351319 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_13 :
    Uω (aρ 13) (bρ 13) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(708224407302227743551 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2576115101430907 / 8000000000000000 : ℝ) ≤
      (-(708224407302227743551 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2576115101430907 / 8000000000000000 : ℚ))
        (r' := (2576115101430907 / 2000000000000000 : ℚ))
        (U := (-(708224407302227743551 / 625000000000000000000 : ℚ)))
        (U' := (158209568072772256449 / 625000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (253217566953633 / 1000000000000000 : ℚ))
      (q := (2576115101430907 / 8000000000000000 : ℚ))
      (U := (-(708224407302227743551 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_14 :
    Uω (aρ 14) (bρ 14) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(1768717515541818394809 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9717277055474861 / 40000000000000000 : ℝ) ≤
      (-(1768717515541818394809 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9717277055474861 / 40000000000000000 : ℚ))
        (r' := (9717277055474861 / 5000000000000000 : ℚ))
        (U := (-(1768717515541818394809 / 1250000000000000000000 : ℚ)))
        (U' := (830584410583181605191 / 1250000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (22034512175891 / 32000000000000 : ℚ))
      (s := (1294453728741493 / 10000000000000000 : ℚ))
      (q := (9717277055474861 / 40000000000000000 : ℚ))
      (U := (-(1768717515541818394809 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_595_15 :
    Uω (aρ 15) (bρ 15) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_595_16 :
    Uω (aρ 16) (bρ 16) (22034512175891 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_595 :
    Uρ (22034512175891 / 32000000000000 : ℝ) ≤
      (-(3221710550820856703479 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_595_1 U_595_2 U_595_3 U_595_4 U_595_5 U_595_6 U_595_7 U_595_8 U_595_9 U_595_10
    U_595_11 U_595_12 U_595_13 U_595_14 U_595_15 U_595_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_596_1 :
    Uω (aρ 1) (bρ 1) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(3813517061197737683561 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54635012307707267 / 80000000000000000 : ℝ) ≤
      (-(3813517061197737683561 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54635012307707267 / 80000000000000000 : ℚ))
        (r' := (54635012307707267 / 40000000000000000 : ℚ))
        (U := (-(3813517061197737683561 / 10000000000000000000000 : ℚ)))
        (U' := (3117954741802262316439 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (1707338216510337 / 2500000000000000 : ℚ))
      (q := (54635012307707267 / 80000000000000000 : ℚ))
      (U := (-(3813517061197737683561 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_2 :
    Uω (aρ 2) (bρ 2) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(962144031500172235307 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54443802441813363 / 80000000000000000 : ℝ) ≤
      (-(962144031500172235307 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54443802441813363 / 80000000000000000 : ℚ))
        (r' := (54443802441813363 / 40000000000000000 : ℚ))
        (U := (-(962144031500172235307 / 2500000000000000000000 : ℚ)))
        (U' := (770723919249827764693 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (425332463254867 / 625000000000000 : ℚ))
      (q := (54443802441813363 / 80000000000000000 : ℚ))
      (U := (-(962144031500172235307 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_3 :
    Uω (aρ 3) (bρ 3) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(1959521580007089325513 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54061501675977919 / 80000000000000000 : ℝ) ≤
      (-(1959521580007089325513 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54061501675977919 / 80000000000000000 : ℚ))
        (r' := (54061501675977919 / 40000000000000000 : ℚ))
        (U := (-(1959521580007089325513 / 5000000000000000000000 : ℚ)))
        (U' := (1506214321492910674487 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (6757140326969011 / 10000000000000000 : ℚ))
      (q := (54061501675977919 / 80000000000000000 : ℚ))
      (U := (-(1959521580007089325513 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_4 :
    Uω (aρ 4) (bρ 4) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(2018559031924290803153 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53426924767736511 / 80000000000000000 : ℝ) ≤
      (-(2018559031924290803153 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53426924767736511 / 80000000000000000 : ℚ))
        (r' := (53426924767736511 / 40000000000000000 : ℚ))
        (U := (-(2018559031924290803153 / 5000000000000000000000 : ℚ)))
        (U' := (1447176869575709196847 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (6676790280973659 / 10000000000000000 : ℚ))
      (q := (53426924767736511 / 80000000000000000 : ℚ))
      (U := (-(2018559031924290803153 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_5 :
    Uω (aρ 5) (bρ 5) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(105486658196741034191 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10492304557679267 / 16000000000000000 : ℝ) ≤
      (-(105486658196741034191 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10492304557679267 / 16000000000000000 : ℚ))
        (r' := (10492304557679267 / 8000000000000000 : ℚ))
        (U := (-(105486658196741034191 / 250000000000000000000 : ℚ)))
        (U' := (67800136878258965809 / 250000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (1310725941094723 / 2000000000000000 : ℚ))
      (q := (10492304557679267 / 16000000000000000 : ℚ))
      (U := (-(105486658196741034191 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_6 :
    Uω (aρ 6) (bρ 6) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(4486492233732258104221 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (51079202130316507 / 80000000000000000 : ℝ) ≤
      (-(4486492233732258104221 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (51079202130316507 / 80000000000000000 : ℚ))
        (r' := (51079202130316507 / 40000000000000000 : ℚ))
        (U := (-(4486492233732258104221 / 10000000000000000000000 : ℚ)))
        (U' := (2444979569267741895779 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (3187644958046829 / 5000000000000000 : ℚ))
      (q := (51079202130316507 / 80000000000000000 : ℚ))
      (U := (-(4486492233732258104221 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_7 :
    Uω (aρ 7) (bρ 7) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(4861715463315582096821 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (49198104094068487 / 80000000000000000 : ℝ) ≤
      (-(4861715463315582096821 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (49198104094068487 / 80000000000000000 : ℚ))
        (r' := (49198104094068487 / 40000000000000000 : ℚ))
        (U := (-(4861715463315582096821 / 10000000000000000000000 : ℚ)))
        (U' := (2069756339684417903179 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (6128676787791653 / 10000000000000000 : ℚ))
      (q := (49198104094068487 / 80000000000000000 : ℚ))
      (U := (-(4861715463315582096821 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_8 :
    Uω (aρ 8) (bρ 8) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(42971560525332844949 / 80000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46753173128945367 / 80000000000000000 : ℝ) ≤
      (-(42971560525332844949 / 80000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46753173128945367 / 80000000000000000 : ℚ))
        (r' := (46753173128945367 / 40000000000000000 : ℚ))
        (U := (-(42971560525332844949 / 80000000000000000000 : ℚ)))
        (U' := (12480213898667155051 / 80000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (5800985697850873 / 10000000000000000 : ℚ))
      (q := (46753173128945367 / 80000000000000000 : ℚ))
      (U := (-(42971560525332844949 / 80000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_9 :
    Uω (aρ 9) (bρ 9) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(1209008498005994149171 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43707616844345691 / 80000000000000000 : ℝ) ≤
      (-(1209008498005994149171 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43707616844345691 / 80000000000000000 : ℚ))
        (r' := (43707616844345691 / 40000000000000000 : ℚ))
        (U := (-(1209008498005994149171 / 2000000000000000000000 : ℚ)))
        (U' := (177285862594005850829 / 2000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (2690281127530477 / 5000000000000000 : ℚ))
      (q := (43707616844345691 / 80000000000000000 : ℚ))
      (U := (-(1209008498005994149171 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_10 :
    Uω (aρ 10) (bρ 10) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(3458205459091484569321 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40060288928102091 / 80000000000000000 : ℝ) ≤
      (-(3458205459091484569321 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (40060288928102091 / 80000000000000000 : ℚ))
        (r' := (40060288928102091 / 40000000000000000 : ℚ))
        (U := (-(3458205459091484569321 / 5000000000000000000000 : ℚ)))
        (U' := (7530442408515430679 / 5000000000000000000000 : ℚ))
        1 2 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (2428644654747527 / 5000000000000000 : ℚ))
      (q := (40060288928102091 / 80000000000000000 : ℚ))
      (U := (-(3458205459091484569321 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_11 :
    Uω (aρ 11) (bρ 11) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(8028389739178359166687 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (35844411176559483 / 80000000000000000 : ℝ) ≤
      (-(8028389739178359166687 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35844411176559483 / 80000000000000000 : ℚ))
        (r' := (35844411176559483 / 20000000000000000 : ℚ))
        (U := (-(8028389739178359166687 / 10000000000000000000000 : ℚ)))
        (U' := (5834553866821640833313 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (2110898248907201 / 5000000000000000 : ℚ))
      (q := (35844411176559483 / 80000000000000000 : ℚ))
      (U := (-(8028389739178359166687 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_12 :
    Uω (aρ 12) (bρ 12) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(295172070509336324951 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (31108341806982459 / 80000000000000000 : ℝ) ≤
      (-(295172070509336324951 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (31108341806982459 / 80000000000000000 : ℚ))
        (r' := (31108341806982459 / 20000000000000000 : ℚ))
        (U := (-(295172070509336324951 / 312500000000000000000 : ℚ)))
        (U' := (138044917178163675049 / 312500000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (1730739626052573 / 5000000000000000 : ℚ))
      (q := (31108341806982459 / 80000000000000000 : ℚ))
      (U := (-(295172070509336324951 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_13 :
    Uω (aρ 13) (bρ 13) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(2259926443505063997727 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25843610965586107 / 80000000000000000 : ℝ) ≤
      (-(2259926443505063997727 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25843610965586107 / 80000000000000000 : ℚ))
        (r' := (25843610965586107 / 20000000000000000 : ℚ))
        (U := (-(2259926443505063997727 / 2000000000000000000000 : ℚ)))
        (U' := (512662277694936002273 / 2000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (1272339141675529 / 5000000000000000 : ℚ))
      (q := (25843610965586107 / 80000000000000000 : ℚ))
      (U := (-(2259926443505063997727 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_14 :
    Uω (aρ 14) (bρ 14) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(7043800923483328933247 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19555693060838851 / 80000000000000000 : ℝ) ≤
      (-(7043800923483328933247 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19555693060838851 / 80000000000000000 : ℚ))
        (r' := (19555693060838851 / 10000000000000000 : ℚ))
        (U := (-(7043800923483328933247 / 5000000000000000000000 : ℚ)))
        (U' := (3353406781016671066753 / 5000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (44120943545411 / 64000000000000 : ℚ))
      (s := (329156523052311 / 2500000000000000 : ℚ))
      (q := (19555693060838851 / 80000000000000000 : ℚ))
      (U := (-(7043800923483328933247 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_596_15 :
    Uω (aρ 15) (bρ 15) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_596_16 :
    Uω (aρ 16) (bρ 16) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_596 :
    Uρ (44120943545411 / 64000000000000 : ℝ) ≤
      (-(1606732501947162911213 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_596_1 U_596_2 U_596_3 U_596_4 U_596_5 U_596_6 U_596_7 U_596_8 U_596_9 U_596_10
    U_596_11 U_596_12 U_596_13 U_596_14 U_596_15 U_596_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_597_1 :
    Uω (aρ 1) (bρ 1) (276080392119 / 400000000000 : ℝ) ≤
      (-(475205678070643602751 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (106835764696161 / 156250000000000 : ℝ) ≤
      (-(475205678070643602751 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (106835764696161 / 156250000000000 : ℚ))
        (r' := (106835764696161 / 78125000000000 : ℚ))
        (U := (-(475205678070643602751 / 1250000000000000000000 : ℚ)))
        (U' := (391228297304356397249 / 1250000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (276080392119 / 400000000000 : ℚ))
      (s := (427341581013663 / 625000000000000 : ℚ))
      (q := (106835764696161 / 156250000000000 : ℚ))
      (U := (-(475205678070643602751 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_2 :
    Uω (aρ 2) (bρ 2) (276080392119 / 400000000000 : ℝ) ≤
      (-(959165647276513419161 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1703396966211123 / 2500000000000000 : ℝ) ≤
      (-(959165647276513419161 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1703396966211123 / 2500000000000000 : ℚ))
        (r' := (1703396966211123 / 1250000000000000 : ℚ))
        (U := (-(959165647276513419161 / 2500000000000000000000 : ℚ)))
        (U' := (773702303473486580839 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (276080392119 / 400000000000 : ℚ))
      (s := (851679019663623 / 1250000000000000 : ℚ))
      (q := (1703396966211123 / 2500000000000000 : ℚ))
      (U := (-(959165647276513419161 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_3 :
    Uω (aρ 3) (bρ 3) (276080392119 / 400000000000 : ℝ) ≤
      (-(195352236509487228353 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13531601479762003 / 20000000000000000 : ℝ) ≤
      (-(195352236509487228353 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13531601479762003 / 20000000000000000 : ℚ))
        (r' := (13531601479762003 / 10000000000000000 : ℚ))
        (U := (-(195352236509487228353 / 500000000000000000000 : ℚ)))
        (U' := (151221353640512771647 / 500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (276080392119 / 400000000000 : ℚ))
      (s := (6765254013732003 / 10000000000000000 : ℚ))
      (q := (13531601479762003 / 20000000000000000 : ℚ))
      (U := (-(195352236509487228353 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_4 :
    Uω (aρ 4) (bρ 4) (276080392119 / 400000000000 : ℝ) ≤
      (-(4024975332057229824131 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6686479881673441 / 10000000000000000 : ℝ) ≤
      (-(4024975332057229824131 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6686479881673441 / 10000000000000000 : ℚ))
        (r' := (6686479881673441 / 5000000000000000 : ℚ))
        (U := (-(4024975332057229824131 / 10000000000000000000000 : ℚ)))
        (U' := (2906496470942770175869 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (276080392119 / 400000000000 : ℚ))
      (s := (3342453239190941 / 5000000000000000 : ℚ))
      (q := (6686479881673441 / 10000000000000000 : ℚ))
      (U := (-(4024975332057229824131 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_5 :
    Uω (aρ 5) (bρ 5) (276080392119 / 400000000000 : ℝ) ≤
      (-(4207095548052328053339 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (410362983923773 / 625000000000000 : ℝ) ≤
      (-(4207095548052328053339 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (410362983923773 / 625000000000000 : ℚ))
        (r' := (410362983923773 / 312500000000000 : ℚ))
        (U := (-(4207095548052328053339 / 10000000000000000000000 : ℚ)))
        (U' := (2724376254947671946661 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (276080392119 / 400000000000 : ℚ))
      (s := (410109507495671 / 625000000000000 : ℚ))
      (q := (410362983923773 / 625000000000000 : ℚ))
      (U := (-(4207095548052328053339 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_6 :
    Uω (aρ 6) (bρ 6) (276080392119 / 400000000000 : ℝ) ≤
      (-(4473775633260287782671 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (639302485362523 / 1000000000000000 : ℝ) ≤
      (-(4473775633260287782671 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (639302485362523 / 1000000000000000 : ℚ))
        (r' := (639302485362523 / 500000000000000 : ℚ))
        (U := (-(4473775633260287782671 / 10000000000000000000000 : ℚ)))
        (U' := (2457696169739712217329 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (276080392119 / 400000000000 : ℚ))
      (s := (319171335838023 / 500000000000000 : ℚ))
      (q := (639302485362523 / 1000000000000000 : ℚ))
      (U := (-(4473775633260287782671 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_7 :
    Uω (aρ 7) (bρ 7) (276080392119 / 400000000000 : ℝ) ≤
      (-(4848487529947418754959 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1539475815009909 / 2500000000000000 : ℝ) ≤
      (-(4848487529947418754959 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1539475815009909 / 2500000000000000 : ℚ))
        (r' := (1539475815009909 / 1250000000000000 : ℚ))
        (U := (-(4848487529947418754959 / 10000000000000000000000 : ℚ)))
        (U' := (2082984273052581245041 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (276080392119 / 400000000000 : ℚ))
      (s := (767105613793659 / 1250000000000000 : ℚ))
      (q := (1539475815009909 / 2500000000000000 : ℚ))
      (U := (-(4848487529947418754959 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_8 :
    Uω (aρ 8) (bρ 8) (276080392119 / 400000000000 : ℝ) ≤
      (-(214298820193377640081 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2926159644260453 / 5000000000000000 : ℝ) ≤
      (-(214298820193377640081 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2926159644260453 / 5000000000000000 : ℚ))
        (r' := (2926159644260453 / 2500000000000000 : ℚ))
        (U := (-(214298820193377640081 / 400000000000000000000 : ℚ)))
        (U' := (62960051926622359919 / 400000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (276080392119 / 400000000000 : ℚ))
      (s := (1452304654662953 / 2500000000000000 : ℚ))
      (q := (2926159644260453 / 5000000000000000 : ℚ))
      (U := (-(214298820193377640081 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_9 :
    Uω (aρ 9) (bρ 9) (276080392119 / 400000000000 : ℝ) ≤
      (-(6029977007426569530737 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2188675705235189 / 4000000000000000 : ℝ) ≤
      (-(6029977007426569530737 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2188675705235189 / 4000000000000000 : ℚ))
        (r' := (2188675705235189 / 2000000000000000 : ℚ))
        (U := (-(6029977007426569530737 / 10000000000000000000000 : ℚ)))
        (U' := (901494795573430469263 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (276080392119 / 400000000000 : ℚ))
      (s := (1077784839229189 / 2000000000000000 : ℚ))
      (q := (2188675705235189 / 4000000000000000 : ℚ))
      (U := (-(6029977007426569530737 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_10 :
    Uω (aρ 10) (bρ 10) (276080392119 / 400000000000 : ℝ) ≤
      (-(107808191664674528683 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10031797985137643 / 20000000000000000 : ℝ) ≤
      (-(107808191664674528683 / 156250000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10031797985137643 / 20000000000000000 : ℚ))
        (r' := (10031797985137643 / 10000000000000000 : ℚ))
        (U := (-(107808191664674528683 / 156250000000000000000 : ℚ)))
        (U' := (496055257200471317 / 156250000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (276080392119 / 400000000000 : ℚ))
      (s := (4865902688602643 / 10000000000000000 : ℚ))
      (q := (10031797985137643 / 20000000000000000 : ℚ))
      (U := (-(107808191664674528683 / 156250000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_11 :
    Uω (aρ 11) (bρ 11) (276080392119 / 400000000000 : ℝ) ≤
      (-(2002298744056355109751 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8978319937195677 / 20000000000000000 : ℝ) ≤
      (-(2002298744056355109751 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8978319937195677 / 20000000000000000 : ℚ))
        (r' := (8978319937195677 / 5000000000000000 : ℚ))
        (U := (-(2002298744056355109751 / 2500000000000000000000 : ℚ)))
        (U' := (1463437157443644890249 / 2500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (276080392119 / 400000000000 : ℚ))
      (s := (4230901266865677 / 10000000000000000 : ℚ))
      (q := (8978319937195677 / 20000000000000000 : ℚ))
      (U := (-(2002298744056355109751 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_12 :
    Uω (aρ 12) (bρ 12) (276080392119 / 400000000000 : ℝ) ≤
      (-(4711052134525300289301 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3897653344772773 / 10000000000000000 : ℝ) ≤
      (-(4711052134525300289301 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3897653344772773 / 10000000000000000 : ℚ))
        (r' := (3897653344772773 / 2500000000000000 : ℚ))
        (U := (-(4711052134525300289301 / 5000000000000000000000 : ℚ)))
        (U' := (2220419668474699710699 / 5000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (276080392119 / 400000000000 : ℚ))
      (s := (1735794057950273 / 5000000000000000 : ℚ))
      (q := (3897653344772773 / 10000000000000000 : ℚ))
      (U := (-(4711052134525300289301 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_13 :
    Uω (aρ 13) (bρ 13) (276080392119 / 400000000000 : ℝ) ≤
      (-(1408478791481375428463 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6481482336582191 / 20000000000000000 : ℝ) ≤
      (-(1408478791481375428463 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6481482336582191 / 20000000000000000 : ℚ))
        (r' := (6481482336582191 / 5000000000000000 : ℚ))
        (U := (-(1408478791481375428463 / 1250000000000000000000 : ℚ)))
        (U' := (324389159268624571537 / 1250000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (276080392119 / 400000000000 : ℚ))
      (s := (2557145504532191 / 10000000000000000 : ℚ))
      (q := (6481482336582191 / 20000000000000000 : ℚ))
      (U := (-(1408478791481375428463 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_14 :
    Uω (aρ 14) (bρ 14) (276080392119 / 400000000000 : ℝ) ≤
      (-(7013246972571734108403 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (491888991620867 / 2000000000000000 : ℝ) ≤
      (-(7013246972571734108403 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (491888991620867 / 2000000000000000 : ℚ))
        (r' := (491888991620867 / 250000000000000 : ℚ))
        (U := (-(7013246972571734108403 / 5000000000000000000000 : ℚ)))
        (U' := (3383960731928265891597 / 5000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (276080392119 / 400000000000 : ℚ))
      (s := (133848036920367 / 1000000000000000 : ℚ))
      (q := (491888991620867 / 2000000000000000 : ℚ))
      (U := (-(7013246972571734108403 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_597_15 :
    Uω (aρ 15) (bρ 15) (276080392119 / 400000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_597_16 :
    Uω (aρ 16) (bρ 16) (276080392119 / 400000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_597 :
    Uρ (276080392119 / 400000000000 : ℝ) ≤
      (-(6410514213786317389521 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_597_1 U_597_2 U_597_3 U_597_4 U_597_5 U_597_6 U_597_7 U_597_8 U_597_9 U_597_10
    U_597_11 U_597_12 U_597_13 U_597_14 U_597_15 U_597_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_598_1 :
    Uω (aρ 1) (bρ 1) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(3789787864895543404819 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54764810740629053 / 80000000000000000 : ℝ) ≤
      (-(3789787864895543404819 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54764810740629053 / 80000000000000000 : ℚ))
        (r' := (54764810740629053 / 40000000000000000 : ℚ))
        (U := (-(3789787864895543404819 / 10000000000000000000000 : ℚ)))
        (U' := (3141683938104456595181 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (1711394431565683 / 2500000000000000 : ℚ))
      (q := (54764810740629053 / 80000000000000000 : ℚ))
      (U := (-(3789787864895543404819 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_2 :
    Uω (aρ 2) (bρ 2) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(3824763229207356151267 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10914720678433329 / 16000000000000000 : ℝ) ≤
      (-(3824763229207356151267 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10914720678433329 / 16000000000000000 : ℚ))
        (r' := (10914720678433329 / 8000000000000000 : ℚ))
        (U := (-(3824763229207356151267 / 10000000000000000000000 : ℚ)))
        (U' := (3106708573792643848733 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (682154490165713 / 1000000000000000 : ℚ))
      (q := (10914720678433329 / 16000000000000000 : ℚ))
      (U := (-(3824763229207356151267 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_3 :
    Uω (aρ 3) (bρ 3) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(3895060681667598397467 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54191310149538897 / 80000000000000000 : ℝ) ≤
      (-(3895060681667598397467 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54191310149538897 / 80000000000000000 : ℚ))
        (r' := (54191310149538897 / 40000000000000000 : ℚ))
        (U := (-(3895060681667598397467 / 10000000000000000000000 : ℚ)))
        (U' := (3036411121332401602533 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (6773367697350193 / 10000000000000000 : ℚ))
      (q := (54191310149538897 / 80000000000000000 : ℚ))
      (U := (-(3895060681667598397467 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_4 :
    Uω (aρ 4) (bρ 4) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(250802958368932343957 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53556753301956121 / 80000000000000000 : ℝ) ≤
      (-(250802958368932343957 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53556753301956121 / 80000000000000000 : ℚ))
        (r' := (53556753301956121 / 40000000000000000 : ℚ))
        (U := (-(250802958368932343957 / 625000000000000000000 : ℚ)))
        (U' := (182414029318567656043 / 625000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (6693022666519499 / 10000000000000000 : ℚ))
      (q := (53556753301956121 / 80000000000000000 : ℚ))
      (U := (-(250802958368932343957 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_5 :
    Uω (aρ 5) (bρ 5) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(2097370035909306309519 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (52591400996845877 / 80000000000000000 : ℝ) ≤
      (-(2097370035909306309519 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (52591400996845877 / 80000000000000000 : ℚ))
        (r' := (52591400996845877 / 40000000000000000 : ℚ))
        (U := (-(2097370035909306309519 / 5000000000000000000000 : ℚ)))
        (U' := (1368365865590693690481 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (3284937254788469 / 5000000000000000 : ℚ))
      (q := (52591400996845877 / 80000000000000000 : ℚ))
      (U := (-(2097370035909306309519 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_6 :
    Uω (aρ 6) (bρ 6) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(4461075231951651050771 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (51209195279289041 / 80000000000000000 : ℝ) ≤
      (-(4461075231951651050771 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (51209195279289041 / 80000000000000000 : ℚ))
        (r' := (51209195279289041 / 40000000000000000 : ℚ))
        (U := (-(4461075231951651050771 / 10000000000000000000000 : ℚ)))
        (U' := (2470396571048348949229 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (6391563455327729 / 10000000000000000 : ℚ))
      (q := (51209195279289041 / 80000000000000000 : ℚ))
      (U := (-(4461075231951651050771 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_7 :
    Uω (aρ 7) (bρ 7) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(967055438211356976147 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (49328347475768481 / 80000000000000000 : ℝ) ≤
      (-(967055438211356976147 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (49328347475768481 / 80000000000000000 : ℚ))
        (r' := (49328347475768481 / 40000000000000000 : ℚ))
        (U := (-(967055438211356976147 / 2000000000000000000000 : ℚ)))
        (U' := (419238922388643023853 / 2000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (6145012885207589 / 10000000000000000 : ℚ))
      (q := (49328347475768481 / 80000000000000000 : ℚ))
      (U := (-(967055438211356976147 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_8 :
    Uω (aρ 8) (bρ 8) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(534351573455711606301 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46883934132587653 / 80000000000000000 : ℝ) ≤
      (-(534351573455711606301 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (46883934132587653 / 80000000000000000 : ℚ))
        (r' := (46883934132587653 / 40000000000000000 : ℚ))
        (U := (-(534351573455711606301 / 1000000000000000000000 : ℚ)))
        (U' := (158795606844288393699 / 1000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (2908725600376191 / 5000000000000000 : ℚ))
      (q := (46883934132587653 / 80000000000000000 : ℚ))
      (U := (-(534351573455711606301 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_9 :
    Uω (aρ 9) (bρ 9) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(187966715081535804873 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43839408318014213 / 80000000000000000 : ℝ) ≤
      (-(187966715081535804873 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (43839408318014213 / 80000000000000000 : ℚ))
        (r' := (43839408318014213 / 40000000000000000 : ℚ))
        (U := (-(187966715081535804873 / 312500000000000000000 : ℚ)))
        (U' := (28641778762214195127 / 312500000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (2698642687734511 / 5000000000000000 : ℚ))
      (q := (43839408318014213 / 80000000000000000 : ℚ))
      (U := (-(187966715081535804873 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_10 :
    Uω (aρ 10) (bρ 10) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(1720766780932629166881 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8038817615334817 / 16000000000000000 : ℝ) ≤
      (-(1720766780932629166881 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8038817615334817 / 16000000000000000 : ℚ))
        (r' := (8038817615334817 / 8000000000000000 : ℚ))
        (U := (-(1720766780932629166881 / 2500000000000000000000 : ℚ)))
        (U' := (12101169817370833119 / 2500000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (487451434862899 / 1000000000000000 : ℚ))
      (q := (8038817615334817 / 16000000000000000 : ℚ))
      (U := (-(1720766780932629166881 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_11 :
    Uω (aρ 11) (bρ 11) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(7990041466326574167593 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (35982132201957549 / 80000000000000000 : ℝ) ≤
      (-(7990041466326574167593 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (35982132201957549 / 80000000000000000 : ℚ))
        (r' := (35982132201957549 / 20000000000000000 : ℚ))
        (U := (-(7990041466326574167593 / 10000000000000000000000 : ℚ)))
        (U' := (5872902139673425832407 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (530000250769357 / 1250000000000000 : ℚ))
      (q := (35982132201957549 / 80000000000000000 : ℚ))
      (U := (-(7990041466326574167593 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_12 :
    Uω (aρ 12) (bρ 12) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(469938514580832882803 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (31254069915314197 / 80000000000000000 : ℝ) ≤
      (-(469938514580832882803 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (31254069915314197 / 80000000000000000 : ℚ))
        (r' := (31254069915314197 / 20000000000000000 : ℚ))
        (U := (-(469938514580832882803 / 500000000000000000000 : ℚ)))
        (U' := (223208665719167117197 / 500000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (1740843265589509 / 5000000000000000 : ℚ))
      (q := (31254069915314197 / 80000000000000000 : ℚ))
      (U := (-(469938514580832882803 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_13 :
    Uω (aρ 13) (bρ 13) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(11236182902422223580447 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26008108217176697 / 80000000000000000 : ℝ) ≤
      (-(11236182902422223580447 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26008108217176697 / 80000000000000000 : ℚ))
        (r' := (26008108217176697 / 20000000000000000 : ℚ))
        (U := (-(11236182902422223580447 / 10000000000000000000000 : ℚ)))
        (U' := (2626760703577776419553 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (2569577848239643 / 10000000000000000 : ℚ))
      (q := (26008108217176697 / 80000000000000000 : ℚ))
      (U := (-(11236182902422223580447 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_14 :
    Uω (aρ 14) (bρ 14) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(2793273795028130683401 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19794215259049549 / 80000000000000000 : ℝ) ≤
      (-(2793273795028130683401 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19794215259049549 / 80000000000000000 : ℚ))
        (r' := (19794215259049549 / 10000000000000000 : ℚ))
        (U := (-(2793273795028130683401 / 2000000000000000000000 : ℚ)))
        (U' := (1365609286771869316599 / 2000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (44224781932669 / 64000000000000 : ℚ))
      (s := (170003986719107 / 1250000000000000 : ℚ))
      (q := (19794215259049549 / 80000000000000000 : ℚ))
      (U := (-(2793273795028130683401 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_598_15 :
    Uω (aρ 15) (bρ 15) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_598_16 :
    Uω (aρ 16) (bρ 16) (44224781932669 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_598 :
    Uρ (44224781932669 / 64000000000000 : ℝ) ≤
      (-(39963571329679689973 / 62500000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_598_1 U_598_2 U_598_3 U_598_4 U_598_5 U_598_6 U_598_7 U_598_8 U_598_9 U_598_10
    U_598_11 U_598_12 U_598_13 U_598_14 U_598_15 U_598_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_599_1 :
    Uω (aρ 1) (bρ 1) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(944486087211076226443 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27414854978146513 / 40000000000000000 : ℝ) ≤
      (-(944486087211076226443 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27414854978146513 / 40000000000000000 : ℚ))
        (r' := (27414854978146513 / 20000000000000000 : ℚ))
        (U := (-(944486087211076226443 / 2500000000000000000000 : ℚ)))
        (U' := (788381863538923773557 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (3426845078087097 / 5000000000000000 : ℚ))
      (q := (27414854978146513 / 40000000000000000 : ℚ))
      (U := (-(944486087211076226443 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_2 :
    Uω (aρ 2) (bρ 2) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(381287801260218030659 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27319251931029037 / 40000000000000000 : ℝ) ≤
      (-(381287801260218030659 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27319251931029037 / 40000000000000000 : ℚ))
        (r' := (27319251931029037 / 20000000000000000 : ℚ))
        (U := (-(381287801260218030659 / 1000000000000000000000 : ℚ)))
        (U' := (311859379039781969341 / 1000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (426853602820341 / 625000000000000 : ℚ))
      (q := (27319251931029037 / 40000000000000000 : ℚ))
      (U := (-(381287801260218030659 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_3 :
    Uω (aρ 3) (bρ 3) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(1941545490004321403837 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5425621436749573 / 8000000000000000 : ℝ) ≤
      (-(1941545490004321403837 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5425621436749573 / 8000000000000000 : ℚ))
        (r' := (5425621436749573 / 4000000000000000 : ℚ))
        (U := (-(1941545490004321403837 / 5000000000000000000000 : ℚ)))
        (U' := (1524190411495678596163 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (678148137783487 / 1000000000000000 : ℚ))
      (q := (5425621436749573 / 8000000000000000 : ℚ))
      (U := (-(1941545490004321403837 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_4 :
    Uω (aρ 4) (bρ 4) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(4000734033657501560457 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5362166751357703 / 8000000000000000 : ℝ) ≤
      (-(4000734033657501560457 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5362166751357703 / 8000000000000000 : ℚ))
        (r' := (5362166751357703 / 4000000000000000 : ℚ))
        (U := (-(4000734033657501560457 / 10000000000000000000000 : ℚ)))
        (U' := (2930737769342498439543 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (1340227769084039 / 2000000000000000 : ℚ))
      (q := (5362166751357703 / 8000000000000000 : ℚ))
      (U := (-(4000734033657501560457 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_5 :
    Uω (aρ 5) (bρ 5) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(418239986130542002681 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5265633995257277 / 8000000000000000 : ℝ) ≤
      (-(418239986130542002681 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5265633995257277 / 8000000000000000 : ℚ))
        (r' := (5265633995257277 / 4000000000000000 : ℚ))
        (U := (-(418239986130542002681 / 1000000000000000000000 : ℚ)))
        (U' := (274907194169457997319 / 1000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (657799687450413 / 1000000000000000 : ℚ))
      (q := (5265633995257277 / 8000000000000000 : ℚ))
      (U := (-(418239986130542002681 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_6 :
    Uω (aρ 6) (bρ 6) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(4448390988465003952377 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25637095741062787 / 40000000000000000 : ℝ) ≤
      (-(4448390988465003952377 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25637095741062787 / 40000000000000000 : ℚ))
        (r' := (25637095741062787 / 20000000000000000 : ℚ))
        (U := (-(4448390988465003952377 / 10000000000000000000000 : ℚ)))
        (U' := (2483080814534996047623 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (6399700132032331 / 10000000000000000 : ℚ))
      (q := (25637095741062787 / 40000000000000000 : ℚ))
      (U := (-(4448390988465003952377 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_7 :
    Uω (aρ 7) (bρ 7) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(602760549948094116003 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24696734141387703 / 40000000000000000 : ℝ) ≤
      (-(602760549948094116003 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (24696734141387703 / 40000000000000000 : ℚ))
        (r' := (24696734141387703 / 20000000000000000 : ℚ))
        (U := (-(602760549948094116003 / 1250000000000000000000 : ℚ)))
        (U' := (263673425426905883997 / 1250000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (6153180712954789 / 10000000000000000 : ℚ))
      (q := (24696734141387703 / 40000000000000000 : ℚ))
      (U := (-(602760549948094116003 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_8 :
    Uω (aρ 8) (bρ 8) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(1065916139610143317519 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4694931260795021 / 8000000000000000 : ℝ) ≤
      (-(1065916139610143317519 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4694931260795021 / 8000000000000000 : ℚ))
        (r' := (4694931260795021 / 4000000000000000 : ℚ))
        (U := (-(1065916139610143317519 / 2000000000000000000000 : ℚ)))
        (U' := (320378220989856682481 / 2000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (582568344558849 / 1000000000000000 : ℚ))
      (q := (4694931260795021 / 8000000000000000 : ℚ))
      (U := (-(1065916139610143317519 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_9 :
    Uω (aρ 9) (bρ 9) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(5999916041147995132601 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21952649749208029 / 40000000000000000 : ℝ) ≤
      (-(5999916041147995132601 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21952649749208029 / 40000000000000000 : ℚ))
        (r' := (21952649749208029 / 20000000000000000 : ℚ))
        (U := (-(5999916041147995132601 / 10000000000000000000000 : ℚ)))
        (U' := (931555761852004867399 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (675705724570619 / 1250000000000000 : ℚ))
      (q := (21952649749208029 / 40000000000000000 : ℚ))
      (U := (-(5999916041147995132601 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_10 :
    Uω (aρ 10) (bρ 10) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(6866439379730423357791 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20130488686426481 / 40000000000000000 : ℝ) ≤
      (-(6866439379730423357791 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20130488686426481 / 40000000000000000 : ℚ))
        (r' := (20130488686426481 / 20000000000000000 : ℚ))
        (U := (-(6866439379730423357791 / 10000000000000000000000 : ℚ)))
        (U' := (65032423269576642209 / 10000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (2441562149334589 / 5000000000000000 : ℚ))
      (q := (20130488686426481 / 40000000000000000 : ℚ))
      (U := (-(6866439379730423357791 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_11 :
    Uω (aρ 11) (bρ 11) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(7970929014454339731257 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18025484319827781 / 40000000000000000 : ℝ) ≤
      (-(7970929014454339731257 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18025484319827781 / 40000000000000000 : ℚ))
        (r' := (18025484319827781 / 10000000000000000 : ℚ))
        (U := (-(7970929014454339731257 / 10000000000000000000000 : ℚ)))
        (U' := (5892014591545660268743 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (1062274685393707 / 2500000000000000 : ℚ))
      (q := (18025484319827781 / 40000000000000000 : ℚ))
      (U := (-(7970929014454339731257 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_12 :
    Uω (aρ 12) (bρ 12) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(1875100772085846270361 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15663435820495567 / 40000000000000000 : ℝ) ≤
      (-(1875100772085846270361 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (15663435820495567 / 40000000000000000 : ℚ))
        (r' := (15663435820495567 / 10000000000000000 : ℚ))
        (U := (-(1875100772085846270361 / 2000000000000000000000 : ℚ)))
        (U' := (897487949114153729639 / 2000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (3491774588593721 / 10000000000000000 : ℚ))
      (q := (15663435820495567 / 40000000000000000 : ℚ))
      (U := (-(1875100772085846270361 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_13 :
    Uω (aρ 13) (bρ 13) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(2240937602556298459121 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13045074796685817 / 40000000000000000 : ℝ) ≤
      (-(2240937602556298459121 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13045074796685817 / 40000000000000000 : ℚ))
        (r' := (13045074796685817 / 10000000000000000 : ℚ))
        (U := (-(2240937602556298459121 / 2000000000000000000000 : ℚ)))
        (U' := (531651118643701540879 / 2000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (1290987909141923 / 5000000000000000 : ℚ))
      (q := (13045074796685817 / 40000000000000000 : ℚ))
      (U := (-(2240937602556298459121 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_14 :
    Uω (aρ 14) (bρ 14) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(13907183051807184338793 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1991171652777751 / 8000000000000000 : ℝ) ≤
      (-(13907183051807184338793 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1991171652777751 / 8000000000000000 : ℚ))
        (r' := (1991171652777751 / 1000000000000000 : ℚ))
        (U := (-(13907183051807184338793 / 10000000000000000000000 : ℚ)))
        (U' := (6887232357192815661207 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (22138350563149 / 32000000000000 : ℚ))
      (s := (276258967386063 / 2000000000000000 : ℚ))
      (q := (1991171652777751 / 8000000000000000 : ℚ))
      (U := (-(13907183051807184338793 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_599_15 :
    Uω (aρ 15) (bρ 15) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_599_16 :
    Uω (aρ 16) (bρ 16) (22138350563149 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_599 :
    Uρ (22138350563149 / 32000000000000 : ℝ) ≤
      (-(6377899458709971549779 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_599_1 U_599_2 U_599_3 U_599_4 U_599_5 U_599_6 U_599_7 U_599_8 U_599_9 U_599_10
    U_599_11 U_599_12 U_599_13 U_599_14 U_599_15 U_599_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_600_1 :
    Uω (aρ 1) (bρ 1) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(3766114843185157129627 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54894609171428223 / 80000000000000000 : ℝ) ≤
      (-(3766114843185157129627 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54894609171428223 / 80000000000000000 : ℚ))
        (r' := (54894609171428223 / 40000000000000000 : ℚ))
        (U := (-(3766114843185157129627 / 10000000000000000000000 : ℚ)))
        (U' := (3165356959814842870373 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (3430901292976731 / 5000000000000000 : ℚ))
      (q := (54894609171428223 / 80000000000000000 : ℚ))
      (U := (-(3766114843185157129627 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_2 :
    Uω (aρ 2) (bρ 2) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(19005034528540760341 / 50000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54703404328442747 / 80000000000000000 : ℝ) ≤
      (-(19005034528540760341 / 50000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54703404328442747 / 80000000000000000 : ℚ))
        (r' := (54703404328442747 / 40000000000000000 : ℚ))
        (U := (-(19005034528540760341 / 50000000000000000000 : ℚ)))
        (U' := (15652324486459239659 / 50000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (6837770387717093 / 10000000000000000 : ℚ))
      (q := (54703404328442747 / 80000000000000000 : ℚ))
      (U := (-(19005034528540760341 / 50000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_3 :
    Uω (aρ 3) (bρ 3) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(38711355908973622577 / 100000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54321118572963439 / 80000000000000000 : ℝ) ≤
      (-(38711355908973622577 / 100000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54321118572963439 / 80000000000000000 : ℚ))
        (r' := (54321118572963439 / 40000000000000000 : ℚ))
        (U := (-(38711355908973622577 / 100000000000000000000 : ℚ)))
        (U' := (30603362121026377423 / 100000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (3394797527598633 / 5000000000000000 : ℚ))
      (q := (54321118572963439 / 80000000000000000 : ℚ))
      (U := (-(38711355908973622577 / 100000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_4 :
    Uω (aρ 4) (bρ 4) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(3988635395722701368637 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10737316337676867 / 16000000000000000 : ℝ) ≤
      (-(3988635395722701368637 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10737316337676867 / 16000000000000000 : ℚ))
        (r' := (10737316337676867 / 8000000000000000 : ℚ))
        (U := (-(3988635395722701368637 / 10000000000000000000000 : ℚ)))
        (U' := (2942836407277298631363 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (670925501511749 / 1000000000000000 : ℚ))
      (q := (10737316337676867 / 16000000000000000 : ℚ))
      (U := (-(3988635395722701368637 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_5 :
    Uω (aρ 5) (bρ 5) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(834014975758038440671 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10544255761957887 / 16000000000000000 : ℝ) ≤
      (-(834014975758038440671 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10544255761957887 / 16000000000000000 : ℚ))
        (r' := (10544255761957887 / 8000000000000000 : ℚ))
        (U := (-(834014975758038440671 / 2000000000000000000000 : ℚ)))
        (U' := (552279384841961559329 / 2000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (1317223842960753 / 2000000000000000 : ℚ))
      (q := (10544255761957887 / 16000000000000000 : ℚ))
      (U := (-(834014975758038440671 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_6 :
    Uω (aρ 6) (bρ 6) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(887144572323505302381 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (51339187438454079 / 80000000000000000 : ℝ) ≤
      (-(887144572323505302381 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (51339187438454079 / 80000000000000000 : ℚ))
        (r' := (51339187438454079 / 40000000000000000 : ℚ))
        (U := (-(887144572323505302381 / 2000000000000000000000 : ℚ)))
        (U' := (499149788276494697619 / 2000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (3203918373554963 / 5000000000000000 : ℚ))
      (q := (51339187438454079 / 80000000000000000 : ℚ))
      (U := (-(887144572323505302381 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_7 :
    Uω (aρ 7) (bρ 7) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(4808909108662188216689 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (49458588503678087 / 80000000000000000 : ℝ) ≤
      (-(4808909108662188216689 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (49458588503678087 / 80000000000000000 : ℚ))
        (r' := (49458588503678087 / 40000000000000000 : ℚ))
        (U := (-(4808909108662188216689 / 10000000000000000000000 : ℚ)))
        (U' := (2122562694337811783311 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (770168549271991 / 1250000000000000 : ℚ))
      (q := (49458588503678087 / 80000000000000000 : ℚ))
      (U := (-(4808909108662188216689 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_8 :
    Uω (aρ 8) (bρ 8) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(5315665338778738707151 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47014689739965883 / 80000000000000000 : ℝ) ≤
      (-(5315665338778738707151 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47014689739965883 / 80000000000000000 : ℚ))
        (r' := (47014689739965883 / 40000000000000000 : ℚ))
        (U := (-(5315665338778738707151 / 10000000000000000000000 : ℚ)))
        (U' := (1615806464221261292849 / 10000000000000000000000 : ℚ))
        1 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (5833915354587877 / 10000000000000000 : ℚ))
      (q := (47014689739965883 / 80000000000000000 : ℚ))
      (U := (-(5315665338778738707151 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_9 :
    Uω (aρ 9) (bρ 9) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(598492040897808695309 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8794237531991951 / 16000000000000000 : ℝ) ≤
      (-(598492040897808695309 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8794237531991951 / 16000000000000000 : ℚ))
        (r' := (8794237531991951 / 8000000000000000 : ℚ))
        (U := (-(598492040897808695309 / 1000000000000000000000 : ℚ)))
        (U' := (94655139402191304691 / 1000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (1082801092589269 / 2000000000000000 : ℚ))
      (q := (8794237531991951 / 16000000000000000 : ℚ))
      (U := (-(598492040897808695309 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_10 :
    Uω (aρ 10) (bρ 10) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(6849840925155560255049 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40327859865204219 / 80000000000000000 : ℝ) ≤
      (-(6849840925155560255049 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (40327859865204219 / 80000000000000000 : ℚ))
        (r' := (40327859865204219 / 40000000000000000 : ℚ))
        (U := (-(6849840925155560255049 / 10000000000000000000000 : ℚ)))
        (U' := (81630877844439744951 / 10000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (4891732547752461 / 10000000000000000 : ℚ))
      (q := (40327859865204219 / 80000000000000000 : ℚ))
      (U := (-(6849840925155560255049 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_11 :
    Uω (aρ 11) (bρ 11) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(3975928713532320038747 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36119789164517907 / 80000000000000000 : ℝ) ≤
      (-(3975928713532320038747 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (36119789164517907 / 80000000000000000 : ℚ))
        (r' := (36119789164517907 / 20000000000000000 : ℚ))
        (U := (-(3975928713532320038747 / 5000000000000000000000 : ℚ)))
        (U' := (2955543089467679961253 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (4258191498785883 / 10000000000000000 : ℚ))
      (q := (36119789164517907 / 80000000000000000 : ℚ))
      (U := (-(3975928713532320038747 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_12 :
    Uω (aρ 12) (bρ 12) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(9352304517135290160901 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (31399632293277399 / 80000000000000000 : ℝ) ≤
      (-(9352304517135290160901 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (31399632293277399 / 80000000000000000 : ℚ))
        (r' := (31399632293277399 / 20000000000000000 : ℚ))
        (U := (-(9352304517135290160901 / 10000000000000000000000 : ℚ)))
        (U' := (4510639088864709839099 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (875463094415189 / 2500000000000000 : ℚ))
      (q := (31399632293277399 / 80000000000000000 : ℚ))
      (U := (-(9352304517135290160901 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_13 :
    Uω (aρ 13) (bρ 13) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(5586671893103846167657 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26172055446114123 / 80000000000000000 : ℝ) ≤
      (-(5586671893103846167657 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26172055446114123 / 80000000000000000 : ℚ))
        (r' := (26172055446114123 / 20000000000000000 : ℚ))
        (U := (-(5586671893103846167657 / 5000000000000000000000 : ℚ)))
        (U' := (1344799909896153832343 / 5000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (2594339907464937 / 10000000000000000 : ℚ))
      (q := (26172055446114123 / 80000000000000000 : ℚ))
      (U := (-(5586671893103846167657 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_14 :
    Uω (aρ 14) (bρ 14) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(2769779097549425911313 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4005623196142587 / 16000000000000000 : ℝ) ≤
      (-(2769779097549425911313 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4005623196142587 / 16000000000000000 : ℚ))
        (r' := (4005623196142587 / 4000000000000000 : ℚ))
        (U := (-(2769779097549425911313 / 2000000000000000000000 : ℚ)))
        (U' := (2809623650574088687 / 2000000000000000000000 : ℚ))
        2 2 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (44328620319927 / 64000000000000 : ℚ))
      (s := (35057058153991 / 250000000000000 : ℚ))
      (q := (4005623196142587 / 16000000000000000 : ℚ))
      (U := (-(2769779097549425911313 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_600_15 :
    Uω (aρ 15) (bρ 15) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_600_16 :
    Uω (aρ 16) (bρ 16) (44328620319927 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_600 :
    Uρ (44328620319927 / 64000000000000 : ℝ) ≤
      (-(3180848175369736682521 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_600_1 U_600_2 U_600_3 U_600_4 U_600_5 U_600_6 U_600_7 U_600_8 U_600_9 U_600_10
    U_600_11 U_600_12 U_600_13 U_600_14 U_600_15 U_600_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_601_1 :
    Uω (aρ 1) (bρ 1) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(938574828702399587789 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3434969274127283 / 5000000000000000 : ℝ) ≤
      (-(938574828702399587789 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3434969274127283 / 5000000000000000 : ℚ))
        (r' := (3434969274127283 / 2500000000000000 : ℚ))
        (U := (-(938574828702399587789 / 2500000000000000000000 : ℚ)))
        (U' := (794293122047600412211 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (6869915015601007 / 10000000000000000 : ℚ))
      (q := (3434969274127283 / 5000000000000000 : ℚ))
      (U := (-(938574828702399587789 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_2 :
    Uω (aρ 2) (bρ 2) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(757829975012473701853 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3423019049458321 / 5000000000000000 : ℝ) ≤
      (-(757829975012473701853 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3423019049458321 / 5000000000000000 : ℚ))
        (r' := (3423019049458321 / 2500000000000000 : ℚ))
        (U := (-(757829975012473701853 / 2000000000000000000000 : ℚ)))
        (U' := (628464385587526298147 / 2000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (6845883129435159 / 10000000000000000 : ℚ))
      (q := (3423019049458321 / 5000000000000000 : ℚ))
      (U := (-(757829975012473701853 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_3 :
    Uω (aρ 3) (bρ 3) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(964798620035307040553 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13596505691496687 / 20000000000000000 : ℝ) ≤
      (-(964798620035307040553 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13596505691496687 / 20000000000000000 : ℚ))
        (r' := (13596505691496687 / 10000000000000000 : ℚ))
        (U := (-(964798620035307040553 / 2500000000000000000000 : ℚ)))
        (U' := (768069330714692959447 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (3398854364724281 / 5000000000000000 : ℚ))
      (q := (13596505691496687 / 20000000000000000 : ℚ))
      (U := (-(964798620035307040553 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_4 :
    Uω (aρ 4) (bρ 4) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(994137846157366722441 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13437873956627869 / 20000000000000000 : ℝ) ≤
      (-(994137846157366722441 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13437873956627869 / 20000000000000000 : ℚ))
        (r' := (13437873956627869 / 10000000000000000 : ℚ))
        (U := (-(994137846157366722441 / 2500000000000000000000 : ℚ)))
        (U' := (738730104592633277559 / 2500000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (839671396955593 / 1250000000000000 : ℚ))
      (q := (13437873956627869 / 20000000000000000 : ℚ))
      (U := (-(994137846157366722441 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_5 :
    Uω (aρ 5) (bρ 5) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(4157765086690188808493 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13196554392214973 / 20000000000000000 : ℝ) ≤
      (-(4157765086690188808493 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13196554392214973 / 20000000000000000 : ℚ))
        (r' := (13196554392214973 / 10000000000000000 : ℚ))
        (U := (-(4157765086690188808493 / 10000000000000000000000 : ℚ)))
        (U' := (2773706716309811191507 / 10000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (103035023915107 / 156250000000000 : ℚ))
      (q := (13196554392214973 / 20000000000000000 : ℚ))
      (U := (-(4157765086690188808493 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_6 :
    Uω (aρ 6) (bρ 6) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(2211535405192055338863 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12851045787303101 / 20000000000000000 : ℝ) ≤
      (-(2211535405192055338863 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12851045787303101 / 20000000000000000 : ℚ))
        (r' := (12851045787303101 / 10000000000000000 : ℚ))
        (U := (-(2211535405192055338863 / 5000000000000000000000 : ℚ)))
        (U' := (1254200496307944661137 / 5000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (200499165649843 / 312500000000000 : ℚ))
      (q := (12851045787303101 / 20000000000000000 : ℚ))
      (U := (-(2211535405192055338863 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_7 :
    Uω (aρ 7) (bρ 7) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(959150254321744450281 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (309523175880027 / 500000000000000 : ℝ) ≤
      (-(959150254321744450281 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (309523175880027 / 500000000000000 : ℚ))
        (r' := (309523175880027 / 250000000000000 : ℚ))
        (U := (-(959150254321744450281 / 2000000000000000000000 : ℚ)))
        (U' := (427144106278255549719 / 2000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (1233903185890591 / 2000000000000000 : ℚ))
      (q := (309523175880027 / 500000000000000 : ℚ))
      (U := (-(959150254321744450281 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_8 :
    Uω (aρ 8) (bρ 8) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(265088480022531474809 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2942504095894577 / 5000000000000000 : ℝ) ≤
      (-(265088480022531474809 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2942504095894577 / 5000000000000000 : ℚ))
        (r' := (2942504095894577 / 2500000000000000 : ℚ))
        (U := (-(265088480022531474809 / 500000000000000000000 : ℚ)))
        (U' := (81485110127468525191 / 500000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (5842146929170183 / 10000000000000000 : ℚ))
      (q := (2942504095894577 / 5000000000000000 : ℚ))
      (U := (-(265088480022531474809 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_9 :
    Uω (aρ 9) (bρ 9) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(5969947912396625863489 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11009268204151959 / 20000000000000000 : ℝ) ≤
      (-(5969947912396625863489 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11009268204151959 / 20000000000000000 : ℚ))
        (r' := (11009268204151959 / 10000000000000000 : ℚ))
        (U := (-(5969947912396625863489 / 10000000000000000000000 : ℚ)))
        (U' := (961523890603374136511 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (2711182189051917 / 5000000000000000 : ℚ))
      (q := (11009268204151959 / 20000000000000000 : ℚ))
      (U := (-(5969947912396625863489 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_10 :
    Uω (aρ 10) (bρ 10) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(3416635825630334296627 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1262335487174499 / 2500000000000000 : ℝ) ≤
      (-(3416635825630334296627 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1262335487174499 / 2500000000000000 : ℚ))
        (r' := (1262335487174499 / 1250000000000000 : ℚ))
        (U := (-(3416635825630334296627 / 5000000000000000000000 : ℚ)))
        (U' := (49100075869665703373 / 5000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (4900339104842867 / 10000000000000000 : ℚ))
      (q := (1262335487174499 / 2500000000000000 : ℚ))
      (U := (-(3416635825630334296627 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_11 :
    Uω (aρ 11) (bρ 11) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(7932826512081039083167 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9047148469566547 / 20000000000000000 : ℝ) ≤
      (-(7932826512081039083167 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9047148469566547 / 20000000000000000 : ℚ))
        (r' := (9047148469566547 / 5000000000000000 : ℚ))
        (U := (-(7932826512081039083167 / 10000000000000000000000 : ℚ)))
        (U' := (5930117093918960916833 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (2133640151609211 / 5000000000000000 : ℚ))
      (q := (9047148469566547 / 20000000000000000 : ℚ))
      (U := (-(7932826512081039083167 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_12 :
    Uω (aρ 12) (bρ 12) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(9329171808514020960711 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (983511007055157 / 2500000000000000 : ℝ) ≤
      (-(9329171808514020960711 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (983511007055157 / 2500000000000000 : ℚ))
        (r' := (983511007055157 / 625000000000000 : ℚ))
        (U := (-(9329171808514020960711 / 10000000000000000000000 : ℚ)))
        (U' := (4533771797485979039289 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (3511919986778131 / 10000000000000000 : ℚ))
      (q := (983511007055157 / 2500000000000000 : ℚ))
      (U := (-(9329171808514020960711 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_13 :
    Uω (aρ 13) (bρ 13) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(11142148384564178563437 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6563456925967253 / 20000000000000000 : ℝ) ≤
      (-(11142148384564178563437 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6563456925967253 / 20000000000000000 : ℚ))
        (r' := (6563456925967253 / 5000000000000000 : ℚ))
        (U := (-(11142148384564178563437 / 10000000000000000000000 : ℚ)))
        (U' := (2720795221435821436563 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (325833824737391 / 1250000000000000 : ℚ))
      (q := (6563456925967253 / 20000000000000000 : ℚ))
      (U := (-(11142148384564178563437 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_14 :
    Uω (aρ 14) (bρ 14) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(551658738635868358737 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5035865592274749 / 20000000000000000 : ℝ) ≤
      (-(551658738635868358737 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5035865592274749 / 20000000000000000 : ℚ))
        (r' := (5035865592274749 / 5000000000000000 : ℚ))
        (U := (-(551658738635868358737 / 400000000000000000000 : ℚ)))
        (U' := (2859005604131641263 / 400000000000000000000 : ℚ))
        2 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (11095134878389 / 16000000000000 : ℚ))
      (s := (177875818656453 / 1250000000000000 : ℚ))
      (q := (5035865592274749 / 20000000000000000 : ℚ))
      (U := (-(551658738635868358737 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_601_15 :
    Uω (aρ 15) (bρ 15) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_601_16 :
    Uω (aρ 16) (bρ 16) (11095134878389 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_601 :
    Uρ (11095134878389 / 16000000000000 : ℝ) ≤
      (-(6345560218321767044647 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_601_1 U_601_2 U_601_3 U_601_4 U_601_5 U_601_6 U_601_7 U_601_8 U_601_9 U_601_10
    U_601_11 U_601_12 U_601_13 U_601_14 U_601_15 U_601_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_602_1 :
    Uω (aρ 1) (bρ 1) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(233906108170397038313 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (55024407600119797 / 80000000000000000 : ℝ) ≤
      (-(233906108170397038313 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (55024407600119797 / 80000000000000000 : ℚ))
        (r' := (55024407600119797 / 40000000000000000 : ℚ))
        (U := (-(233906108170397038313 / 625000000000000000000 : ℚ)))
        (U' := (199310879517102961687 / 625000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (6878027445117293 / 10000000000000000 : ℚ))
      (q := (55024407600119797 / 80000000000000000 : ℚ))
      (U := (-(233906108170397038313 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_2 :
    Uω (aρ 2) (bρ 2) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(944326721830208510903 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54833205250741649 / 80000000000000000 : ℝ) ≤
      (-(944326721830208510903 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54833205250741649 / 80000000000000000 : ℚ))
        (r' := (54833205250741649 / 40000000000000000 : ℚ))
        (U := (-(944326721830208510903 / 2500000000000000000000 : ℚ)))
        (U' := (788541228919791489097 / 2500000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (1713498967570689 / 2500000000000000 : ℚ))
      (q := (54833205250741649 / 80000000000000000 : ℚ))
      (U := (-(944326721830208510903 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_3 :
    Uω (aρ 3) (bρ 3) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(384726761367011421543 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10890185389322033 / 16000000000000000 : ℝ) ≤
      (-(384726761367011421543 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10890185389322033 / 16000000000000000 : ℚ))
        (r' := (10890185389322033 / 8000000000000000 : ℚ))
        (U := (-(384726761367011421543 / 1000000000000000000000 : ℚ)))
        (U' := (308420418932988578457 / 1000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (1361164480119977 / 2000000000000000 : ℚ))
      (q := (10890185389322033 / 16000000000000000 : ℚ))
      (U := (-(384726761367011421543 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_4 :
    Uω (aρ 4) (bρ 4) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(792896393007470868719 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53816409928091253 / 80000000000000000 : ℝ) ≤
      (-(792896393007470868719 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (53816409928091253 / 80000000000000000 : ℚ))
        (r' := (53816409928091253 / 40000000000000000 : ℚ))
        (U := (-(792896393007470868719 / 2000000000000000000000 : ℚ)))
        (U' := (593397967592529131281 / 2000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (6725487327035157 / 10000000000000000 : ℚ))
      (q := (53816409928091253 / 80000000000000000 : ℚ))
      (U := (-(792896393007470868719 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_5 :
    Uω (aρ 5) (bρ 5) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(165818817902471995431 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (52851156230146361 / 80000000000000000 : ℝ) ≤
      (-(165818817902471995431 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (52851156230146361 / 80000000000000000 : ℚ))
        (r' := (52851156230146361 / 40000000000000000 : ℚ))
        (U := (-(165818817902471995431 / 400000000000000000000 : ℚ)))
        (U' := (111440054217528004569 / 400000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (3301181910941967 / 5000000000000000 : ℚ))
      (q := (52851156230146361 / 80000000000000000 : ℚ))
      (U := (-(165818817902471995431 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_6 :
    Uω (aρ 6) (bρ 6) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(88208695877931068533 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (51469178615333637 / 80000000000000000 : ℝ) ≤
      (-(88208695877931068533 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (51469178615333637 / 80000000000000000 : ℚ))
        (r' := (51469178615333637 / 40000000000000000 : ℚ))
        (U := (-(88208695877931068533 / 200000000000000000000 : ℚ)))
        (U' := (50420740182068931467 / 200000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (6424109793320753 / 10000000000000000 : ℚ))
      (q := (51469178615333637 / 80000000000000000 : ℚ))
      (U := (-(88208695877931068533 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_7 :
    Uω (aρ 7) (bρ 7) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(478261084193173771567 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (49588827196469537 / 80000000000000000 : ℝ) ≤
      (-(478261084193173771567 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (49588827196469537 / 80000000000000000 : ℚ))
        (r' := (49588827196469537 / 40000000000000000 : ℚ))
        (U := (-(478261084193173771567 / 1000000000000000000000 : ℚ)))
        (U' := (214886096106826228433 / 1000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (772210414920591 / 1250000000000000 : ℚ))
      (q := (49588827196469537 / 80000000000000000 : ℚ))
      (U := (-(478261084193173771567 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_8 :
    Uω (aρ 8) (bρ 8) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(5287893427020350660491 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47145439996638613 / 80000000000000000 : ℝ) ≤
      (-(5287893427020350660491 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47145439996638613 / 80000000000000000 : ℚ))
        (r' := (47145439996638613 / 40000000000000000 : ℚ))
        (U := (-(5287893427020350660491 / 10000000000000000000000 : ℚ)))
        (U' := (1643578375979649339509 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (5850378170746997 / 10000000000000000 : ℚ))
      (q := (47145439996638613 / 80000000000000000 : ℚ))
      (U := (-(5287893427020350660491 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_9 :
    Uω (aρ 9) (bρ 9) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(5954998478060639171699 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (44102954982235617 / 80000000000000000 : ℝ) ≤
      (-(5954998478060639171699 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (44102954982235617 / 80000000000000000 : ℚ))
        (r' := (44102954982235617 / 40000000000000000 : ℚ))
        (U := (-(5954998478060639171699 / 10000000000000000000000 : ℚ)))
        (U' := (976473324939360828301 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (678840318188281 / 1250000000000000 : ℚ))
      (q := (44102954982235617 / 80000000000000000 : ℚ))
      (U := (-(5954998478060639171699 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_10 :
    Uω (aρ 10) (bρ 10) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(6816731449933417676493 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8092320916317969 / 16000000000000000 : ℝ) ≤
      (-(6816731449933417676493 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8092320916317969 / 16000000000000000 : ℚ))
        (r' := (8092320916317969 / 8000000000000000 : ℚ))
        (U := (-(6816731449933417676493 / 10000000000000000000000 : ℚ)))
        (U' := (114740353066582323507 / 10000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (981788795767961 / 2000000000000000 : ℚ))
      (q := (8092320916317969 / 16000000000000000 : ℚ))
      (U := (-(6816731449933417676493 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_11 :
    Uω (aρ 11) (bρ 11) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(3956918039439585658247 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36257382881713221 / 80000000000000000 : ℝ) ≤
      (-(3956918039439585658247 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (36257382881713221 / 80000000000000000 : ℚ))
        (r' := (36257382881713221 / 20000000000000000 : ℚ))
        (U := (-(3956918039439585658247 / 5000000000000000000000 : ℚ)))
        (U' := (2974553763560414341753 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (4276365180075649 / 10000000000000000 : ℚ))
      (q := (36257382881713221 / 80000000000000000 : ℚ))
      (U := (-(3956918039439585658247 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_12 :
    Uω (aρ 12) (bρ 12) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(9306105286396064384171 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (31545031787647909 / 80000000000000000 : ℝ) ≤
      (-(9306105286396064384171 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (31545031787647909 / 80000000000000000 : ℚ))
        (r' := (31545031787647909 / 20000000000000000 : ℚ))
        (U := (-(9306105286396064384171 / 10000000000000000000000 : ℚ)))
        (U' := (4556838319603935615829 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (3521977503244321 / 10000000000000000 : ℚ))
      (q := (31545031787647909 / 80000000000000000 : ℚ))
      (U := (-(9306105286396064384171 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_13 :
    Uω (aρ 13) (bρ 13) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(5555550003594789216321 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5267093650724393 / 16000000000000000 : ℝ) ≤
      (-(5555550003594789216321 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5267093650724393 / 16000000000000000 : ℚ))
        (r' := (5267093650724393 / 4000000000000000 : ℚ))
        (U := (-(5555550003594789216321 / 5000000000000000000000 : ℚ)))
        (U' := (1375921799405210783679 / 5000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (523793672266567 / 2000000000000000 : ℚ))
      (q := (5267093650724393 / 16000000000000000 : ℚ))
      (U := (-(5555550003594789216321 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_14 :
    Uω (aρ 14) (bρ 14) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(6867433388723770022023 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20257801050088877 / 80000000000000000 : ℝ) ≤
      (-(6867433388723770022023 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20257801050088877 / 80000000000000000 : ℚ))
        (r' := (20257801050088877 / 20000000000000000 : ℚ))
        (U := (-(6867433388723770022023 / 5000000000000000000000 : ℚ)))
        (U' := (64038414276229977977 / 5000000000000000000000 : ℚ))
        2 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (8886491741437 / 12800000000000 : ℚ))
      (s := (1443478845494563 / 10000000000000000 : ℚ))
      (q := (20257801050088877 / 80000000000000000 : ℚ))
      (U := (-(6867433388723770022023 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_602_15 :
    Uω (aρ 15) (bρ 15) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_602_16 :
    Uω (aρ 16) (bρ 16) (8886491741437 / 12800000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_602 :
    Uρ (8886491741437 / 12800000000000 : ℝ) ≤
      (-(6329489309641351499701 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_602_1 U_602_2 U_602_3 U_602_4 U_602_5 U_602_6 U_602_7 U_602_8 U_602_9 U_602_10
    U_602_11 U_602_12 U_602_13 U_602_14 U_602_15 U_602_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_603_1 :
    Uω (aρ 1) (bρ 1) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(3730710058060810453223 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27544653406839947 / 40000000000000000 : ℝ) ≤
      (-(3730710058060810453223 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27544653406839947 / 40000000000000000 : ℚ))
        (r' := (27544653406839947 / 20000000000000000 : ℚ))
        (U := (-(3730710058060810453223 / 10000000000000000000000 : ℚ)))
        (U' := (3200761744939189546777 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (3443069937251393 / 5000000000000000 : ℚ))
      (q := (27544653406839947 / 40000000000000000 : ℚ))
      (U := (-(3730710058060810453223 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_2 :
    Uω (aρ 2) (bρ 2) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(3765477909257897765203 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5489810570668063 / 8000000000000000 : ℝ) ≤
      (-(3765477909257897765203 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5489810570668063 / 8000000000000000 : ℚ))
        (r' := (5489810570668063 / 4000000000000000 : ℚ))
        (U := (-(3765477909257897765203 / 10000000000000000000000 : ℚ)))
        (U' := (3165993893742102234797 / 10000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (686210861026297 / 1000000000000000 : ℚ))
      (q := (5489810570668063 / 8000000000000000 : ℚ))
      (U := (-(3765477909257897765203 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_3 :
    Uω (aρ 3) (bρ 3) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(1917677478767856130919 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27257915557438993 / 40000000000000000 : ℝ) ≤
      (-(1917677478767856130919 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27257915557438993 / 40000000000000000 : ℚ))
        (r' := (27257915557438993 / 20000000000000000 : ℚ))
        (U := (-(1917677478767856130919 / 5000000000000000000000 : ℚ)))
        (U' := (1548058422732143869081 / 5000000000000000000000 : ℚ))
        1 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (6813936068662309 / 10000000000000000 : ℚ))
      (q := (27257915557438993 / 40000000000000000 : ℚ))
      (U := (-(1917677478767856130919 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_4 :
    Uω (aρ 4) (bρ 4) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(4940533877167384837 / 12500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26940661996627907 / 40000000000000000 : ℝ) ≤
      (-(4940533877167384837 / 12500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26940661996627907 / 40000000000000000 : ℚ))
        (r' := (26940661996627907 / 20000000000000000 : ℚ))
        (U := (-(4940533877167384837 / 12500000000000000000 : ℚ)))
        (U' := (3723805876582615163 / 12500000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (3366801734660883 / 5000000000000000 : ℚ))
      (q := (26940661996627907 / 40000000000000000 : ℚ))
      (U := (-(4940533877167384837 / 12500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_5 :
    Uω (aρ 5) (bρ 5) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(413319092409985669183 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26458047397004643 / 40000000000000000 : ℝ) ≤
      (-(413319092409985669183 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26458047397004643 / 40000000000000000 : ℚ))
        (r' := (26458047397004643 / 20000000000000000 : ℚ))
        (U := (-(413319092409985669183 / 1000000000000000000000 : ℚ)))
        (U' := (279828087890014330817 / 1000000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (3305243044422567 / 5000000000000000 : ℚ))
      (q := (26458047397004643 / 40000000000000000 : ℚ))
      (U := (-(413319092409985669183 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_6 :
    Uω (aρ 6) (bρ 6) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(87956295428855053233 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1030683476754923 / 1600000000000000 : ℝ) ≤
      (-(87956295428855053233 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1030683476754923 / 1600000000000000 : ℚ))
        (r' := (1030683476754923 / 800000000000000 : ℚ))
        (U := (-(87956295428855053233 / 200000000000000000000 : ℚ)))
        (U' := (50673140631144946767 / 200000000000000000000 : ℚ))
        1 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (128644924498387 / 200000000000000 : ℚ))
      (q := (1030683476754923 / 1600000000000000 : ℚ))
      (U := (-(87956295428855053233 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_7 :
    Uω (aρ 7) (bρ 7) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(4769487773325352152819 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4965394567297691 / 8000000000000000 : ℝ) ≤
      (-(4769487773325352152819 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4965394567297691 / 8000000000000000 : ℚ))
        (r' := (4965394567297691 / 4000000000000000 : ℚ))
        (U := (-(4769487773325352152819 / 10000000000000000000000 : ℚ)))
        (U' := (2161984029674647847181 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (9665391507011 / 15625000000000 : ℚ))
      (q := (4965394567297691 / 8000000000000000 : ℚ))
      (U := (-(4769487773325352152819 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_8 :
    Uω (aρ 8) (bρ 8) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(5274036762684941512903 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4721081313255643 / 8000000000000000 : ℝ) ≤
      (-(5274036762684941512903 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4721081313255643 / 8000000000000000 : ℚ))
        (r' := (4721081313255643 / 4000000000000000 : ℚ))
        (U := (-(5274036762684941512903 / 10000000000000000000000 : ℚ)))
        (U' := (1657435040315058487097 / 10000000000000000000000 : ℚ))
        1 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (2288519172157 / 3906250000000 : ℚ))
      (q := (4721081313255643 / 8000000000000000 : ℚ))
      (U := (-(5274036762684941512903 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_9 :
    Uω (aρ 9) (bρ 9) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(5940072032984582198809 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22084417085315947 / 40000000000000000 : ℝ) ≤
      (-(5940072032984582198809 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (22084417085315947 / 40000000000000000 : ℚ))
        (r' := (22084417085315947 / 20000000000000000 : ℚ))
        (U := (-(5940072032984582198809 / 10000000000000000000000 : ℚ)))
        (U' := (991399770015417801191 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (2719539984300393 / 5000000000000000 : ℚ))
      (q := (22084417085315947 / 40000000000000000 : ℚ))
      (U := (-(5940072032984582198809 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_10 :
    Uω (aρ 10) (bρ 10) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(6800220213689320315221 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4052846687656339 / 8000000000000000 : ℝ) ≤
      (-(6800220213689320315221 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4052846687656339 / 8000000000000000 : ℚ))
        (r' := (4052846687656339 / 4000000000000000 : ℚ))
        (U := (-(6800220213689320315221 / 10000000000000000000000 : ℚ)))
        (U' := (131251589310679684779 / 10000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (245877358928933 / 500000000000000 : ℚ))
      (q := (4052846687656339 / 8000000000000000 : ℚ))
      (U := (-(6800220213689320315221 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_11 :
    Uω (aρ 11) (bρ 11) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(3947442969135704496559 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18163078137386779 / 40000000000000000 : ℝ) ≤
      (-(3947442969135704496559 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18163078137386779 / 40000000000000000 : ℚ))
        (r' := (18163078137386779 / 10000000000000000 : ℚ))
        (U := (-(3947442969135704496559 / 5000000000000000000000 : ℚ)))
        (U' := (2984028833864295503441 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (2142723077168101 / 5000000000000000 : ℚ))
      (q := (18163078137386779 / 40000000000000000 : ℚ))
      (U := (-(3947442969135704496559 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_12 :
    Uω (aρ 12) (bρ 12) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(9283104507584379732129 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15808835661897267 / 40000000000000000 : ℝ) ≤
      (-(9283104507584379732129 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (15808835661897267 / 40000000000000000 : ℚ))
        (r' := (15808835661897267 / 10000000000000000 : ℚ))
        (U := (-(9283104507584379732129 / 10000000000000000000000 : ℚ)))
        (U' := (4579839098415620267871 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (1766012506638223 / 5000000000000000 : ℚ))
      (q := (15808835661897267 / 40000000000000000 : ℚ))
      (U := (-(9283104507584379732129 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_13 :
    Uω (aρ 13) (bρ 13) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(11080196889829367210413 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13208489471044621 / 40000000000000000 : ℝ) ≤
      (-(11080196889829367210413 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13208489471044621 / 40000000000000000 : ℚ))
        (r' := (13208489471044621 / 10000000000000000 : ℚ))
        (U := (-(11080196889829367210413 / 10000000000000000000000 : ℚ)))
        (U' := (2782746716170632789587 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 13) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (2631233659445123 / 10000000000000000 : ℚ))
      (q := (13208489471044621 / 40000000000000000 : ℚ))
      (U := (-(11080196889829367210413 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_14 :
    Uω (aρ 14) (bρ 14) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(341976439182884107769 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10185587153490103 / 40000000000000000 : ℝ) ≤
      (-(341976439182884107769 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10185587153490103 / 40000000000000000 : ℚ))
        (r' := (10185587153490103 / 10000000000000000 : ℚ))
        (U := (-(341976439182884107769 / 250000000000000000000 : ℚ)))
        (U' := (4597150967115892231 / 250000000000000000000 : ℚ))
        2 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 14) (t := (22242188950407 / 32000000000000 : ℚ))
      (s := (45740930803527 / 312500000000000 : ℚ))
      (q := (10185587153490103 / 40000000000000000 : ℚ))
      (U := (-(341976439182884107769 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_603_15 :
    Uω (aρ 15) (bρ 15) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_603_16 :
    Uω (aρ 16) (bρ 16) (22242188950407 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_603 :
    Uρ (22242188950407 / 32000000000000 : ℝ) ≤
      (-(1578370495051350464269 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_603_1 U_603_2 U_603_3 U_603_4 U_603_5 U_603_6 U_603_7 U_603_8 U_603_9 U_603_10
    U_603_11 U_603_12 U_603_13 U_603_14 U_603_15 U_603_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
