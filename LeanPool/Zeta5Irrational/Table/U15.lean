/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U15) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_184_1 :
    Uω (aρ 1) (bρ 1) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(10734696757160727232713 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1168412208664483 / 10000000000000000 : ℝ) ≤
      (-(10734696757160727232713 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1168412208664483 / 10000000000000000 : ℚ))
        (r' := (1168412208664483 / 625000000000000 : ℚ))
        (U := (-(10734696757160727232713 / 5000000000000000000000 : ℚ)))
        (U' := (3128246848839272767287 / 5000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1972876467523 / 16000000000000 : ℚ))
      (s := (1168273843212091 / 10000000000000000 : ℚ))
      (q := (1168412208664483 / 10000000000000000 : ℚ))
      (U := (-(10734696757160727232713 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_184_2 :
    Uω (aρ 2) (bρ 2) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(10840908887218247258763 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1143854059566267 / 10000000000000000 : ℝ) ≤
      (-(10840908887218247258763 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1143854059566267 / 10000000000000000 : ℚ))
        (r' := (1143854059566267 / 625000000000000 : ℚ))
        (U := (-(10840908887218247258763 / 5000000000000000000000 : ℚ)))
        (U' := (3022034718781752741237 / 5000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1972876467523 / 16000000000000 : ℚ))
      (s := (1142926557525659 / 10000000000000000 : ℚ))
      (q := (1143854059566267 / 10000000000000000 : ℚ))
      (U := (-(10840908887218247258763 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_184_3 :
    Uω (aρ 3) (bρ 3) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(11063702462299722560483 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1094004261679317 / 10000000000000000 : ℝ) ≤
      (-(11063702462299722560483 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1094004261679317 / 10000000000000000 : ℚ))
        (r' := (1094004261679317 / 625000000000000 : ℚ))
        (U := (-(11063702462299722560483 / 5000000000000000000000 : ℚ)))
        (U' := (2799241143700277439517 / 5000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1972876467523 / 16000000000000 : ℚ))
      (s := (1090623068101759 / 10000000000000000 : ℚ))
      (q := (1094004261679317 / 10000000000000000 : ℚ))
      (U := (-(11063702462299722560483 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_184_4 :
    Uω (aρ 4) (bρ 4) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(22939613024631683193711 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2017322162972089 / 20000000000000000 : ℝ) ≤
      (-(22939613024631683193711 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2017322162972089 / 20000000000000000 : ℚ))
        (r' := (2017322162972089 / 1250000000000000 : ℚ))
        (U := (-(22939613024631683193711 / 10000000000000000000000 : ℚ)))
        (U' := (4786274187368316806289 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1972876467523 / 16000000000000 : ℚ))
      (s := (499115444390107 / 5000000000000000 : ℚ))
      (q := (2017322162972089 / 20000000000000000 : ℚ))
      (U := (-(22939613024631683193711 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_184_5 :
    Uω (aρ 5) (bρ 5) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(4882994056373813382959 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (174060933478281 / 2000000000000000 : ℝ) ≤
      (-(4882994056373813382959 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (174060933478281 / 2000000000000000 : ℚ))
        (r' := (174060933478281 / 125000000000000 : ℚ))
        (U := (-(4882994056373813382959 / 2000000000000000000000 : ℚ)))
        (U' := (662183386026186617041 / 2000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1972876467523 / 16000000000000 : ℚ))
      (s := (167941595985187 / 2000000000000000 : ℚ))
      (q := (174060933478281 / 2000000000000000 : ℚ))
      (U := (-(4882994056373813382959 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_184_6 :
    Uω (aρ 6) (bρ 6) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(13764778325010343518127 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3186959537949 / 50000000000000 : ℝ) ≤
      (-(13764778325010343518127 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3186959537949 / 50000000000000 : ℚ))
        (r' := (3186959537949 / 3125000000000 : ℚ))
        (U := (-(13764778325010343518127 / 5000000000000000000000 : ℚ)))
        (U' := (98165280989656481873 / 5000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1972876467523 / 16000000000000 : ℚ))
      (s := (21644913418509 / 400000000000000 : ℚ))
      (q := (3186959537949 / 50000000000000 : ℚ))
      (U := (-(13764778325010343518127 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_184_7 :
    Uω (aρ 7) (bρ 7) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_184_8 :
    Uω (aρ 8) (bρ 8) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_184_9 :
    Uω (aρ 9) (bρ 9) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_184_10 :
    Uω (aρ 10) (bρ 10) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_184_11 :
    Uω (aρ 11) (bρ 11) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_184_12 :
    Uω (aρ 12) (bρ 12) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_184_13 :
    Uω (aρ 13) (bρ 13) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_184_14 :
    Uω (aρ 14) (bρ 14) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_184_15 :
    Uω (aρ 15) (bρ 15) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_184_16 :
    Uω (aρ 16) (bρ 16) (1972876467523 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_184 :
    Uρ (1972876467523 / 16000000000000 : ℝ) ≤
      (-(11343342076695662676383 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_184_1 U_184_2 U_184_3 U_184_4 U_184_5 U_184_6 U_184_7 U_184_8 U_184_9 U_184_10
    U_184_11 U_184_12 U_184_13 U_184_14 U_184_15 U_184_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_185_1 :
    Uω (aρ 1) (bρ 1) (199529881231 / 1600000000000 : ℝ) ≤
      (-(4270030594954638318783 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1182427814235847 / 10000000000000000 : ℝ) ≤
      (-(4270030594954638318783 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1182427814235847 / 10000000000000000 : ℚ))
        (r' := (1182427814235847 / 625000000000000 : ℚ))
        (U := (-(4270030594954638318783 / 2000000000000000000000 : ℚ)))
        (U' := (1275146847445361681217 / 2000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (199529881231 / 1600000000000 : ℚ))
      (s := (36946596526967 / 312500000000000 : ℚ))
      (q := (1182427814235847 / 10000000000000000 : ℚ))
      (U := (-(4270030594954638318783 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_185_2 :
    Uω (aρ 2) (bρ 2) (199529881231 / 1600000000000 : ℝ) ≤
      (-(21559949844423918091557 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7236745373357 / 62500000000000 : ℝ) ≤
      (-(21559949844423918091557 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7236745373357 / 62500000000000 : ℚ))
        (r' := (7236745373357 / 3906250000000 : ℚ))
        (U := (-(21559949844423918091557 / 10000000000000000000000 : ℚ)))
        (U' := (6165937367576081908443 / 10000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (199529881231 / 1600000000000 : ℚ))
      (s := (115696299237549 / 1000000000000000 : ℚ))
      (q := (7236745373357 / 62500000000000 : ℚ))
      (U := (-(21559949844423918091557 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_185_3 :
    Uω (aρ 3) (bρ 3) (199529881231 / 1600000000000 : ℝ) ≤
      (-(21999733418108408918803 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (277015280245117 / 2500000000000000 : ℝ) ≤
      (-(21999733418108408918803 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (277015280245117 / 2500000000000000 : ℚ))
        (r' := (277015280245117 / 156250000000000 : ℚ))
        (U := (-(21999733418108408918803 / 10000000000000000000000 : ℚ)))
        (U' := (5726153793891591081197 / 10000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (199529881231 / 1600000000000 : ℚ))
      (s := (552361410606093 / 5000000000000000 : ℚ))
      (q := (277015280245117 / 2500000000000000 : ℚ))
      (U := (-(21999733418108408918803 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_185_4 :
    Uω (aρ 4) (bρ 4) (199529881231 / 1600000000000 : ℝ) ≤
      (-(22800221341664611774923 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (409127770634337 / 4000000000000000 : ℝ) ≤
      (-(22800221341664611774923 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (409127770634337 / 4000000000000000 : ℚ))
        (r' := (409127770634337 / 250000000000000 : ℚ))
        (U := (-(22800221341664611774923 / 10000000000000000000000 : ℚ)))
        (U' := (4925665870335388225077 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (199529881231 / 1600000000000 : ℚ))
      (s := (202506722697587 / 2000000000000000 : ℚ))
      (q := (409127770634337 / 4000000000000000 : ℚ))
      (U := (-(22800221341664611774923 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_185_5 :
    Uω (aρ 5) (bρ 5) (199529881231 / 1600000000000 : ℝ) ≤
      (-(24249554734050633766169 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (884820586671631 / 10000000000000000 : ℝ) ≤
      (-(24249554734050633766169 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (884820586671631 / 10000000000000000 : ℚ))
        (r' := (884820586671631 / 625000000000000 : ℚ))
        (U := (-(24249554734050633766169 / 10000000000000000000000 : ℚ)))
        (U' := (3476332477949366233831 / 10000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (199529881231 / 1600000000000 : ℚ))
      (s := (53420365812157 / 625000000000000 : ℚ))
      (q := (884820586671631 / 10000000000000000 : ℚ))
      (U := (-(24249554734050633766169 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_185_6 :
    Uω (aρ 6) (bρ 6) (199529881231 / 1600000000000 : ℝ) ≤
      (-(5454999569515305561689 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (653825558776359 / 10000000000000000 : ℝ) ≤
      (-(5454999569515305561689 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (653825558776359 / 10000000000000000 : ℚ))
        (r' := (653825558776359 / 625000000000000 : ℚ))
        (U := (-(5454999569515305561689 / 2000000000000000000000 : ℚ)))
        (U' := (90177872884694438311 / 2000000000000000000000 : ℚ))
        4 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (199529881231 / 1600000000000 : ℚ))
      (s := (17499255385749 / 312500000000000 : ℚ))
      (q := (653825558776359 / 10000000000000000 : ℚ))
      (U := (-(5454999569515305561689 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_185_7 :
    Uω (aρ 7) (bρ 7) (199529881231 / 1600000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_185_8 :
    Uω (aρ 8) (bρ 8) (199529881231 / 1600000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_185_9 :
    Uω (aρ 9) (bρ 9) (199529881231 / 1600000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_185_10 :
    Uω (aρ 10) (bρ 10) (199529881231 / 1600000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_185_11 :
    Uω (aρ 11) (bρ 11) (199529881231 / 1600000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_185_12 :
    Uω (aρ 12) (bρ 12) (199529881231 / 1600000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_185_13 :
    Uω (aρ 13) (bρ 13) (199529881231 / 1600000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_185_14 :
    Uω (aρ 14) (bρ 14) (199529881231 / 1600000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_185_15 :
    Uω (aρ 15) (bρ 15) (199529881231 / 1600000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_185_16 :
    Uω (aρ 16) (bρ 16) (199529881231 / 1600000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_185 :
    Uρ (199529881231 / 1600000000000 : ℝ) ≤
      (-(2829593273725598213717 / 1250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_185_1 U_185_2 U_185_3 U_185_4 U_185_5 U_185_6 U_185_7 U_185_8 U_185_9 U_185_10
    U_185_11 U_185_12 U_185_13 U_185_14 U_185_15 U_185_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_186_1 :
    Uω (aρ 1) (bρ 1) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(2654039731137533813037 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (478577352551123 / 4000000000000000 : ℝ) ≤
      (-(2654039731137533813037 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (478577352551123 / 4000000000000000 : ℚ))
        (r' := (478577352551123 / 250000000000000 : ℚ))
        (U := (-(2654039731137533813037 / 1250000000000000000000 : ℚ)))
        (U' := (811696170362466186963 / 1250000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2017721157097 / 16000000000000 : ℚ))
      (s := (119630825765499 / 1000000000000000 : ℚ))
      (q := (478577352551123 / 4000000000000000 : ℚ))
      (U := (-(2654039731137533813037 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_186_2 :
    Uω (aρ 2) (bρ 2) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(4287910305227927671211 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (292976047697431 / 2500000000000000 : ℝ) ≤
      (-(4287910305227927671211 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (292976047697431 / 2500000000000000 : ℚ))
        (r' := (292976047697431 / 156250000000000 : ℚ))
        (U := (-(4287910305227927671211 / 2000000000000000000000 : ℚ)))
        (U' := (1257267137172072328789 / 2000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2017721157097 / 16000000000000 : ℚ))
      (s := (1170998888988823 / 10000000000000000 : ℚ))
      (q := (292976047697431 / 2500000000000000 : ℚ))
      (U := (-(4287910305227927671211 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_186_3 :
    Uω (aρ 3) (bρ 3) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(21873680991519987290401 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (280529225611763 / 2500000000000000 : ℝ) ≤
      (-(21873680991519987290401 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (280529225611763 / 2500000000000000 : ℚ))
        (r' := (280529225611763 / 156250000000000 : ℚ))
        (U := (-(21873680991519987290401 / 10000000000000000000000 : ℚ)))
        (U' := (5852206220480012709599 / 10000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2017721157097 / 16000000000000 : ℚ))
      (s := (1118820418653479 / 10000000000000000 : ℚ))
      (q := (280529225611763 / 2500000000000000 : ℚ))
      (U := (-(21873680991519987290401 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_186_4 :
    Uω (aρ 4) (bρ 4) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(22662784376969185616087 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (129621723770819 / 1250000000000000 : ℝ) ≤
      (-(22662784376969185616087 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (129621723770819 / 1250000000000000 : ℚ))
        (r' := (129621723770819 / 78125000000000 : ℚ))
        (U := (-(22662784376969185616087 / 10000000000000000000000 : ℚ)))
        (U' := (5063102835030814383913 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2017721157097 / 16000000000000 : ℚ))
      (s := (1026828375157479 / 10000000000000000 : ℚ))
      (q := (129621723770819 / 1250000000000000 : ℚ))
      (U := (-(22662784376969185616087 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_186_5 :
    Uω (aρ 5) (bρ 5) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(4817403452281815741051 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (71945580042487 / 800000000000000 : ℝ) ≤
      (-(4817403452281815741051 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (71945580042487 / 800000000000000 : ℚ))
        (r' := (71945580042487 / 50000000000000 : ℚ))
        (U := (-(4817403452281815741051 / 2000000000000000000000 : ℚ)))
        (U' := (727773990118184258949 / 2000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2017721157097 / 16000000000000 : ℚ))
      (s := (17394204304431 / 200000000000000 : ℚ))
      (q := (71945580042487 / 800000000000000 : ℚ))
      (U := (-(4817403452281815741051 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_186_6 :
    Uω (aρ 6) (bρ 6) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(27028809110634695454701 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (670121781883347 / 10000000000000000 : ℝ) ≤
      (-(27028809110634695454701 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (670121781883347 / 10000000000000000 : ℚ))
        (r' := (670121781883347 / 625000000000000 : ℚ))
        (U := (-(27028809110634695454701 / 10000000000000000000000 : ℚ)))
        (U' := (697078101365304545299 / 10000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (2017721157097 / 16000000000000 : ℚ))
      (s := (578554653066069 / 10000000000000000 : ℚ))
      (q := (670121781883347 / 10000000000000000 : ℚ))
      (U := (-(27028809110634695454701 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_186_7 :
    Uω (aρ 7) (bρ 7) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_186_8 :
    Uω (aρ 8) (bρ 8) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_186_9 :
    Uω (aρ 9) (bρ 9) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_186_10 :
    Uω (aρ 10) (bρ 10) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_186_11 :
    Uω (aρ 11) (bρ 11) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_186_12 :
    Uω (aρ 12) (bρ 12) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_186_13 :
    Uω (aρ 13) (bρ 13) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_186_14 :
    Uω (aρ 14) (bρ 14) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_186_15 :
    Uω (aρ 15) (bρ 15) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_186_16 :
    Uω (aρ 16) (bρ 16) (2017721157097 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_186 :
    Uρ (2017721157097 / 16000000000000 : ℝ) ≤
      (-(5646977118127164902371 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_186_1 U_186_2 U_186_3 U_186_4 U_186_5 U_186_6 U_186_7 U_186_8 U_186_9 U_186_10
    U_186_11 U_186_12 U_186_13 U_186_14 U_186_15 U_186_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_187_1 :
    Uω (aρ 1) (bρ 1) (510035875471 / 4000000000000 : ℝ) ≤
      (-(10557927693038472750489 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (605229455712777 / 5000000000000000 : ℝ) ≤
      (-(10557927693038472750489 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (605229455712777 / 5000000000000000 : ℚ))
        (r' := (605229455712777 / 312500000000000 : ℚ))
        (U := (-(10557927693038472750489 / 5000000000000000000000 : ℚ)))
        (U' := (3305015912961527249511 / 5000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (510035875471 / 4000000000000 : ℚ))
      (s := (75645334516163 / 625000000000000 : ℚ))
      (q := (605229455712777 / 5000000000000000 : ℚ))
      (U := (-(10557927693038472750489 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_187_2 :
    Uω (aρ 2) (bρ 2) (510035875471 / 4000000000000 : ℝ) ≤
      (-(21320587743862525124249 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (474371544914651 / 4000000000000000 : ℝ) ≤
      (-(21320587743862525124249 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (474371544914651 / 4000000000000000 : ℚ))
        (r' := (474371544914651 / 250000000000000 : ℚ))
        (U := (-(21320587743862525124249 / 10000000000000000000000 : ℚ)))
        (U' := (6405299468137474875751 / 10000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (510035875471 / 4000000000000 : ℚ))
      (s := (237006853298151 / 2000000000000000 : ℚ))
      (q := (474371544914651 / 4000000000000000 : ℚ))
      (U := (-(21320587743862525124249 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_187_3 :
    Uω (aρ 3) (bρ 3) (510035875471 / 4000000000000 : ℝ) ≤
      (-(4349841371920999492129 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2272343292631247 / 20000000000000000 : ℝ) ≤
      (-(4349841371920999492129 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2272343292631247 / 20000000000000000 : ℚ))
        (r' := (2272343292631247 / 1250000000000000 : ℚ))
        (U := (-(4349841371920999492129 / 2000000000000000000000 : ℚ)))
        (U' := (1195336070479000507871 / 2000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (510035875471 / 4000000000000 : ℚ))
      (s := (1132915940898747 / 10000000000000000 : ℚ))
      (q := (2272343292631247 / 20000000000000000 : ℚ))
      (U := (-(4349841371920999492129 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_187_4 :
    Uω (aρ 4) (bρ 4) (510035875471 / 4000000000000 : ℝ) ≤
      (-(28159058803363137901 / 12500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1051124336229791 / 10000000000000000 : ℝ) ≤
      (-(28159058803363137901 / 12500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1051124336229791 / 10000000000000000 : ℚ))
        (r' := (1051124336229791 / 625000000000000 : ℚ))
        (U := (-(28159058803363137901 / 12500000000000000000 : ℚ)))
        (U' := (6498300211636862099 / 12500000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (510035875471 / 4000000000000 : ℚ))
      (s := (520557750896041 / 5000000000000000 : ℚ))
      (q := (1051124336229791 / 10000000000000000 : ℚ))
      (U := (-(28159058803363137901 / 12500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_187_5 :
    Uω (aρ 5) (bρ 5) (510035875471 / 4000000000000 : ℝ) ≤
      (-(11963626737311393197339 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1827606020754751 / 20000000000000000 : ℝ) ≤
      (-(11963626737311393197339 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1827606020754751 / 20000000000000000 : ℚ))
        (r' := (1827606020754751 / 1250000000000000 : ℚ))
        (U := (-(11963626737311393197339 / 5000000000000000000000 : ℚ)))
        (U' := (1899316868688606802661 / 5000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (510035875471 / 4000000000000 : ℚ))
      (s := (884662769422251 / 10000000000000000 : ℚ))
      (q := (1827606020754751 / 20000000000000000 : ℚ))
      (U := (-(11963626737311393197339 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_187_6 :
    Uω (aρ 6) (bρ 6) (510035875471 / 4000000000000 : ℝ) ≤
      (-(13395175617456387926221 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (686293409856847 / 10000000000000000 : ℝ) ≤
      (-(13395175617456387926221 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (686293409856847 / 10000000000000000 : ℚ))
        (r' := (686293409856847 / 625000000000000 : ℚ))
        (U := (-(13395175617456387926221 / 5000000000000000000000 : ℚ)))
        (U' := (467767988543612073779 / 5000000000000000000000 : ℚ))
        4 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (510035875471 / 4000000000000 : ℚ))
      (s := (298441971760597 / 5000000000000000 : ℚ))
      (q := (686293409856847 / 10000000000000000 : ℚ))
      (U := (-(13395175617456387926221 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_187_7 :
    Uω (aρ 7) (bρ 7) (510035875471 / 4000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_187_8 :
    Uω (aρ 8) (bρ 8) (510035875471 / 4000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_187_9 :
    Uω (aρ 9) (bρ 9) (510035875471 / 4000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_187_10 :
    Uω (aρ 10) (bρ 10) (510035875471 / 4000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_187_11 :
    Uω (aρ 11) (bρ 11) (510035875471 / 4000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_187_12 :
    Uω (aρ 12) (bρ 12) (510035875471 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_187_13 :
    Uω (aρ 13) (bρ 13) (510035875471 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_187_14 :
    Uω (aρ 14) (bρ 14) (510035875471 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_187_15 :
    Uω (aρ 15) (bρ 15) (510035875471 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_187_16 :
    Uω (aρ 16) (bρ 16) (510035875471 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_187 :
    Uρ (510035875471 / 4000000000000 : ℝ) ≤
      (-(22540107043114398128433 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_187_1 U_187_2 U_187_3 U_187_4 U_187_5 U_187_6 U_187_7 U_187_8 U_187_9 U_187_10
    U_187_11 U_187_12 U_187_13 U_187_14 U_187_15 U_187_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_188_1 :
    Uω (aρ 1) (bρ 1) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(2088692305103148942643 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2476979730553741 / 20000000000000000 : ℝ) ≤
      (-(2088692305103148942643 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2476979730553741 / 20000000000000000 : ℚ))
        (r' := (2476979730553741 / 1250000000000000 : ℚ))
        (U := (-(2088692305103148942643 / 1000000000000000000000 : ℚ)))
        (U' := (683896416096851057357 / 1000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1042494095729 / 8000000000000 : ℚ))
      (s := (1238359328977491 / 10000000000000000 : ℚ))
      (q := (2476979730553741 / 20000000000000000 : ℚ))
      (U := (-(2088692305103148942643 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_188_2 :
    Uω (aρ 2) (bρ 2) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(5271707410071795261109 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2427954925298247 / 20000000000000000 : ℝ) ≤
      (-(5271707410071795261109 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2427954925298247 / 20000000000000000 : ℚ))
        (r' := (2427954925298247 / 1250000000000000 : ℚ))
        (U := (-(5271707410071795261109 / 2500000000000000000000 : ℚ)))
        (U' := (1659764392928204738891 / 2500000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1042494095729 / 8000000000000 : ℚ))
      (s := (1213103536231997 / 10000000000000000 : ℚ))
      (q := (2427954925298247 / 20000000000000000 : ℚ))
      (U := (-(5271707410071795261109 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_188_3 :
    Uω (aρ 3) (bρ 3) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(4300967582928605563113 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (582139086203921 / 5000000000000000 : ℝ) ≤
      (-(4300967582928605563113 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (582139086203921 / 5000000000000000 : ℚ))
        (r' := (582139086203921 / 312500000000000 : ℚ))
        (U := (-(4300967582928605563113 / 2000000000000000000000 : ℚ)))
        (U' := (1244209859471394436887 / 2000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1042494095729 / 8000000000000 : ℚ))
      (s := (580550531049717 / 5000000000000000 : ℚ))
      (q := (582139086203921 / 5000000000000000 : ℚ))
      (U := (-(4300967582928605563113 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_188_4 :
    Uω (aρ 4) (bρ 4) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(22261662463063795315849 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (539707293795511 / 5000000000000000 : ℝ) ≤
      (-(22261662463063795315849 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (539707293795511 / 5000000000000000 : ℚ))
        (r' := (539707293795511 / 312500000000000 : ℚ))
        (U := (-(22261662463063795315849 / 10000000000000000000000 : ℚ)))
        (U' := (5464224748936204684151 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1042494095729 / 8000000000000 : ℚ))
      (s := (534834036765397 / 5000000000000000 : ℚ))
      (q := (539707293795511 / 5000000000000000 : ℚ))
      (U := (-(22261662463063795315849 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_188_5 :
    Uω (aρ 5) (bρ 5) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(23615658202251705360119 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1885449873843263 / 20000000000000000 : ℝ) ≤
      (-(23615658202251705360119 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1885449873843263 / 20000000000000000 : ℚ))
        (r' := (1885449873843263 / 1250000000000000 : ℚ))
        (U := (-(23615658202251705360119 / 10000000000000000000000 : ℚ)))
        (U' := (4110229009748294639881 / 10000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1042494095729 / 8000000000000 : ℚ))
      (s := (914478691527013 / 10000000000000000 : ℚ))
      (q := (1885449873843263 / 20000000000000000 : ℚ))
      (U := (-(23615658202251705360119 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_188_6 :
    Uω (aρ 6) (bρ 6) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(329180582000059646687 / 125000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1436612075902289 / 20000000000000000 : ℝ) ≤
      (-(329180582000059646687 / 125000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1436612075902289 / 20000000000000000 : ℚ))
        (r' := (1436612075902289 / 1250000000000000 : ℚ))
        (U := (-(329180582000059646687 / 125000000000000000000 : ℚ)))
        (U' := (17393008149940353313 / 125000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1042494095729 / 8000000000000 : ℚ))
      (s := (632881268726039 / 10000000000000000 : ℚ))
      (q := (1436612075902289 / 20000000000000000 : ℚ))
      (U := (-(329180582000059646687 / 125000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_188_7 :
    Uω (aρ 7) (bρ 7) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_188_8 :
    Uω (aρ 8) (bρ 8) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_188_9 :
    Uω (aρ 9) (bρ 9) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_188_10 :
    Uω (aρ 10) (bρ 10) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_188_11 :
    Uω (aρ 11) (bρ 11) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_188_12 :
    Uω (aρ 12) (bρ 12) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_188_13 :
    Uω (aρ 13) (bρ 13) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_188_14 :
    Uω (aρ 14) (bρ 14) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_188_15 :
    Uω (aρ 15) (bρ 15) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_188_16 :
    Uω (aρ 16) (bρ 16) (1042494095729 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_188 :
    Uρ (1042494095729 / 8000000000000 : ℝ) ≤
      (-(22447390042549224808151 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_188_1 U_188_2 U_188_3 U_188_4 U_188_5 U_188_6 U_188_7 U_188_8 U_188_9 U_188_10
    U_188_11 U_188_12 U_188_13 U_188_14 U_188_15 U_188_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_189_1 :
    Uω (aρ 1) (bρ 1) (266229110129 / 2000000000000 : ℝ) ≤
      (-(20663115692318653602647 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (633260342654493 / 5000000000000000 : ℝ) ≤
      (-(20663115692318653602647 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (633260342654493 / 5000000000000000 : ℚ))
        (r' := (633260342654493 / 625000000000000 : ℚ))
        (U := (-(20663115692318653602647 / 10000000000000000000000 : ℚ)))
        (U' := (131299716681346397353 / 10000000000000000000000 : ℚ))
        3 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (266229110129 / 2000000000000 : ℚ))
      (s := (316598259514493 / 2500000000000000 : ℚ))
      (q := (633260342654493 / 5000000000000000 : ℚ))
      (U := (-(20663115692318653602647 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_189_2 :
    Uω (aρ 2) (bρ 2) (266229110129 / 2000000000000 : ℝ) ≤
      (-(20858418761046195439279 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1242025128818447 / 10000000000000000 : ℝ) ≤
      (-(20858418761046195439279 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1242025128818447 / 10000000000000000 : ℚ))
        (r' := (1242025128818447 / 625000000000000 : ℚ))
        (U := (-(20858418761046195439279 / 10000000000000000000000 : ℚ)))
        (U' := (6867468450953804560721 / 10000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (266229110129 / 2000000000000 : ℚ))
      (s := (620585468793447 / 5000000000000000 : ℚ))
      (q := (1242025128818447 / 10000000000000000 : ℚ))
      (U := (-(20858418761046195439279 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_189_3 :
    Uω (aρ 3) (bρ 3) (266229110129 / 2000000000000 : ℝ) ≤
      (-(4253265914535006292877 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1192380983595443 / 10000000000000000 : ℝ) ≤
      (-(4253265914535006292877 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1192380983595443 / 10000000000000000 : ℚ))
        (r' := (1192380983595443 / 625000000000000 : ℚ))
        (U := (-(4253265914535006292877 / 2000000000000000000000 : ℚ)))
        (U' := (1291911527864993707123 / 2000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (266229110129 / 2000000000000 : ℚ))
      (s := (594639376745443 / 5000000000000000 : ℚ))
      (q := (1192380983595443 / 10000000000000000 : ℚ))
      (U := (-(4253265914535006292877 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_189_4 :
    Uω (aρ 4) (bρ 4) (266229110129 / 2000000000000 : ℝ) ≤
      (-(22003071308913592837197 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2215382647996537 / 20000000000000000 : ℝ) ≤
      (-(22003071308913592837197 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2215382647996537 / 20000000000000000 : ℚ))
        (r' := (2215382647996537 / 1250000000000000 : ℚ))
        (U := (-(22003071308913592837197 / 10000000000000000000000 : ℚ)))
        (U' := (5722815903086407162803 / 10000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (266229110129 / 2000000000000 : ℚ))
      (s := (1098193615361537 / 10000000000000000 : ℚ))
      (q := (2215382647996537 / 20000000000000000 : ℚ))
      (U := (-(22003071308913592837197 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_189_5 :
    Uω (aρ 5) (bρ 5) (266229110129 / 2000000000000 : ℝ) ≤
      (-(11657021536339170325913 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1943184195125871 / 20000000000000000 : ℝ) ≤
      (-(11657021536339170325913 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1943184195125871 / 20000000000000000 : ℚ))
        (r' := (1943184195125871 / 1250000000000000 : ℚ))
        (U := (-(11657021536339170325913 / 5000000000000000000000 : ℚ)))
        (U' := (2205922069660829674087 / 5000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (266229110129 / 2000000000000 : ℚ))
      (s := (944185081825871 / 10000000000000000 : ℚ))
      (q := (1943184195125871 / 20000000000000000 : ℚ))
      (U := (-(11657021536339170325913 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_189_6 :
    Uω (aρ 6) (bρ 6) (266229110129 / 2000000000000 : ℝ) ≤
      (-(25903511253721066404459 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1499874063837843 / 20000000000000000 : ℝ) ≤
      (-(25903511253721066404459 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1499874063837843 / 20000000000000000 : ℚ))
        (r' := (1499874063837843 / 1250000000000000 : ℚ))
        (U := (-(25903511253721066404459 / 10000000000000000000000 : ℚ)))
        (U' := (1822375958278933595541 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (266229110129 / 2000000000000 : ℚ))
      (s := (668115325677843 / 10000000000000000 : ℚ))
      (q := (1499874063837843 / 20000000000000000 : ℚ))
      (U := (-(25903511253721066404459 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_189_7 :
    Uω (aρ 7) (bρ 7) (266229110129 / 2000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_189_8 :
    Uω (aρ 8) (bρ 8) (266229110129 / 2000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_189_9 :
    Uω (aρ 9) (bρ 9) (266229110129 / 2000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_189_10 :
    Uω (aρ 10) (bρ 10) (266229110129 / 2000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_189_11 :
    Uω (aρ 11) (bρ 11) (266229110129 / 2000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_189_12 :
    Uω (aρ 12) (bρ 12) (266229110129 / 2000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_189_13 :
    Uω (aρ 13) (bρ 13) (266229110129 / 2000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_189_14 :
    Uω (aρ 14) (bρ 14) (266229110129 / 2000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_189_15 :
    Uω (aρ 15) (bρ 15) (266229110129 / 2000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_189_16 :
    Uω (aρ 16) (bρ 16) (266229110129 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_189 :
    Uρ (266229110129 / 2000000000000 : ℝ) ≤
      (-(11179100805596847419571 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_189_1 U_189_2 U_189_3 U_189_4 U_189_5 U_189_6 U_189_7 U_189_8 U_189_9 U_189_10
    U_189_11 U_189_12 U_189_13 U_189_14 U_189_15 U_189_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_190_1 :
    Uω (aρ 1) (bρ 1) (110976113009 / 800000000000 : ℝ) ≤
      (-(20229992373945278136929 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2645163915912357 / 20000000000000000 : ℝ) ≤
      (-(20229992373945278136929 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2645163915912357 / 20000000000000000 : ℚ))
        (r' := (2645163915912357 / 2500000000000000 : ℚ))
        (U := (-(20229992373945278136929 / 10000000000000000000000 : ℚ)))
        (U' := (564423035054721863071 / 10000000000000000000000 : ℚ))
        3 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (110976113009 / 800000000000 : ℚ))
      (s := (1322459721384857 / 10000000000000000 : ℚ))
      (q := (2645163915912357 / 20000000000000000 : ℚ))
      (U := (-(20229992373945278136929 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_190_2 :
    Uω (aρ 2) (bρ 2) (110976113009 / 800000000000 : ℝ) ≤
      (-(20416696451517995856967 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2596235802222861 / 20000000000000000 : ℝ) ≤
      (-(20416696451517995856967 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2596235802222861 / 20000000000000000 : ℚ))
        (r' := (2596235802222861 / 2500000000000000 : ℚ))
        (U := (-(20416696451517995856967 / 10000000000000000000000 : ℚ)))
        (U' := (377718957482004143033 / 10000000000000000000000 : ℚ))
        3 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (110976113009 / 800000000000 : ℚ))
      (s := (1297300620205361 / 10000000000000000 : ℚ))
      (q := (2596235802222861 / 20000000000000000 : ℚ))
      (U := (-(20416696451517995856967 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_190_3 :
    Uω (aρ 3) (bρ 3) (110976113009 / 800000000000 : ℝ) ≤
      (-(2080581013886745405213 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1248576469633047 / 10000000000000000 : ℝ) ≤
      (-(2080581013886745405213 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1248576469633047 / 10000000000000000 : ℚ))
        (r' := (1248576469633047 / 625000000000000 : ℚ))
        (U := (-(2080581013886745405213 / 1000000000000000000000 : ℚ)))
        (U' := (692007707313254594787 / 1000000000000000000000 : ℚ))
        4 15 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (110976113009 / 800000000000 : ℚ))
      (s := (622806931799297 / 5000000000000000 : ℚ))
      (q := (1248576469633047 / 10000000000000000 : ℚ))
      (U := (-(2080581013886745405213 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_190_4 :
    Uω (aρ 4) (bρ 4) (110976113009 / 800000000000 : ℝ) ≤
      (-(21505438446981235916047 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1164208255837901 / 10000000000000000 : ℝ) ≤
      (-(21505438446981235916047 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1164208255837901 / 10000000000000000 : ℚ))
        (r' := (1164208255837901 / 625000000000000 : ℚ))
        (U := (-(21505438446981235916047 / 10000000000000000000000 : ℚ)))
        (U' := (6220448765018764083953 / 10000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (110976113009 / 800000000000 : ℚ))
      (s := (577585808536651 / 5000000000000000 : ℚ))
      (q := (1164208255837901 / 10000000000000000 : ℚ))
      (U := (-(21505438446981235916047 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_190_5 :
    Uω (aρ 5) (bρ 5) (110976113009 / 800000000000 : ℝ) ≤
      (-(4547642411201558481751 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2058363123946183 / 20000000000000000 : ℝ) ≤
      (-(4547642411201558481751 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2058363123946183 / 20000000000000000 : ℚ))
        (r' := (2058363123946183 / 1250000000000000 : ℚ))
        (U := (-(4547642411201558481751 / 2000000000000000000000 : ℚ)))
        (U' := (997535031198441518249 / 2000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (110976113009 / 800000000000 : ℚ))
      (s := (1003308148678683 / 10000000000000000 : ℚ))
      (q := (2058363123946183 / 20000000000000000 : ℚ))
      (U := (-(4547642411201558481751 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_190_6 :
    Uω (aρ 6) (bρ 6) (110976113009 / 800000000000 : ℝ) ≤
      (-(25105050925041415667209 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (406136007713679 / 5000000000000000 : ℝ) ≤
      (-(25105050925041415667209 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (406136007713679 / 5000000000000000 : ℚ))
        (r' := (406136007713679 / 312500000000000 : ℚ))
        (U := (-(25105050925041415667209 / 10000000000000000000000 : ℚ)))
        (U' := (2620836286958584332791 / 10000000000000000000000 : ℚ))
        4 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (110976113009 / 800000000000 : ℚ))
      (s := (46045589420451 / 625000000000000 : ℚ))
      (q := (406136007713679 / 5000000000000000 : ℚ))
      (U := (-(25105050925041415667209 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_190_7 :
    Uω (aρ 7) (bρ 7) (110976113009 / 800000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_190_8 :
    Uω (aρ 8) (bρ 8) (110976113009 / 800000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_190_9 :
    Uω (aρ 9) (bρ 9) (110976113009 / 800000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_190_10 :
    Uω (aρ 10) (bρ 10) (110976113009 / 800000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_190_11 :
    Uω (aρ 11) (bρ 11) (110976113009 / 800000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_190_12 :
    Uω (aρ 12) (bρ 12) (110976113009 / 800000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_190_13 :
    Uω (aρ 13) (bρ 13) (110976113009 / 800000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_190_14 :
    Uω (aρ 14) (bρ 14) (110976113009 / 800000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_190_15 :
    Uω (aρ 15) (bρ 15) (110976113009 / 800000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_190_16 :
    Uω (aρ 16) (bρ 16) (110976113009 / 800000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_190 :
    Uρ (110976113009 / 800000000000 : ℝ) ≤
      (-(11094580622395912739221 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_190_1 U_190_2 U_190_3 U_190_4 U_190_5 U_190_6 U_190_7 U_190_8 U_190_9 U_190_10
    U_190_11 U_190_12 U_190_13 U_190_14 U_190_15 U_190_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_191_1 :
    Uω (aρ 1) (bρ 1) (72162863729 / 500000000000 : ℝ) ≤
      (-(19814855621105804326481 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (275728558105041 / 2000000000000000 : ℝ) ≤
      (-(19814855621105804326481 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (275728558105041 / 2000000000000000 : ℚ))
        (r' := (275728558105041 / 250000000000000 : ℚ))
        (U := (-(19814855621105804326481 / 10000000000000000000000 : ℚ)))
        (U' := (979559787894195673519 / 10000000000000000000000 : ℚ))
        3 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (72162863729 / 500000000000 : ℚ))
      (s := (137852552455541 / 1000000000000000 : ℚ))
      (q := (275728558105041 / 2000000000000000 : ℚ))
      (U := (-(19814855621105804326481 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_191_2 :
    Uω (aρ 2) (bρ 2) (72162863729 / 500000000000 : ℝ) ≤
      (-(19993685957203362780097 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2708415227817231 / 20000000000000000 : ℝ) ≤
      (-(19993685957203362780097 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2708415227817231 / 20000000000000000 : ℚ))
        (r' := (2708415227817231 / 2500000000000000 : ℚ))
        (U := (-(19993685957203362780097 / 10000000000000000000000 : ℚ)))
        (U' := (800729451796637219903 / 10000000000000000000000 : ℚ))
        3 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (72162863729 / 500000000000 : ℚ))
      (s := (1353424183832231 / 10000000000000000 : ℚ))
      (q := (2708415227817231 / 20000000000000000 : ℚ))
      (U := (-(19993685957203362780097 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_191_3 :
    Uω (aρ 3) (bρ 3) (72162863729 / 500000000000 : ℝ) ≤
      (-(10182830255675675289117 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (521903960994751 / 4000000000000000 : ℝ) ≤
      (-(10182830255675675289117 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (521903960994751 / 4000000000000000 : ℚ))
        (r' := (521903960994751 / 500000000000000 : ℚ))
        (U := (-(10182830255675675289117 / 5000000000000000000000 : ℚ)))
        (U' := (214377448824324710883 / 5000000000000000000000 : ℚ))
        3 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (72162863729 / 500000000000 : ℚ))
      (s := (260384973467751 / 2000000000000000 : ℚ))
      (q := (521903960994751 / 4000000000000000 : ℚ))
      (U := (-(10182830255675675289117 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_191_4 :
    Uω (aρ 4) (bρ 4) (72162863729 / 500000000000 : ℝ) ≤
      (-(2628969020630553055031 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2441364382080019 / 20000000000000000 : ℝ) ≤
      (-(2628969020630553055031 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2441364382080019 / 20000000000000000 : ℚ))
        (r' := (2441364382080019 / 1250000000000000 : ℚ))
        (U := (-(2628969020630553055031 / 1250000000000000000000 : ℚ)))
        (U' := (836766880869446944969 / 1250000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (72162863729 / 500000000000 : ℚ))
      (s := (1212063625510019 / 10000000000000000 : ℚ))
      (q := (2441364382080019 / 20000000000000000 : ℚ))
      (U := (-(2628969020630553055031 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_191_5 :
    Uω (aρ 5) (bρ 5) (72162863729 / 500000000000 : ℝ) ≤
      (-(22195271732922818939507 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2173209482836907 / 20000000000000000 : ℝ) ≤
      (-(22195271732922818939507 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2173209482836907 / 20000000000000000 : ℚ))
        (r' := (2173209482836907 / 1250000000000000 : ℚ))
        (U := (-(22195271732922818939507 / 10000000000000000000000 : ℚ)))
        (U' := (5530615479077181060493 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (72162863729 / 500000000000 : ℚ))
      (s := (1062098645601907 / 10000000000000000 : ℚ))
      (q := (2173209482836907 / 20000000000000000 : ℚ))
      (U := (-(22195271732922818939507 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_191_6 :
    Uω (aρ 6) (bρ 6) (72162863729 / 500000000000 : ℝ) ≤
      (-(24376790840821149583193 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (349453517251867 / 4000000000000000 : ℝ) ≤
      (-(24376790840821149583193 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (349453517251867 / 4000000000000000 : ℚ))
        (r' := (349453517251867 / 250000000000000 : ℚ))
        (U := (-(24376790840821149583193 / 10000000000000000000000 : ℚ)))
        (U' := (3349096371178850416807 / 10000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (72162863729 / 500000000000 : ℚ))
      (s := (160679424832867 / 2000000000000000 : ℚ))
      (q := (349453517251867 / 4000000000000000 : ℚ))
      (U := (-(24376790840821149583193 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_191_7 :
    Uω (aρ 7) (bρ 7) (72162863729 / 500000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_191_8 :
    Uω (aρ 8) (bρ 8) (72162863729 / 500000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_191_9 :
    Uω (aρ 9) (bρ 9) (72162863729 / 500000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_191_10 :
    Uω (aρ 10) (bρ 10) (72162863729 / 500000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_191_11 :
    Uω (aρ 11) (bρ 11) (72162863729 / 500000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_191_12 :
    Uω (aρ 12) (bρ 12) (72162863729 / 500000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_191_13 :
    Uω (aρ 13) (bρ 13) (72162863729 / 500000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_191_14 :
    Uω (aρ 14) (bρ 14) (72162863729 / 500000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_191_15 :
    Uω (aρ 15) (bρ 15) (72162863729 / 500000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_191_16 :
    Uω (aρ 16) (bρ 16) (72162863729 / 500000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_191 :
    Uρ (72162863729 / 500000000000 : ℝ) ≤
      (-(22030937450651269436371 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_191_1 U_191_2 U_191_3 U_191_4 U_191_5 U_191_6 U_191_7 U_191_8 U_191_9 U_191_10
    U_191_11 U_191_12 U_191_13 U_191_14 U_191_15 U_191_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_192_1 :
    Uω (aρ 1) (bρ 1) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(787478463849348170387 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5585552167037221 / 40000000000000000 : ℝ) ≤
      (-(787478463849348170387 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5585552167037221 / 40000000000000000 : ℚ))
        (r' := (5585552167037221 / 5000000000000000 : ℚ))
        (U := (-(787478463849348170387 / 400000000000000000000 : ℚ)))
        (U' := (44298152510651829613 / 400000000000000000000 : ℚ))
        3 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4675203313927 / 32000000000000 : ℚ))
      (s := (1396272266001423 / 10000000000000000 : ℚ))
      (q := (5585552167037221 / 40000000000000000 : ℚ))
      (U := (-(787478463849348170387 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_192_2 :
    Uω (aρ 2) (bρ 2) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(19863436151075893595487 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5487846051701767 / 40000000000000000 : ℝ) ≤
      (-(19863436151075893595487 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5487846051701767 / 40000000000000000 : ℚ))
        (r' := (5487846051701767 / 5000000000000000 : ℚ))
        (U := (-(19863436151075893595487 / 10000000000000000000000 : ℚ)))
        (U' := (930979257924106404513 / 10000000000000000000000 : ℚ))
        3 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4675203313927 / 32000000000000 : ℚ))
      (s := (85699263802731 / 625000000000000 : ℚ))
      (q := (5487846051701767 / 40000000000000000 : ℚ))
      (U := (-(19863436151075893595487 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_192_3 :
    Uω (aρ 3) (bρ 3) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(4046059230732191981441 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5290167124837241 / 40000000000000000 : ℝ) ≤
      (-(4046059230732191981441 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5290167124837241 / 40000000000000000 : ℚ))
        (r' := (5290167124837241 / 5000000000000000 : ℚ))
        (U := (-(4046059230732191981441 / 2000000000000000000000 : ℚ)))
        (U' := (112823851067808018559 / 2000000000000000000000 : ℚ))
        3 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4675203313927 / 32000000000000 : ℚ))
      (s := (1319744863761433 / 10000000000000000 : ℚ))
      (q := (5290167124837241 / 40000000000000000 : ℚ))
      (U := (-(4046059230732191981441 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_192_4 :
    Uω (aρ 4) (bρ 4) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(20886435181837476410703 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4954201155424141 / 40000000000000000 : ℝ) ≤
      (-(20886435181837476410703 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4954201155424141 / 40000000000000000 : ℚ))
        (r' := (4954201155424141 / 2500000000000000 : ℚ))
        (U := (-(20886435181837476410703 / 10000000000000000000000 : ℚ)))
        (U' := (6839452030162523589297 / 10000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4675203313927 / 32000000000000 : ℚ))
      (s := (1230056060119883 / 10000000000000000 : ℚ))
      (q := (4954201155424141 / 40000000000000000 : ℚ))
      (U := (-(20886435181837476410703 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_192_5 :
    Uω (aρ 5) (bρ 5) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(22029650929542333847147 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (883800825444237 / 8000000000000000 : ℝ) ≤
      (-(22029650929542333847147 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (883800825444237 / 8000000000000000 : ℚ))
        (r' := (883800825444237 / 500000000000000 : ℚ))
        (U := (-(22029650929542333847147 / 10000000000000000000000 : ℚ)))
        (U' := (5696236282457666152853 / 10000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4675203313927 / 32000000000000 : ℚ))
      (s := (216129493070681 / 2000000000000000 : ℚ))
      (q := (883800825444237 / 8000000000000000 : ℚ))
      (U := (-(22029650929542333847147 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_192_6 :
    Uω (aρ 6) (bρ 6) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(19326993602285207127 / 8000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3571569920567127 / 40000000000000000 : ℝ) ≤
      (-(19326993602285207127 / 8000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3571569920567127 / 40000000000000000 : ℚ))
        (r' := (3571569920567127 / 2500000000000000 : ℚ))
        (U := (-(19326993602285207127 / 8000000000000000000 : ℚ)))
        (U' := (2853716167314792873 / 8000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (4675203313927 / 32000000000000 : ℚ))
      (s := (103021342145797 / 1250000000000000 : ℚ))
      (q := (3571569920567127 / 40000000000000000 : ℚ))
      (U := (-(19326993602285207127 / 8000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_192_7 :
    Uω (aρ 7) (bρ 7) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(969506853701683875103 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (359521826035421 / 8000000000000000 : ℝ) ≤
      (-(969506853701683875103 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (359521826035421 / 8000000000000000 : ℚ))
        (r' := (359521826035421 / 250000000000000 : ℚ))
        (U := (-(969506853701683875103 / 312500000000000000000 : ℚ)))
        (U' := (113535615517066124897 / 312500000000000000000 : ℚ))
        5 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (4675203313927 / 32000000000000 : ℚ))
      (s := (32170344546273 / 2000000000000000 : ℚ))
      (q := (359521826035421 / 8000000000000000 : ℚ))
      (U := (-(969506853701683875103 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_192_8 :
    Uω (aρ 8) (bρ 8) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_192_9 :
    Uω (aρ 9) (bρ 9) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_192_10 :
    Uω (aρ 10) (bρ 10) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_192_11 :
    Uω (aρ 11) (bρ 11) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_192_12 :
    Uω (aρ 12) (bρ 12) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_192_13 :
    Uω (aρ 13) (bρ 13) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_192_14 :
    Uω (aρ 14) (bρ 14) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_192_15 :
    Uω (aρ 15) (bρ 15) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_192_16 :
    Uω (aρ 16) (bρ 16) (4675203313927 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_192 :
    Uρ (4675203313927 / 32000000000000 : ℝ) ≤
      (-(21794875057781414112513 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_192_1 U_192_2 U_192_3 U_192_4 U_192_5 U_192_6 U_192_7 U_192_8 U_192_9 U_192_10
    U_192_11 U_192_12 U_192_13 U_192_14 U_192_15 U_192_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_193_1 :
    Uω (aρ 1) (bρ 1) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(19560682890171164556221 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (282826651118107 / 2000000000000000 : ℝ) ≤
      (-(19560682890171164556221 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (282826651118107 / 2000000000000000 : ℚ))
        (r' := (282826651118107 / 250000000000000 : ℚ))
        (U := (-(19560682890171164556221 / 10000000000000000000000 : ℚ)))
        (U' := (1233732518828835443779 / 10000000000000000000000 : ℚ))
        3 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2365991674599 / 16000000000000 : ℚ))
      (s := (282803786528339 / 2000000000000000 : ℚ))
      (q := (282826651118107 / 2000000000000000 : ℚ))
      (U := (-(19560682890171164556221 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_193_2 :
    Uω (aρ 2) (bρ 2) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(394697258427317257959 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1389715152769981 / 10000000000000000 : ℝ) ≤
      (-(394697258427317257959 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1389715152769981 / 10000000000000000 : ℚ))
        (r' := (1389715152769981 / 1250000000000000 : ℚ))
        (U := (-(394697258427317257959 / 200000000000000000000 : ℚ)))
        (U' := (21191049752682742041 / 200000000000000000000 : ℚ))
        3 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2365991674599 / 16000000000000 : ℚ))
      (s := (1388951739510587 / 10000000000000000 : ℚ))
      (q := (1389715152769981 / 10000000000000000 : ℚ))
      (U := (-(394697258427317257959 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_193_3 :
    Uω (aρ 3) (bρ 3) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(2512093407885480065093 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (335080661610237 / 2500000000000000 : ℝ) ≤
      (-(2512093407885480065093 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (335080661610237 / 2500000000000000 : ℚ))
        (r' := (335080661610237 / 312500000000000 : ℚ))
        (U := (-(2512093407885480065093 / 1250000000000000000000 : ℚ)))
        (U' := (87208518239519934907 / 1250000000000000000000 : ℚ))
        3 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2365991674599 / 16000000000000 : ℚ))
      (s := (1337562833202521 / 10000000000000000 : ℚ))
      (q := (335080661610237 / 2500000000000000 : ℚ))
      (U := (-(2512093407885480065093 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_193_4 :
    Uω (aρ 4) (bρ 4) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(10371614014328306359131 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1256414826444487 / 10000000000000000 : ℝ) ≤
      (-(10371614014328306359131 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1256414826444487 / 10000000000000000 : ℚ))
        (r' := (1256414826444487 / 1250000000000000 : ℚ))
        (U := (-(10371614014328306359131 / 5000000000000000000000 : ℚ)))
        (U' := (25593690171693640869 / 5000000000000000000000 : ℚ))
        3 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2365991674599 / 16000000000000 : ℚ))
      (s := (1248041374274599 / 10000000000000000 : ℚ))
      (q := (1256414826444487 / 10000000000000000 : ℚ))
      (U := (-(10371614014328306359131 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_193_5 :
    Uω (aρ 5) (bρ 5) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(5466711720418222399723 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1122884031566689 / 10000000000000000 : ℝ) ≤
      (-(5466711720418222399723 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1122884031566689 / 10000000000000000 : ℚ))
        (r' := (1122884031566689 / 625000000000000 : ℚ))
        (U := (-(5466711720418222399723 / 2500000000000000000000 : ℚ)))
        (U' := (1464760082581777600277 / 2500000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2365991674599 / 16000000000000 : ℚ))
      (s := (1099169703854003 / 10000000000000000 : ℚ))
      (q := (1122884031566689 / 10000000000000000 : ℚ))
      (U := (-(5466711720418222399723 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_193_6 :
    Uω (aρ 6) (bρ 6) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(23946103601804326428943 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (456041051278531 / 5000000000000000 : ℝ) ≤
      (-(23946103601804326428943 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (456041051278531 / 5000000000000000 : ℚ))
        (r' := (456041051278531 / 312500000000000 : ℚ))
        (U := (-(23946103601804326428943 / 10000000000000000000000 : ℚ)))
        (U' := (3779783610195673571057 / 10000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (2365991674599 / 16000000000000 : ℚ))
      (s := (844806220974749 / 10000000000000000 : ℚ))
      (q := (456041051278531 / 5000000000000000 : ℚ))
      (U := (-(23946103601804326428943 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_193_7 :
    Uω (aρ 7) (bρ 7) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(752824408466949677751 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (39382206101409 / 800000000000000 : ℝ) ≤
      (-(752824408466949677751 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (39382206101409 / 800000000000000 : ℚ))
        (r' := (39382206101409 / 25000000000000 : ℚ))
        (U := (-(752824408466949677751 / 250000000000000000000 : ℚ)))
        (U' := (113609566908050322249 / 250000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (2365991674599 / 16000000000000 : ℚ))
      (s := (4577170983117 / 200000000000000 : ℚ))
      (q := (39382206101409 / 800000000000000 : ℚ))
      (U := (-(752824408466949677751 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_193_8 :
    Uω (aρ 8) (bρ 8) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_193_9 :
    Uω (aρ 9) (bρ 9) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_193_10 :
    Uω (aρ 10) (bρ 10) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_193_11 :
    Uω (aρ 11) (bρ 11) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_193_12 :
    Uω (aρ 12) (bρ 12) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_193_13 :
    Uω (aρ 13) (bρ 13) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_193_14 :
    Uω (aρ 14) (bρ 14) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_193_15 :
    Uω (aρ 15) (bρ 15) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_193_16 :
    Uω (aρ 16) (bρ 16) (2365991674599 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_193 :
    Uρ (2365991674599 / 16000000000000 : ℝ) ≤
      (-(21670353188008540621837 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_193_1 U_193_2 U_193_3 U_193_4 U_193_5 U_193_6 U_193_7 U_193_8 U_193_9 U_193_10
    U_193_11 U_193_12 U_193_13 U_193_14 U_193_15 U_193_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_194_1 :
    Uω (aρ 1) (bρ 1) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(3887195840299343045543 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5727513733638853 / 40000000000000000 : ℝ) ≤
      (-(3887195840299343045543 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5727513733638853 / 40000000000000000 : ℚ))
        (r' := (5727513733638853 / 5000000000000000 : ℚ))
        (U := (-(3887195840299343045543 / 2000000000000000000000 : ℚ)))
        (U' := (271687241500656954457 / 2000000000000000000000 : ℚ))
        3 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (4788763384469 / 32000000000000 : ℚ))
      (s := (178970690907233 / 1250000000000000 : ℚ))
      (q := (5727513733638853 / 40000000000000000 : ℚ))
      (U := (-(3887195840299343045543 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_194_2 :
    Uω (aρ 2) (bρ 2) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(1960792360803155468861 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1125974834608363 / 8000000000000000 : ℝ) ≤
      (-(1960792360803155468861 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1125974834608363 / 8000000000000000 : ℚ))
        (r' := (1125974834608363 / 1000000000000000 : ℚ))
        (U := (-(1960792360803155468861 / 1000000000000000000000 : ℚ)))
        (U' := (118649180096844531139 / 1000000000000000000000 : ℚ))
        3 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (4788763384469 / 32000000000000 : ℚ))
      (s := (281342951893869 / 2000000000000000 : ℚ))
      (q := (1125974834608363 / 8000000000000000 : ℚ))
      (U := (-(1960792360803155468861 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_194_3 :
    Uω (aρ 3) (bρ 3) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(19964965591887264809447 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5432410152608797 / 40000000000000000 : ℝ) ≤
      (-(19964965591887264809447 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5432410152608797 / 40000000000000000 : ℚ))
        (r' := (5432410152608797 / 5000000000000000 : ℚ))
        (U := (-(19964965591887264809447 / 10000000000000000000000 : ℚ)))
        (U' := (829449817112735190553 / 10000000000000000000000 : ℚ))
        3 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (4788763384469 / 32000000000000 : ℚ))
      (s := (338844713900709 / 2500000000000000 : ℚ))
      (q := (5432410152608797 / 40000000000000000 : ℚ))
      (U := (-(19964965591887264809447 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_194_4 :
    Uω (aρ 4) (bρ 4) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(20602069529176842578973 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5097103822148609 / 40000000000000000 : ℝ) ≤
      (-(20602069529176842578973 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5097103822148609 / 40000000000000000 : ℚ))
        (r' := (5097103822148609 / 5000000000000000 : ℚ))
        (U := (-(20602069529176842578973 / 10000000000000000000000 : ℚ)))
        (U' := (192345879823157421027 / 10000000000000000000000 : ℚ))
        3 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (4788763384469 / 32000000000000 : ℚ))
      (s := (633009935718871 / 5000000000000000 : ℚ))
      (q := (5097103822148609 / 40000000000000000 : ℚ))
      (U := (-(20602069529176842578973 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_194_5 :
    Uω (aρ 5) (bρ 5) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(21706761635276424051639 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4564017605877021 / 40000000000000000 : ℝ) ≤
      (-(21706761635276424051639 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4564017605877021 / 40000000000000000 : ℚ))
        (r' := (4564017605877021 / 2500000000000000 : ℚ))
        (U := (-(21706761635276424051639 / 10000000000000000000000 : ℚ)))
        (U' := (6019125576723575948361 / 10000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (4788763384469 / 32000000000000 : ℚ))
      (s := (279416670659237 / 2500000000000000 : ℚ))
      (q := (4564017605877021 / 40000000000000000 : ℚ))
      (U := (-(21706761635276424051639 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_194_6 :
    Uω (aρ 6) (bρ 6) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(4747716261870926325079 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3724830405755021 / 40000000000000000 : ℝ) ≤
      (-(4747716261870926325079 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3724830405755021 / 40000000000000000 : ℚ))
        (r' := (3724830405755021 / 2500000000000000 : ℚ))
        (U := (-(4747716261870926325079 / 2000000000000000000000 : ℚ)))
        (U' := (797461180529073674921 / 2000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (4788763384469 / 32000000000000 : ℚ))
      (s := (216328364428987 / 2500000000000000 : ℚ))
      (q := (3724830405755021 / 40000000000000000 : ℚ))
      (U := (-(4747716261870926325079 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_194_7 :
    Uω (aρ 7) (bρ 7) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(14708997966031985063453 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2110827096636869 / 40000000000000000 : ℝ) ≤
      (-(14708997966031985063453 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2110827096636869 / 40000000000000000 : ℚ))
        (r' := (2110827096636869 / 1250000000000000 : ℚ))
        (U := (-(14708997966031985063453 / 5000000000000000000000 : ℚ)))
        (U' := (2619681541468014936547 / 5000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (4788763384469 / 32000000000000 : ℚ))
      (s := (35246647989609 / 1250000000000000 : ℚ))
      (q := (2110827096636869 / 40000000000000000 : ℚ))
      (U := (-(14708997966031985063453 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_194_8 :
    Uω (aρ 8) (bρ 8) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_194_9 :
    Uω (aρ 9) (bρ 9) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_194_10 :
    Uω (aρ 10) (bρ 10) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_194_11 :
    Uω (aρ 11) (bρ 11) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_194_12 :
    Uω (aρ 12) (bρ 12) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_194_13 :
    Uω (aρ 13) (bρ 13) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_194_14 :
    Uω (aρ 14) (bρ 14) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_194_15 :
    Uω (aρ 15) (bρ 15) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_194_16 :
    Uω (aρ 16) (bρ 16) (4788763384469 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_194 :
    Uρ (4788763384469 / 32000000000000 : ℝ) ≤
      (-(10782516787768049362653 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_194_1 U_194_2 U_194_3 U_194_4 U_194_5 U_194_6 U_194_7 U_194_8 U_194_9 U_194_10
    U_194_11 U_194_12 U_194_13 U_194_14 U_194_15 U_194_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_195_1 :
    Uω (aρ 1) (bρ 1) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(1210887862743762534847 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11526008073845393 / 80000000000000000 : ℝ) ≤
      (-(1210887862743762534847 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11526008073845393 / 80000000000000000 : ℚ))
        (r' := (11526008073845393 / 10000000000000000 : ℚ))
        (U := (-(1210887862743762534847 / 625000000000000000000 : ℚ)))
        (U' := (88763100318737465153 / 625000000000000000000 : ℚ))
        3 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (9634306804209 / 64000000000000 : ℚ))
      (s := (360159699597173 / 2500000000000000 : ℚ))
      (q := (11526008073845393 / 80000000000000000 : ℚ))
      (U := (-(1210887862743762534847 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_195_2 :
    Uω (aρ 2) (bρ 2) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(977252689052743997793 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11330761183450273 / 80000000000000000 : ℝ) ≤
      (-(977252689052743997793 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11330761183450273 / 80000000000000000 : ℚ))
        (r' := (11330761183450273 / 10000000000000000 : ℚ))
        (U := (-(977252689052743997793 / 500000000000000000000 : ℚ)))
        (U' := (62468081397256002207 / 500000000000000000000 : ℚ))
        3 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (9634306804209 / 64000000000000 : ℚ))
      (s := (176949511037489 / 1250000000000000 : ℚ))
      (q := (11330761183450273 / 80000000000000000 : ℚ))
      (U := (-(977252689052743997793 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_195_3 :
    Uω (aρ 3) (bρ 3) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(9949861454974666734381 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10935937046850741 / 80000000000000000 : ℝ) ≤
      (-(9949861454974666734381 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10935937046850741 / 80000000000000000 : ℚ))
        (r' := (10935937046850741 / 10000000000000000 : ℚ))
        (U := (-(9949861454974666734381 / 5000000000000000000000 : ℚ)))
        (U' := (447346249525333265619 / 5000000000000000000000 : ℚ))
        3 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (9634306804209 / 64000000000000 : ℚ))
      (s := (1364286160500029 / 10000000000000000 : ℚ))
      (q := (10935937046850741 / 80000000000000000 : ℚ))
      (U := (-(9949861454974666734381 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_195_4 :
    Uω (aρ 4) (bρ 4) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(20532240139569703071389 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10265642295664161 / 80000000000000000 : ℝ) ≤
      (-(20532240139569703071389 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10265642295664161 / 80000000000000000 : ℚ))
        (r' := (10265642295664161 / 10000000000000000 : ℚ))
        (U := (-(20532240139569703071389 / 10000000000000000000000 : ℚ)))
        (U' := (262175269430296928611 / 10000000000000000000000 : ℚ))
        3 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (9634306804209 / 64000000000000 : ℚ))
      (s := (19921978965131 / 156250000000000 : ℚ))
      (q := (10265642295664161 / 80000000000000000 : ℚ))
      (U := (-(20532240139569703071389 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_195_5 :
    Uω (aρ 5) (bρ 5) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(21627709382413351683267 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9200480356847417 / 80000000000000000 : ℝ) ≤
      (-(21627709382413351683267 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9200480356847417 / 80000000000000000 : ℚ))
        (r' := (9200480356847417 / 5000000000000000 : ℚ))
        (U := (-(21627709382413351683267 / 10000000000000000000000 : ℚ)))
        (U' := (6098177829586648316733 / 10000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (9634306804209 / 64000000000000 : ℚ))
      (s := (563453044199599 / 5000000000000000 : ℚ))
      (q := (9200480356847417 / 80000000000000000 : ℚ))
      (U := (-(21627709382413351683267 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_195_6 :
    Uω (aρ 6) (bρ 6) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(5909163429288754127091 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1505196341988161 / 16000000000000000 : ℝ) ≤
      (-(5909163429288754127091 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1505196341988161 / 16000000000000000 : ℚ))
        (r' := (1505196341988161 / 1000000000000000 : ℚ))
        (U := (-(5909163429288754127091 / 2500000000000000000000 : ℚ)))
        (U' := (1022308373711245872909 / 2500000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (9634306804209 / 64000000000000 : ℚ))
      (s := (175104360362509 / 2000000000000000 : ℚ))
      (q := (1505196341988161 / 16000000000000000 : ℚ))
      (U := (-(5909163429288754127091 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_195_7 :
    Uω (aρ 7) (bρ 7) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(2911592179000382039081 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4351125095812169 / 80000000000000000 : ℝ) ≤
      (-(2911592179000382039081 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4351125095812169 / 80000000000000000 : ℚ))
        (r' := (4351125095812169 / 2500000000000000 : ℚ))
        (U := (-(2911592179000382039081 / 1000000000000000000000 : ℚ)))
        (U' := (554143722499617960919 / 1000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (9634306804209 / 64000000000000 : ℚ))
      (s := (152734514520193 / 5000000000000000 : ℚ))
      (q := (4351125095812169 / 80000000000000000 : ℚ))
      (U := (-(2911592179000382039081 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_195_8 :
    Uω (aρ 8) (bρ 8) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_195_9 :
    Uω (aρ 9) (bρ 9) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_195_10 :
    Uω (aρ 10) (bρ 10) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_195_11 :
    Uω (aρ 11) (bρ 11) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_195_12 :
    Uω (aρ 12) (bρ 12) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_195_13 :
    Uω (aρ 13) (bρ 13) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_195_14 :
    Uω (aρ 14) (bρ 14) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_195_15 :
    Uω (aρ 15) (bρ 15) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_195_16 :
    Uω (aρ 16) (bρ 16) (9634306804209 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_195 :
    Uρ (9634306804209 / 64000000000000 : ℝ) ≤
      (-(21516535824810612976769 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_195_1 U_195_2 U_195_3 U_195_4 U_195_5 U_195_6 U_195_7 U_195_8 U_195_9 U_195_10
    U_195_11 U_195_12 U_195_13 U_195_14 U_195_15 U_195_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
