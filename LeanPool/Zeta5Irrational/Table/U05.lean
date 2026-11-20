/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U05) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_64_1 :
    Uω (aρ 1) (bρ 1) (944711264583 / 32000000000000 : ℝ) ≤
      (-(18860822371165874400701 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (920088864570853 / 40000000000000000 : ℝ) ≤
      (-(18860822371165874400701 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (920088864570853 / 40000000000000000 : ℚ))
        (r' := (920088864570853 / 625000000000000 : ℚ))
        (U := (-(18860822371165874400701 / 5000000000000000000000 : ℚ)))
        (U' := (1933593037834125599299 / 5000000000000000000000 : ℚ))
        6 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (944711264583 / 32000000000000 : ℚ))
      (s := (229319380188239 / 10000000000000000 : ℚ))
      (q := (920088864570853 / 40000000000000000 : ℚ))
      (U := (-(18860822371165874400701 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_64_2 :
    Uω (aρ 2) (bρ 2) (944711264583 / 32000000000000 : ℝ) ≤
      (-(19517893536797811818607 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (806784040118343 / 40000000000000000 : ℝ) ≤
      (-(19517893536797811818607 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (806784040118343 / 40000000000000000 : ℚ))
        (r' := (806784040118343 / 625000000000000 : ℚ))
        (U := (-(19517893536797811818607 / 5000000000000000000000 : ℚ)))
        (U' := (1276521872202188181393 / 5000000000000000000000 : ℚ))
        6 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (944711264583 / 32000000000000 : ℚ))
      (s := (12277248779499 / 625000000000000 : ℚ))
      (q := (806784040118343 / 40000000000000000 : ℚ))
      (U := (-(19517893536797811818607 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_64_3 :
    Uω (aρ 3) (bρ 3) (944711264583 / 32000000000000 : ℝ) ≤
      (-(21660038294705195113549 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (525645521645909 / 40000000000000000 : ℝ) ≤
      (-(21660038294705195113549 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (525645521645909 / 40000000000000000 : ℚ))
        (r' := (525645521645909 / 312500000000000 : ℚ))
        (U := (-(21660038294705195113549 / 5000000000000000000000 : ℚ)))
        (U' := (2600113015794804886451 / 5000000000000000000000 : ℚ))
        7 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (944711264583 / 32000000000000 : ℚ))
      (s := (103262827585767 / 10000000000000000 : ℚ))
      (q := (525645521645909 / 40000000000000000 : ℚ))
      (U := (-(21660038294705195113549 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_64_4 :
    Uω (aρ 4) (bρ 4) (944711264583 / 32000000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_64_5 :
    Uω (aρ 5) (bρ 5) (944711264583 / 32000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_64_6 :
    Uω (aρ 6) (bρ 6) (944711264583 / 32000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_64_7 :
    Uω (aρ 7) (bρ 7) (944711264583 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_64_8 :
    Uω (aρ 8) (bρ 8) (944711264583 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_64_9 :
    Uω (aρ 9) (bρ 9) (944711264583 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_64_10 :
    Uω (aρ 10) (bρ 10) (944711264583 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_64_11 :
    Uω (aρ 11) (bρ 11) (944711264583 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_64_12 :
    Uω (aρ 12) (bρ 12) (944711264583 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_64_13 :
    Uω (aρ 13) (bρ 13) (944711264583 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_64_14 :
    Uω (aρ 14) (bρ 14) (944711264583 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_64_15 :
    Uω (aρ 15) (bρ 15) (944711264583 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_64_16 :
    Uω (aρ 16) (bρ 16) (944711264583 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_64 :
    Uρ (944711264583 / 32000000000000 : ℝ) ≤
      (-(5502100664475844411457 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_64_1 U_64_2 U_64_3 U_64_4 U_64_5 U_64_6 U_64_7 U_64_8 U_64_9 U_64_10 U_64_11
    U_64_12 U_64_13 U_64_14 U_64_15 U_64_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_65_1 :
    Uω (aρ 1) (bρ 1) (59550060209 / 2000000000000 : ℝ) ≤
      (-(37612010995240153131751 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (93023164149801 / 4000000000000000 : ℝ) ≤
      (-(37612010995240153131751 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (93023164149801 / 4000000000000000 : ℚ))
        (r' := (93023164149801 / 62500000000000 : ℚ))
        (U := (-(37612010995240153131751 / 10000000000000000000000 : ℚ)))
        (U' := (3976819822759846868249 / 10000000000000000000000 : ℚ))
        6 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (59550060209 / 2000000000000 : ℚ))
      (s := (46372547557801 / 2000000000000000 : ℚ))
      (q := (93023164149801 / 4000000000000000 : ℚ))
      (U := (-(37612010995240153131751 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_65_2 :
    Uω (aρ 2) (bρ 2) (59550060209 / 2000000000000 : ℝ) ≤
      (-(7781591291438441479693 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (408581704475813 / 20000000000000000 : ℝ) ≤
      (-(7781591291438441479693 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (408581704475813 / 20000000000000000 : ℚ))
        (r' := (408581704475813 / 312500000000000 : ℚ))
        (U := (-(7781591291438441479693 / 2000000000000000000000 : ℚ)))
        (U' := (536174872161558520307 / 2000000000000000000000 : ℚ))
        6 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (59550060209 / 2000000000000 : ℚ))
      (s := (199097634025813 / 10000000000000000 : ℚ))
      (q := (408581704475813 / 20000000000000000 : ℚ))
      (U := (-(7781591291438441479693 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_65_3 :
    Uω (aρ 3) (bρ 3) (59550060209 / 2000000000000 : ℝ) ≤
      (-(43079747104388786598999 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (134607839669749 / 10000000000000000 : ℝ) ≤
      (-(43079747104388786598999 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (134607839669749 / 10000000000000000 : ℚ))
        (r' := (134607839669749 / 78125000000000 : ℚ))
        (U := (-(43079747104388786598999 / 10000000000000000000000 : ℚ)))
        (U' := (5440555516611213401001 / 10000000000000000000000 : ℚ))
        7 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (59550060209 / 2000000000000 : ℚ))
      (s := (53563857619749 / 5000000000000000 : ℚ))
      (q := (134607839669749 / 10000000000000000 : ℚ))
      (U := (-(43079747104388786598999 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_65_4 :
    Uω (aρ 4) (bρ 4) (59550060209 / 2000000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_65_5 :
    Uω (aρ 5) (bρ 5) (59550060209 / 2000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_65_6 :
    Uω (aρ 6) (bρ 6) (59550060209 / 2000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_65_7 :
    Uω (aρ 7) (bρ 7) (59550060209 / 2000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_65_8 :
    Uω (aρ 8) (bρ 8) (59550060209 / 2000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_65_9 :
    Uω (aρ 9) (bρ 9) (59550060209 / 2000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_65_10 :
    Uω (aρ 10) (bρ 10) (59550060209 / 2000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_65_11 :
    Uω (aρ 11) (bρ 11) (59550060209 / 2000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_65_12 :
    Uω (aρ 12) (bρ 12) (59550060209 / 2000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_65_13 :
    Uω (aρ 13) (bρ 13) (59550060209 / 2000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_65_14 :
    Uω (aρ 14) (bρ 14) (59550060209 / 2000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_65_15 :
    Uω (aρ 15) (bρ 15) (59550060209 / 2000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_65_16 :
    Uω (aρ 16) (bρ 16) (59550060209 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_65 :
    Uρ (59550060209 / 2000000000000 : ℝ) ≤
      (-(13747632336952287678791 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_65_1 U_65_2 U_65_3 U_65_4 U_65_5 U_65_6 U_65_7 U_65_8 U_65_9 U_65_10 U_65_11
    U_65_12 U_65_13 U_65_14 U_65_15 U_65_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_66_1 :
    Uω (aρ 1) (bρ 1) (192178132421 / 6400000000000 : ℝ) ≤
      (-(37503573233468039420779 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (940373755235099 / 40000000000000000 : ℝ) ≤
      (-(37503573233468039420779 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (940373755235099 / 40000000000000000 : ℚ))
        (r' := (940373755235099 / 625000000000000 : ℚ))
        (U := (-(37503573233468039420779 / 10000000000000000000000 : ℚ)))
        (U' := (4085257584531960579221 / 10000000000000000000000 : ℚ))
        6 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (192178132421 / 6400000000000 : ℚ))
      (s := (234405763794737 / 10000000000000000 : ℚ))
      (q := (940373755235099 / 40000000000000000 : ℚ))
      (U := (-(37503573233468039420779 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_66_2 :
    Uω (aρ 2) (bρ 2) (192178132421 / 6400000000000 : ℝ) ≤
      (-(4847727796490385371113 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33101436143929 / 1600000000000000 : ℝ) ≤
      (-(4847727796490385371113 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (33101436143929 / 1600000000000000 : ℚ))
        (r' := (33101436143929 / 25000000000000 : ℚ))
        (U := (-(4847727796490385371113 / 1250000000000000000000 : ℚ)))
        (U' := (350876055759614628887 / 1250000000000000000000 : ℚ))
        6 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (192178132421 / 6400000000000 : ℚ))
      (s := (2017558504863 / 100000000000000 : ℚ))
      (q := (33101436143929 / 1600000000000000 : ℚ))
      (U := (-(4847727796490385371113 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_66_3 :
    Uω (aρ 3) (bρ 3) (192178132421 / 6400000000000 : ℝ) ≤
      (-(42847853324868564028227 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (551063142507483 / 40000000000000000 : ℝ) ≤
      (-(42847853324868564028227 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (551063142507483 / 40000000000000000 : ℚ))
        (r' := (551063142507483 / 312500000000000 : ℚ))
        (U := (-(42847853324868564028227 / 10000000000000000000000 : ℚ)))
        (U' := (5672449296131435971773 / 10000000000000000000000 : ℚ))
        7 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (192178132421 / 6400000000000 : ℚ))
      (s := (110915576290929 / 10000000000000000 : ℚ))
      (q := (551063142507483 / 40000000000000000 : ℚ))
      (U := (-(42847853324868564028227 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_66_4 :
    Uω (aρ 4) (bρ 4) (192178132421 / 6400000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_66_5 :
    Uω (aρ 5) (bρ 5) (192178132421 / 6400000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_66_6 :
    Uω (aρ 6) (bρ 6) (192178132421 / 6400000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_66_7 :
    Uω (aρ 7) (bρ 7) (192178132421 / 6400000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_66_8 :
    Uω (aρ 8) (bρ 8) (192178132421 / 6400000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_66_9 :
    Uω (aρ 9) (bρ 9) (192178132421 / 6400000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_66_10 :
    Uω (aρ 10) (bρ 10) (192178132421 / 6400000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_66_11 :
    Uω (aρ 11) (bρ 11) (192178132421 / 6400000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_66_12 :
    Uω (aρ 12) (bρ 12) (192178132421 / 6400000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_66_13 :
    Uω (aρ 13) (bρ 13) (192178132421 / 6400000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_66_14 :
    Uω (aρ 14) (bρ 14) (192178132421 / 6400000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_66_15 :
    Uω (aρ 15) (bρ 15) (192178132421 / 6400000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_66_16 :
    Uω (aρ 16) (bρ 16) (192178132421 / 6400000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_66 :
    Uρ (192178132421 / 6400000000000 : ℝ) ≤
      (-(13740225391654598492339 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_66_1 U_66_2 U_66_3 U_66_4 U_66_5 U_66_6 U_66_7 U_66_8 U_66_9 U_66_10 U_66_11
    U_66_12 U_66_13 U_66_14 U_66_15 U_66_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_67_1 :
    Uω (aρ 1) (bρ 1) (484490180433 / 16000000000000 : ℝ) ≤
      (-(37396305496047393699967 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (95051522713499 / 4000000000000000 : ℝ) ≤
      (-(37396305496047393699967 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (95051522713499 / 4000000000000000 : ℚ))
        (r' := (95051522713499 / 62500000000000 : ℚ))
        (U := (-(37396305496047393699967 / 10000000000000000000000 : ℚ)))
        (U' := (4192525321952606300033 / 10000000000000000000000 : ℚ))
        6 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (484490180433 / 16000000000000 : ℚ))
      (s := (23694846888187 / 1000000000000000 : ℚ))
      (q := (95051522713499 / 4000000000000000 : ℚ))
      (U := (-(37396305496047393699967 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_67_2 :
    Uω (aρ 2) (bρ 2) (484490180433 / 16000000000000 : ℝ) ≤
      (-(19328669154765280711259 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41895089611997 / 2000000000000000 : ℝ) ≤
      (-(19328669154765280711259 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41895089611997 / 2000000000000000 : ℚ))
        (r' := (41895089611997 / 31250000000000 : ℚ))
        (U := (-(19328669154765280711259 / 5000000000000000000000 : ℚ)))
        (U' := (1465746254234719288741 / 5000000000000000000000 : ℚ))
        6 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (484490180433 / 16000000000000 : ℚ))
      (s := (40882152788869 / 2000000000000000 : ℚ))
      (q := (41895089611997 / 2000000000000000 : ℚ))
      (U := (-(19328669154765280711259 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_67_3 :
    Uω (aρ 3) (bρ 3) (484490180433 / 16000000000000 : ℝ) ≤
      (-(1704947106755531654199 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8805564762709 / 625000000000000 : ℝ) ≤
      (-(1704947106755531654199 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8805564762709 / 625000000000000 : ℚ))
        (r' := (8805564762709 / 4882812500000 : ℚ))
        (U := (-(1704947106755531654199 / 400000000000000000000 : ℚ)))
        (U' := (235864998084468345801 / 400000000000000000000 : ℚ))
        7 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (484490180433 / 16000000000000 : ℚ))
      (s := (114634046581063 / 10000000000000000 : ℚ))
      (q := (8805564762709 / 625000000000000 : ℚ))
      (U := (-(1704947106755531654199 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_67_4 :
    Uω (aρ 4) (bρ 4) (484490180433 / 16000000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_67_5 :
    Uω (aρ 5) (bρ 5) (484490180433 / 16000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_67_6 :
    Uω (aρ 6) (bρ 6) (484490180433 / 16000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_67_7 :
    Uω (aρ 7) (bρ 7) (484490180433 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_67_8 :
    Uω (aρ 8) (bρ 8) (484490180433 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_67_9 :
    Uω (aρ 9) (bρ 9) (484490180433 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_67_10 :
    Uω (aρ 10) (bρ 10) (484490180433 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_67_11 :
    Uω (aρ 11) (bρ 11) (484490180433 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_67_12 :
    Uω (aρ 12) (bρ 12) (484490180433 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_67_13 :
    Uω (aρ 13) (bρ 13) (484490180433 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_67_14 :
    Uω (aρ 14) (bρ 14) (484490180433 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_67_15 :
    Uω (aρ 15) (bρ 15) (484490180433 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_67_16 :
    Uω (aρ 16) (bρ 16) (484490180433 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_67 :
    Uρ (484490180433 / 16000000000000 : ℝ) ≤
      (-(27466029197992934502529 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_67_1 U_67_2 U_67_3 U_67_4 U_67_5 U_67_6 U_67_7 U_67_8 U_67_9 U_67_10 U_67_11
    U_67_12 U_67_13 U_67_14 U_67_15 U_67_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_68_1 :
    Uω (aρ 1) (bρ 1) (977070059627 / 32000000000000 : ℝ) ≤
      (-(37290182662862082118669 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (960656077641081 / 40000000000000000 : ℝ) ≤
      (-(37290182662862082118669 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (960656077641081 / 40000000000000000 : ℚ))
        (r' := (960656077641081 / 625000000000000 : ℚ))
        (U := (-(37290182662862082118669 / 10000000000000000000000 : ℚ)))
        (U' := (4298648155137917881331 / 10000000000000000000000 : ℚ))
        6 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (977070059627 / 32000000000000 : ℚ))
      (s := (239490863272103 / 10000000000000000 : ℚ))
      (q := (960656077641081 / 40000000000000000 : ℚ))
      (U := (-(37290182662862082118669 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_68_2 :
    Uω (aρ 2) (bρ 2) (977070059627 / 32000000000000 : ℝ) ≤
      (-(19267229861265618418229 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (848261328979417 / 40000000000000000 : ℝ) ≤
      (-(19267229861265618418229 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (848261328979417 / 40000000000000000 : ℚ))
        (r' := (848261328979417 / 625000000000000 : ℚ))
        (U := (-(19267229861265618418229 / 5000000000000000000000 : ℚ)))
        (U' := (1527185547734381581771 / 5000000000000000000000 : ℚ))
        6 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (977070059627 / 32000000000000 : ℚ))
      (s := (207062501451271 / 10000000000000000 : ℚ))
      (q := (848261328979417 / 40000000000000000 : ℚ))
      (U := (-(19267229861265618418229 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_68_3 :
    Uω (aρ 3) (bρ 3) (977070059627 / 32000000000000 : ℝ) ≤
      (-(42406599719954955895771 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (575923453871657 / 40000000000000000 : ℝ) ≤
      (-(42406599719954955895771 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (575923453871657 / 40000000000000000 : ℚ))
        (r' := (575923453871657 / 312500000000000 : ℚ))
        (U := (-(42406599719954955895771 / 10000000000000000000000 : ℚ)))
        (U' := (6113702901045044104229 / 10000000000000000000000 : ℚ))
        7 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (977070059627 / 32000000000000 : ℚ))
      (s := (118289670247391 / 10000000000000000 : ℚ))
      (q := (575923453871657 / 40000000000000000 : ℚ))
      (U := (-(42406599719954955895771 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_68_4 :
    Uω (aρ 4) (bρ 4) (977070059627 / 32000000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_68_5 :
    Uω (aρ 5) (bρ 5) (977070059627 / 32000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_68_6 :
    Uω (aρ 6) (bρ 6) (977070059627 / 32000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_68_7 :
    Uω (aρ 7) (bρ 7) (977070059627 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_68_8 :
    Uω (aρ 8) (bρ 8) (977070059627 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_68_9 :
    Uω (aρ 9) (bρ 9) (977070059627 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_68_10 :
    Uω (aρ 10) (bρ 10) (977070059627 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_68_11 :
    Uω (aρ 11) (bρ 11) (977070059627 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_68_12 :
    Uω (aρ 12) (bρ 12) (977070059627 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_68_13 :
    Uω (aρ 13) (bρ 13) (977070059627 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_68_14 :
    Uω (aρ 14) (bρ 14) (977070059627 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_68_15 :
    Uω (aρ 15) (bρ 15) (977070059627 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_68_16 :
    Uω (aρ 16) (bρ 16) (977070059627 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_68 :
    Uρ (977070059627 / 32000000000000 : ℝ) ≤
      (-(27451971703722815927747 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_68_1 U_68_2 U_68_3 U_68_4 U_68_5 U_68_6 U_68_7 U_68_8 U_68_9 U_68_10 U_68_11
    U_68_12 U_68_13 U_68_14 U_68_15 U_68_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_69_1 :
    Uω (aρ 1) (bρ 1) (246289939597 / 8000000000000 : ℝ) ≤
      (-(37185180418532968481481 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (485398163167677 / 20000000000000000 : ℝ) ≤
      (-(37185180418532968481481 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (485398163167677 / 20000000000000000 : ℚ))
        (r' := (485398163167677 / 312500000000000 : ℚ))
        (U := (-(37185180418532968481481 / 10000000000000000000000 : ℚ)))
        (U' := (4403650399467031518519 / 10000000000000000000000 : ℚ))
        6 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (246289939597 / 8000000000000 : ℚ))
      (s := (242032956756427 / 10000000000000000 : ℚ))
      (q := (485398163167677 / 20000000000000000 : ℚ))
      (U := (-(37185180418532968481481 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_69_2 :
    Uω (aρ 2) (bρ 2) (246289939597 / 8000000000000 : ℝ) ≤
      (-(4801642989010586665173 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17172295095413 / 800000000000000 : ℝ) ≤
      (-(4801642989010586665173 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17172295095413 / 800000000000000 : ℚ))
        (r' := (17172295095413 / 12500000000000 : ℚ))
        (U := (-(4801642989010586665173 / 1250000000000000000000 : ℚ)))
        (U' := (396960863239413334827 / 1250000000000000000000 : ℚ))
        6 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (246289939597 / 8000000000000 : ℚ))
      (s := (8388447339363 / 400000000000000 : ℚ))
      (q := (17172295095413 / 800000000000000 : ℚ))
      (U := (-(4801642989010586665173 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_69_3 :
    Uω (aρ 3) (bρ 3) (246289939597 / 8000000000000 : ℝ) ≤
      (-(10549019659401938900341 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (294088189591647 / 20000000000000000 : ℝ) ≤
      (-(10549019659401938900341 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (294088189591647 / 20000000000000000 : ℚ))
        (r' := (294088189591647 / 156250000000000 : ℚ))
        (U := (-(10549019659401938900341 / 2500000000000000000000 : ℚ)))
        (U' := (1581055995848061099659 / 2500000000000000000000 : ℚ))
        7 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (246289939597 / 8000000000000 : ℚ))
      (s := (121888102040397 / 10000000000000000 : ℚ))
      (q := (294088189591647 / 20000000000000000 : ℚ))
      (U := (-(10549019659401938900341 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_69_4 :
    Uω (aρ 4) (bρ 4) (246289939597 / 8000000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_69_5 :
    Uω (aρ 5) (bρ 5) (246289939597 / 8000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_69_6 :
    Uω (aρ 6) (bρ 6) (246289939597 / 8000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_69_7 :
    Uω (aρ 7) (bρ 7) (246289939597 / 8000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_69_8 :
    Uω (aρ 8) (bρ 8) (246289939597 / 8000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_69_9 :
    Uω (aρ 9) (bρ 9) (246289939597 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_69_10 :
    Uω (aρ 10) (bρ 10) (246289939597 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_69_11 :
    Uω (aρ 11) (bρ 11) (246289939597 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_69_12 :
    Uω (aρ 12) (bρ 12) (246289939597 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_69_13 :
    Uω (aρ 13) (bρ 13) (246289939597 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_69_14 :
    Uω (aρ 14) (bρ 14) (246289939597 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_69_15 :
    Uω (aρ 15) (bρ 15) (246289939597 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_69_16 :
    Uω (aρ 16) (bρ 16) (246289939597 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_69 :
    Uρ (246289939597 / 8000000000000 : ℝ) ≤
      (-(27438253565757300111681 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_69_1 U_69_2 U_69_3 U_69_4 U_69_5 U_69_6 U_69_7 U_69_8 U_69_9 U_69_10 U_69_11
    U_69_12 U_69_13 U_69_14 U_69_15 U_69_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_70_1 :
    Uω (aρ 1) (bρ 1) (100133915591 / 3200000000000 : ℝ) ≤
      (-(7395688851059352324481 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (247768773144139 / 10000000000000000 : ℝ) ≤
      (-(7395688851059352324481 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (247768773144139 / 10000000000000000 : ℚ))
        (r' := (247768773144139 / 156250000000000 : ℚ))
        (U := (-(7395688851059352324481 / 2000000000000000000000 : ℚ)))
        (U' := (922077312540647675519 / 2000000000000000000000 : ℚ))
        6 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (100133915591 / 3200000000000 : ℚ))
      (s := (247116278151403 / 10000000000000000 : ℚ))
      (q := (247768773144139 / 10000000000000000 : ℚ))
      (U := (-(7395688851059352324481 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_70_2 :
    Uω (aρ 2) (bρ 2) (100133915591 / 3200000000000 : ℝ) ≤
      (-(3817503845189056183093 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (109913022081481 / 5000000000000000 : ℝ) ≤
      (-(3817503845189056183093 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (109913022081481 / 5000000000000000 : ℚ))
        (r' := (109913022081481 / 78125000000000 : ℚ))
        (U := (-(3817503845189056183093 / 1000000000000000000000 : ℚ)))
        (U' := (341379236610943816907 / 1000000000000000000000 : ℚ))
        6 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (100133915591 / 3200000000000 : ℚ))
      (s := (214999832699049 / 10000000000000000 : ℚ))
      (q := (109913022081481 / 5000000000000000 : ℚ))
      (U := (-(3817503845189056183093 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_70_3 :
    Uω (aρ 3) (bρ 3) (100133915591 / 3200000000000 : ℝ) ≤
      (-(2612053898144625343839 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (76547154724709 / 5000000000000000 : ℝ) ≤
      (-(2612053898144625343839 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (76547154724709 / 5000000000000000 : ℚ))
        (r' := (76547154724709 / 39062500000000 : ℚ))
        (U := (-(2612053898144625343839 / 625000000000000000000 : ℚ)))
        (U' := (420465015667874656161 / 625000000000000000000 : ℚ))
        7 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (100133915591 / 3200000000000 : ℚ))
      (s := (128932469621961 / 10000000000000000 : ℚ))
      (q := (76547154724709 / 5000000000000000 : ℚ))
      (U := (-(2612053898144625343839 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_70_4 :
    Uω (aρ 4) (bρ 4) (100133915591 / 3200000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_70_5 :
    Uω (aρ 5) (bρ 5) (100133915591 / 3200000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_70_6 :
    Uω (aρ 6) (bρ 6) (100133915591 / 3200000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_70_7 :
    Uω (aρ 7) (bρ 7) (100133915591 / 3200000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_70_8 :
    Uω (aρ 8) (bρ 8) (100133915591 / 3200000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_70_9 :
    Uω (aρ 9) (bρ 9) (100133915591 / 3200000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_70_10 :
    Uω (aρ 10) (bρ 10) (100133915591 / 3200000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_70_11 :
    Uω (aρ 11) (bρ 11) (100133915591 / 3200000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_70_12 :
    Uω (aρ 12) (bρ 12) (100133915591 / 3200000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_70_13 :
    Uω (aρ 13) (bρ 13) (100133915591 / 3200000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_70_14 :
    Uω (aρ 14) (bρ 14) (100133915591 / 3200000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_70_15 :
    Uω (aρ 15) (bρ 15) (100133915591 / 3200000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_70_16 :
    Uω (aρ 16) (bρ 16) (100133915591 / 3200000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_70 :
    Uρ (100133915591 / 3200000000000 : ℝ) ≤
      (-(685293759890628417919 / 250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_70_1 U_70_2 U_70_3 U_70_4 U_70_5 U_70_6 U_70_7 U_70_8 U_70_9 U_70_10 U_70_11
    U_70_12 U_70_13 U_70_14 U_70_15 U_70_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_71_1 :
    Uω (aρ 1) (bρ 1) (127189819179 / 4000000000000 : ℝ) ≤
      (-(18387958661588722880311 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (505675833464109 / 20000000000000000 : ℝ) ≤
      (-(18387958661588722880311 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (505675833464109 / 20000000000000000 : ℚ))
        (r' := (505675833464109 / 312500000000000 : ℚ))
        (U := (-(18387958661588722880311 / 5000000000000000000000 : ℚ)))
        (U' := (2406456747411277119689 / 5000000000000000000000 : ℚ))
        6 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (127189819179 / 4000000000000 : ℚ))
      (s := (252198503601609 / 10000000000000000 : ℚ))
      (q := (505675833464109 / 20000000000000000 : ℚ))
      (U := (-(18387958661588722880311 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_71_2 :
    Uω (aρ 2) (bρ 2) (127189819179 / 4000000000000 : ℝ) ≤
      (-(7588542707518441531123 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (224992938362713 / 10000000000000000 : ℝ) ≤
      (-(7588542707518441531123 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (224992938362713 / 10000000000000000 : ℚ))
        (r' := (224992938362713 / 156250000000000 : ℚ))
        (U := (-(7588542707518441531123 / 2000000000000000000000 : ℚ)))
        (U' := (729223456081558468877 / 2000000000000000000000 : ℚ))
        6 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (127189819179 / 4000000000000 : ℚ))
      (s := (110138779686463 / 5000000000000000 : ℚ))
      (q := (224992938362713 / 10000000000000000 : ℚ))
      (U := (-(7588542707518441531123 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_71_3 :
    Uω (aρ 3) (bρ 3) (127189819179 / 4000000000000 : ℝ) ≤
      (-(1656433616878713809077 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (79527998946249 / 5000000000000000 : ℝ) ≤
      (-(1656433616878713809077 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (79527998946249 / 5000000000000000 : ℚ))
        (r' := (79527998946249 / 78125000000000 : ℚ))
        (U := (-(1656433616878713809077 / 400000000000000000000 : ℚ)))
        (U' := (7119615841286190923 / 400000000000000000000 : ℚ))
        6 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (127189819179 / 4000000000000 : ℚ))
      (s := (4243743274453 / 312500000000000 : ℚ))
      (q := (79527998946249 / 5000000000000000 : ℚ))
      (U := (-(1656433616878713809077 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_71_4 :
    Uω (aρ 4) (bρ 4) (127189819179 / 4000000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_71_5 :
    Uω (aρ 5) (bρ 5) (127189819179 / 4000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_71_6 :
    Uω (aρ 6) (bρ 6) (127189819179 / 4000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_71_7 :
    Uω (aρ 7) (bρ 7) (127189819179 / 4000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_71_8 :
    Uω (aρ 8) (bρ 8) (127189819179 / 4000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_71_9 :
    Uω (aρ 9) (bρ 9) (127189819179 / 4000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_71_10 :
    Uω (aρ 10) (bρ 10) (127189819179 / 4000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_71_11 :
    Uω (aρ 11) (bρ 11) (127189819179 / 4000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_71_12 :
    Uω (aρ 12) (bρ 12) (127189819179 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_71_13 :
    Uω (aρ 13) (bρ 13) (127189819179 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_71_14 :
    Uω (aρ 14) (bρ 14) (127189819179 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_71_15 :
    Uω (aρ 15) (bρ 15) (127189819179 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_71_16 :
    Uω (aρ 16) (bρ 16) (127189819179 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_71 :
    Uρ (127189819179 / 4000000000000 : ℝ) ≤
      (-(13693185907714144032147 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_71_1 U_71_2 U_71_3 U_71_4 U_71_5 U_71_6 U_71_7 U_71_8 U_71_9 U_71_10 U_71_11
    U_71_12 U_71_13 U_71_14 U_71_15 U_71_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_72_1 :
    Uω (aρ 1) (bρ 1) (516848975477 / 16000000000000 : ℝ) ≤
      (-(36577430804916419226009 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (257906544821033 / 10000000000000000 : ℝ) ≤
      (-(36577430804916419226009 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (257906544821033 / 10000000000000000 : ℚ))
        (r' := (257906544821033 / 156250000000000 : ℚ))
        (U := (-(36577430804916419226009 / 10000000000000000000000 : ℚ)))
        (U' := (5011400013083580773991 / 10000000000000000000000 : ℚ))
        6 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (516848975477 / 16000000000000 : ℚ))
      (s := (257279698053941 / 10000000000000000 : ℚ))
      (q := (257906544821033 / 10000000000000000 : ℚ))
      (U := (-(36577430804916419226009 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_72_2 :
    Uω (aρ 2) (bρ 2) (516848975477 / 16000000000000 : ℝ) ≤
      (-(9428971103386477538939 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (460309509343253 / 20000000000000000 : ℝ) ≤
      (-(9428971103386477538939 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (460309509343253 / 20000000000000000 : ℚ))
        (r' := (460309509343253 / 312500000000000 : ℚ))
        (U := (-(9428971103386477538939 / 2500000000000000000000 : ℚ)))
        (U' := (968236601113522461061 / 2500000000000000000000 : ℚ))
        6 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (516848975477 / 16000000000000 : ℚ))
      (s := (28193141283141 / 1250000000000000 : ℚ))
      (q := (460309509343253 / 20000000000000000 : ℚ))
      (U := (-(9428971103386477538939 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_72_3 :
    Uω (aρ 3) (bρ 3) (516848975477 / 16000000000000 : ℝ) ≤
      (-(41047467247559701779401 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (65976783420521 / 4000000000000000 : ℝ) ≤
      (-(41047467247559701779401 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (65976783420521 / 4000000000000000 : ℚ))
        (r' := (65976783420521 / 62500000000000 : ℚ))
        (U := (-(41047467247559701779401 / 10000000000000000000000 : ℚ)))
        (U' := (541363570440298220599 / 10000000000000000000000 : ℚ))
        6 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (516848975477 / 16000000000000 : ℚ))
      (s := (1781445554681 / 125000000000000 : ℚ))
      (q := (65976783420521 / 4000000000000000 : ℚ))
      (U := (-(41047467247559701779401 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_72_4 :
    Uω (aρ 4) (bρ 4) (516848975477 / 16000000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_72_5 :
    Uω (aρ 5) (bρ 5) (516848975477 / 16000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_72_6 :
    Uω (aρ 6) (bρ 6) (516848975477 / 16000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_72_7 :
    Uω (aρ 7) (bρ 7) (516848975477 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_72_8 :
    Uω (aρ 8) (bρ 8) (516848975477 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_72_9 :
    Uω (aρ 9) (bρ 9) (516848975477 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_72_10 :
    Uω (aρ 10) (bρ 10) (516848975477 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_72_11 :
    Uω (aρ 11) (bρ 11) (516848975477 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_72_12 :
    Uω (aρ 12) (bρ 12) (516848975477 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_72_13 :
    Uω (aρ 13) (bρ 13) (516848975477 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_72_14 :
    Uω (aρ 14) (bρ 14) (516848975477 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_72_15 :
    Uω (aρ 15) (bρ 15) (516848975477 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_72_16 :
    Uω (aρ 16) (bρ 16) (516848975477 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_72 :
    Uρ (516848975477 / 16000000000000 : ℝ) ≤
      (-(273619983663501507283 / 100000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_72_1 U_72_2 U_72_3 U_72_4 U_72_5 U_72_6 U_72_7 U_72_8 U_72_9 U_72_10 U_72_11
    U_72_12 U_72_13 U_72_14 U_72_15 U_72_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_73_1 :
    Uω (aρ 1) (bρ 1) (262469337119 / 8000000000000 : ℝ) ≤
      (-(1455313035456262498261 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (262974687362493 / 10000000000000000 : ℝ) ≤
      (-(1455313035456262498261 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (262974687362493 / 10000000000000000 : ℚ))
        (r' := (262974687362493 / 156250000000000 : ℚ))
        (U := (-(1455313035456262498261 / 400000000000000000000 : ℚ)))
        (U' := (208240197263737501739 / 400000000000000000000 : ℚ))
        6 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (262469337119 / 8000000000000 : ℚ))
      (s := (65589980352809 / 2500000000000000 : ℚ))
      (q := (262974687362493 / 10000000000000000 : ℚ))
      (U := (-(1455313035456262498261 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_73_2 :
    Uω (aρ 2) (bρ 2) (262469337119 / 8000000000000 : ℝ) ≤
      (-(9373571884890926660439 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (235311840764937 / 10000000000000000 : ℝ) ≤
      (-(9373571884890926660439 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (235311840764937 / 10000000000000000 : ℚ))
        (r' := (235311840764937 / 156250000000000 : ℚ))
        (U := (-(9373571884890926660439 / 2500000000000000000000 : ℚ)))
        (U' := (1023635819609073339561 / 2500000000000000000000 : ℚ))
        6 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (262469337119 / 8000000000000 : ℚ))
      (s := (57700810181531 / 2500000000000000 : ℚ))
      (q := (235311840764937 / 10000000000000000 : ℚ))
      (U := (-(9373571884890926660439 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_73_3 :
    Uω (aρ 3) (bρ 3) (262469337119 / 8000000000000 : ℝ) ≤
      (-(8140134214423032915029 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (341524850067617 / 20000000000000000 : ℝ) ≤
      (-(8140134214423032915029 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (341524850067617 / 20000000000000000 : ℚ))
        (r' := (341524850067617 / 312500000000000 : ℚ))
        (U := (-(8140134214423032915029 / 2000000000000000000000 : ℚ)))
        (U' := (177631949176967084971 / 2000000000000000000000 : ℚ))
        6 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (262469337119 / 8000000000000 : ℚ))
      (s := (149100515613867 / 10000000000000000 : ℚ))
      (q := (341524850067617 / 20000000000000000 : ℚ))
      (U := (-(8140134214423032915029 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_73_4 :
    Uω (aρ 4) (bρ 4) (262469337119 / 8000000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_73_5 :
    Uω (aρ 5) (bρ 5) (262469337119 / 8000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_73_6 :
    Uω (aρ 6) (bρ 6) (262469337119 / 8000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_73_7 :
    Uω (aρ 7) (bρ 7) (262469337119 / 8000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_73_8 :
    Uω (aρ 8) (bρ 8) (262469337119 / 8000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_73_9 :
    Uω (aρ 9) (bρ 9) (262469337119 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_73_10 :
    Uω (aρ 10) (bρ 10) (262469337119 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_73_11 :
    Uω (aρ 11) (bρ 11) (262469337119 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_73_12 :
    Uω (aρ 12) (bρ 12) (262469337119 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_73_13 :
    Uω (aρ 13) (bρ 13) (262469337119 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_73_14 :
    Uω (aρ 14) (bρ 14) (262469337119 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_73_15 :
    Uω (aρ 15) (bρ 15) (262469337119 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_73_16 :
    Uω (aρ 16) (bρ 16) (262469337119 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_73 :
    Uρ (262469337119 / 8000000000000 : ℝ) ≤
      (-(27338531661035234682497 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_73_1 U_73_2 U_73_3 U_73_4 U_73_5 U_73_6 U_73_7 U_73_8 U_73_9 U_73_10 U_73_11
    U_73_12 U_73_13 U_73_14 U_73_15 U_73_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_74_1 :
    Uω (aρ 1) (bρ 1) (6763975897 / 200000000000 : ℝ) ≤
      (-(36004671011973596596201 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13655481220777 / 500000000000000 : ℝ) ≤
      (-(36004671011973596596201 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13655481220777 / 500000000000000 : ℚ))
        (r' := (13655481220777 / 7812500000000 : ℚ))
        (U := (-(36004671011973596596201 / 10000000000000000000000 : ℚ)))
        (U' := (5584159806026403403799 / 10000000000000000000000 : ℚ))
        6 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (6763975897 / 200000000000 : ℚ))
      (s := (1703235450413 / 62500000000000 : ℚ))
      (q := (13655481220777 / 500000000000000 : ℚ))
      (U := (-(36004671011973596596201 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_74_2 :
    Uω (aρ 2) (bρ 2) (6763975897 / 200000000000 : ℝ) ≤
      (-(18532915025022758161627 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30701632335961 / 1250000000000000 : ℝ) ≤
      (-(18532915025022758161627 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30701632335961 / 1250000000000000 : ℚ))
        (r' := (30701632335961 / 19531250000000 : ℚ))
        (U := (-(18532915025022758161627 / 5000000000000000000000 : ℚ)))
        (U' := (2261500383977241838373 / 5000000000000000000000 : ℚ))
        6 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (6763975897 / 200000000000 : ℚ))
      (s := (30161694140047 / 1250000000000000 : ℚ))
      (q := (30701632335961 / 1250000000000000 : ℚ))
      (U := (-(18532915025022758161627 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_74_3 :
    Uω (aρ 3) (bρ 3) (6763975897 / 200000000000 : ℝ) ≤
      (-(801004622320808228037 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (364477360851279 / 20000000000000000 : ℝ) ≤
      (-(801004622320808228037 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (364477360851279 / 20000000000000000 : ℚ))
        (r' := (364477360851279 / 312500000000000 : ℚ))
        (U := (-(801004622320808228037 / 200000000000000000000 : ℚ)))
        (U' := (30771994039191771963 / 200000000000000000000 : ℚ))
        6 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (6763975897 / 200000000000 : ℚ))
      (s := (161940902946279 / 10000000000000000 : ℚ))
      (q := (364477360851279 / 20000000000000000 : ℚ))
      (U := (-(801004622320808228037 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_74_4 :
    Uω (aρ 4) (bρ 4) (6763975897 / 200000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_74_5 :
    Uω (aρ 5) (bρ 5) (6763975897 / 200000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_74_6 :
    Uω (aρ 6) (bρ 6) (6763975897 / 200000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_74_7 :
    Uω (aρ 7) (bρ 7) (6763975897 / 200000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_74_8 :
    Uω (aρ 8) (bρ 8) (6763975897 / 200000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_74_9 :
    Uω (aρ 9) (bρ 9) (6763975897 / 200000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_74_10 :
    Uω (aρ 10) (bρ 10) (6763975897 / 200000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_74_11 :
    Uω (aρ 11) (bρ 11) (6763975897 / 200000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_74_12 :
    Uω (aρ 12) (bρ 12) (6763975897 / 200000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_74_13 :
    Uω (aρ 13) (bρ 13) (6763975897 / 200000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_74_14 :
    Uω (aρ 14) (bρ 14) (6763975897 / 200000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_74_15 :
    Uω (aρ 15) (bρ 15) (6763975897 / 200000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_74_16 :
    Uω (aρ 16) (bρ 16) (6763975897 / 200000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_74 :
    Uρ (6763975897 / 200000000000 : ℝ) ≤
      (-(27294001523746580880381 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_74_1 U_74_2 U_74_3 U_74_4 U_74_5 U_74_6 U_74_7 U_74_8 U_74_9 U_74_10 U_74_11
    U_74_12 U_74_13 U_74_14 U_74_15 U_74_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_75_1 :
    Uω (aρ 1) (bρ 1) (278648734641 / 8000000000000 : ℝ) ≤
      (-(35640354467824444665873 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (113297170223489 / 4000000000000000 : ℝ) ≤
      (-(35640354467824444665873 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (113297170223489 / 4000000000000000 : ℚ))
        (r' := (113297170223489 / 62500000000000 : ℚ))
        (U := (-(35640354467824444665873 / 10000000000000000000000 : ℚ)))
        (U' := (5948476350175555334127 / 10000000000000000000000 : ℚ))
        6 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (278648734641 / 8000000000000 : ℚ))
      (s := (56534430180239 / 2000000000000000 : ℚ))
      (q := (113297170223489 / 4000000000000000 : ℚ))
      (U := (-(35640354467824444665873 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_75_2 :
    Uω (aρ 2) (bρ 2) (278648734641 / 8000000000000 : ℝ) ≤
      (-(36655583055019159093507 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (511797605676663 / 20000000000000000 : ℝ) ≤
      (-(36655583055019159093507 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (511797605676663 / 20000000000000000 : ℚ))
        (r' := (511797605676663 / 312500000000000 : ℚ))
        (U := (-(36655583055019159093507 / 10000000000000000000000 : ℚ)))
        (U' := (4933247762980840906493 / 10000000000000000000000 : ℚ))
        6 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (278648734641 / 8000000000000 : ℚ))
      (s := (251752917970413 / 10000000000000000 : ℚ))
      (q := (511797605676663 / 20000000000000000 : ℚ))
      (U := (-(36655583055019159093507 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_75_3 :
    Uω (aρ 3) (bρ 3) (278648734641 / 8000000000000 : ℝ) ≤
      (-(19724394162041300263193 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (387071224436723 / 20000000000000000 : ℝ) ≤
      (-(19724394162041300263193 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (387071224436723 / 20000000000000000 : ℚ))
        (r' := (387071224436723 / 312500000000000 : ℚ))
        (U := (-(19724394162041300263193 / 5000000000000000000000 : ℚ)))
        (U' := (1070021246958699736807 / 5000000000000000000000 : ℚ))
        6 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (278648734641 / 8000000000000 : ℚ))
      (s := (174422643080473 / 10000000000000000 : ℚ))
      (q := (387071224436723 / 20000000000000000 : ℚ))
      (U := (-(19724394162041300263193 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_75_4 :
    Uω (aρ 4) (bρ 4) (278648734641 / 8000000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

lemma U_75_5 :
    Uω (aρ 5) (bρ 5) (278648734641 / 8000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_5]) (by norm_num [bρ_5])]; exact Lmid_5

lemma U_75_6 :
    Uω (aρ 6) (bρ 6) (278648734641 / 8000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

lemma U_75_7 :
    Uω (aρ 7) (bρ 7) (278648734641 / 8000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_75_8 :
    Uω (aρ 8) (bρ 8) (278648734641 / 8000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_75_9 :
    Uω (aρ 9) (bρ 9) (278648734641 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_75_10 :
    Uω (aρ 10) (bρ 10) (278648734641 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_75_11 :
    Uω (aρ 11) (bρ 11) (278648734641 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_75_12 :
    Uω (aρ 12) (bρ 12) (278648734641 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_75_13 :
    Uω (aρ 13) (bρ 13) (278648734641 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_75_14 :
    Uω (aρ 14) (bρ 14) (278648734641 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_75_15 :
    Uω (aρ 15) (bρ 15) (278648734641 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_75_16 :
    Uω (aρ 16) (bρ 16) (278648734641 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_75 :
    Uρ (278648734641 / 8000000000000 : ℝ) ≤
      (-(27252257261802753728461 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_75_1 U_75_2 U_75_3 U_75_4 U_75_5 U_75_6 U_75_7 U_75_8 U_75_9 U_75_10 U_75_11
    U_75_12 U_75_13 U_75_14 U_75_15 U_75_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
