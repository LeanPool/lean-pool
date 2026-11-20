/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U23) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_280_1 :
    Uω (aρ 1) (bρ 1) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(595649490681648873547 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9022809198209127 / 40000000000000000 : ℝ) ≤
      (-(595649490681648873547 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9022809198209127 / 40000000000000000 : ℚ))
        (r' := (9022809198209127 / 5000000000000000 : ℚ))
        (U := (-(595649490681648873547 / 400000000000000000000 : ℚ)))
        (U' := (236127125678351126453 / 400000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (7424867802851 / 32000000000000 : ℚ))
      (s := (1127815314399313 / 5000000000000000 : ℚ))
      (q := (9022809198209127 / 40000000000000000 : ℚ))
      (U := (-(595649490681648873547 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_280_2 :
    Uω (aρ 2) (bρ 2) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(14998978531214893129037 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1785223625503007 / 8000000000000000 : ℝ) ≤
      (-(14998978531214893129037 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1785223625503007 / 8000000000000000 : ℚ))
        (r' := (1785223625503007 / 1000000000000000 : ℚ))
        (U := (-(14998978531214893129037 / 10000000000000000000000 : ℚ)))
        (U' := (5795436877785106870963 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (7424867802851 / 32000000000000 : ℚ))
      (s := (111552705298079 / 500000000000000 : ℚ))
      (q := (1785223625503007 / 8000000000000000 : ℚ))
      (U := (-(14998978531214893129037 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_280_3 :
    Uω (aρ 3) (bρ 3) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(3804810672586354525097 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8731657237410283 / 40000000000000000 : ℝ) ≤
      (-(3804810672586354525097 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8731657237410283 / 40000000000000000 : ℚ))
        (r' := (8731657237410283 / 5000000000000000 : ℚ))
        (U := (-(3804810672586354525097 / 2500000000000000000000 : ℚ)))
        (U' := (1393793179663645474903 / 2500000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (7424867802851 / 32000000000000 : ℚ))
      (s := (545304941814801 / 2500000000000000 : ℚ))
      (q := (8731657237410283 / 40000000000000000 : ℚ))
      (U := (-(3804810672586354525097 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_280_4 :
    Uω (aρ 4) (bρ 4) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(15600250780916396574767 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8405232051652987 / 40000000000000000 : ℝ) ≤
      (-(15600250780916396574767 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8405232051652987 / 40000000000000000 : ℚ))
        (r' := (8405232051652987 / 5000000000000000 : ℚ))
        (U := (-(15600250780916396574767 / 10000000000000000000000 : ℚ)))
        (U' := (5194164628083603425233 / 10000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (7424867802851 / 32000000000000 : ℚ))
      (s := (524075338861389 / 2500000000000000 : ℚ))
      (q := (8405232051652987 / 40000000000000000 : ℚ))
      (U := (-(15600250780916396574767 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_280_5 :
    Uω (aρ 5) (bρ 5) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(16221992242274015104961 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7898558141701877 / 40000000000000000 : ℝ) ≤
      (-(16221992242274015104961 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7898558141701877 / 40000000000000000 : ℚ))
        (r' := (7898558141701877 / 5000000000000000 : ℚ))
        (U := (-(16221992242274015104961 / 10000000000000000000000 : ℚ)))
        (U' := (4572423166725984895039 / 10000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (7424867802851 / 32000000000000 : ℚ))
      (s := (1961154319805001 / 10000000000000000 : ℚ))
      (q := (7898558141701877 / 40000000000000000 : ℚ))
      (U := (-(16221992242274015104961 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_280_6 :
    Uω (aρ 6) (bρ 6) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(17223054302843945077151 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7146151950218381 / 40000000000000000 : ℝ) ≤
      (-(17223054302843945077151 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7146151950218381 / 40000000000000000 : ℚ))
        (r' := (7146151950218381 / 5000000000000000 : ℚ))
        (U := (-(17223054302843945077151 / 10000000000000000000000 : ℚ)))
        (U' := (3571361106156054922849 / 10000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (7424867802851 / 32000000000000 : ℚ))
      (s := (1752191599203253 / 10000000000000000 : ℚ))
      (q := (7146151950218381 / 40000000000000000 : ℚ))
      (U := (-(17223054302843945077151 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_280_7 :
    Uω (aρ 7) (bρ 7) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(3779062541338344784579 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6045705484189657 / 40000000000000000 : ℝ) ≤
      (-(3779062541338344784579 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6045705484189657 / 40000000000000000 : ℚ))
        (r' := (6045705484189657 / 5000000000000000 : ℚ))
        (U := (-(3779062541338344784579 / 2000000000000000000000 : ℚ)))
        (U' := (379820540461655215421 / 2000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (7424867802851 / 32000000000000 : ℚ))
      (s := (1425629746948891 / 10000000000000000 : ℚ))
      (q := (6045705484189657 / 40000000000000000 : ℚ))
      (U := (-(3779062541338344784579 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_280_8 :
    Uω (aρ 8) (bρ 8) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(11127371186098035850237 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4320647243227353 / 40000000000000000 : ℝ) ≤
      (-(11127371186098035850237 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4320647243227353 / 40000000000000000 : ℚ))
        (r' := (4320647243227353 / 2500000000000000 : ℚ))
        (U := (-(11127371186098035850237 / 5000000000000000000000 : ℚ)))
        (U' := (2735572419901964149763 / 5000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (7424867802851 / 32000000000000 : ℚ))
      (s := (846642277807739 / 10000000000000000 : ℚ))
      (q := (4320647243227353 / 40000000000000000 : ℚ))
      (U := (-(11127371186098035850237 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_280_9 :
    Uω (aρ 9) (bρ 9) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_280_10 :
    Uω (aρ 10) (bρ 10) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_280_11 :
    Uω (aρ 11) (bρ 11) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_280_12 :
    Uω (aρ 12) (bρ 12) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_280_13 :
    Uω (aρ 13) (bρ 13) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_280_14 :
    Uω (aρ 14) (bρ 14) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_280_15 :
    Uω (aρ 15) (bρ 15) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_280_16 :
    Uω (aρ 16) (bρ 16) (7424867802851 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_280 :
    Uρ (7424867802851 / 32000000000000 : ℝ) ≤
      (-(18424120970672703313979 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_280_1 U_280_2 U_280_3 U_280_4 U_280_5 U_280_6 U_280_7 U_280_8 U_280_9 U_280_10
    U_280_11 U_280_12 U_280_13 U_280_14 U_280_15 U_280_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_281_1 :
    Uω (aρ 1) (bρ 1) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(14844077893084188706087 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2266365173341027 / 10000000000000000 : ℝ) ≤
      (-(14844077893084188706087 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2266365173341027 / 10000000000000000 : ℚ))
        (r' := (2266365173341027 / 1250000000000000 : ℚ))
        (U := (-(14844077893084188706087 / 10000000000000000000000 : ℚ)))
        (U' := (5950337515915811293913 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (3729493959969 / 16000000000000 : ℚ))
      (s := (2266293839786429 / 10000000000000000 : ℚ))
      (q := (2266365173341027 / 10000000000000000 : ℚ))
      (U := (-(14844077893084188706087 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_281_2 :
    Uω (aρ 2) (bρ 2) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(7475650471701528025081 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (179375546383163 / 800000000000000 : ℝ) ≤
      (-(7475650471701528025081 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (179375546383163 / 800000000000000 : ℚ))
        (r' := (179375546383163 / 100000000000000 : ℚ))
        (U := (-(7475650471701528025081 / 5000000000000000000000 : ℚ)))
        (U' := (2921557232798471974919 / 5000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (3729493959969 / 16000000000000 : ℚ))
      (s := (44834423303869 / 200000000000000 : ℚ))
      (q := (179375546383163 / 800000000000000 : ℚ))
      (U := (-(7475650471701528025081 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_281_3 :
    Uω (aρ 3) (bρ 3) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(15170478598639876278171 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2193585089108003 / 10000000000000000 : ℝ) ≤
      (-(15170478598639876278171 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2193585089108003 / 10000000000000000 : ℚ))
        (r' := (2193585089108003 / 1250000000000000 : ℚ))
        (U := (-(15170478598639876278171 / 10000000000000000000000 : ℚ)))
        (U' := (5623936810360123721829 / 10000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (3729493959969 / 16000000000000 : ℚ))
      (s := (2191898790180381 / 10000000000000000 : ℚ))
      (q := (2193585089108003 / 10000000000000000 : ℚ))
      (U := (-(15170478598639876278171 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_281_4 :
    Uω (aρ 4) (bρ 4) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(3109903348603568808439 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4223991771944979 / 20000000000000000 : ℝ) ≤
      (-(3109903348603568808439 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4223991771944979 / 20000000000000000 : ℚ))
        (r' := (4223991771944979 / 2500000000000000 : ℚ))
        (U := (-(3109903348603568808439 / 2000000000000000000000 : ℚ)))
        (U' := (1048979733196431191561 / 2000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (3729493959969 / 16000000000000 : ℚ))
      (s := (1053507282487177 / 5000000000000000 : ℚ))
      (q := (4223991771944979 / 20000000000000000 : ℚ))
      (U := (-(3109903348603568808439 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_281_5 :
    Uω (aρ 5) (bρ 5) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(16167772839817462190979 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1985374990190821 / 10000000000000000 : ℝ) ≤
      (-(16167772839817462190979 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1985374990190821 / 10000000000000000 : ℚ))
        (r' := (1985374990190821 / 1250000000000000 : ℚ))
        (U := (-(16167772839817462190979 / 10000000000000000000000 : ℚ)))
        (U' := (4626642569182537809021 / 10000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (3729493959969 / 16000000000000 : ℚ))
      (s := (1971962692746017 / 10000000000000000 : ℚ))
      (q := (1985374990190821 / 10000000000000000 : ℚ))
      (U := (-(16167772839817462190979 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_281_6 :
    Uω (aρ 6) (bρ 6) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(858119665204360662129 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1797408242110467 / 10000000000000000 : ℝ) ≤
      (-(858119665204360662129 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1797408242110467 / 10000000000000000 : ℚ))
        (r' := (1797408242110467 / 1250000000000000 : ℚ))
        (U := (-(858119665204360662129 / 500000000000000000000 : ℚ)))
        (U' := (181601105245639337871 / 500000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (3729493959969 / 16000000000000 : ℚ))
      (s := (1763269571725309 / 10000000000000000 : ℚ))
      (q := (1797408242110467 / 10000000000000000 : ℚ))
      (U := (-(858119665204360662129 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_281_7 :
    Uω (aρ 7) (bρ 7) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(3764166476338037308167 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (304545109974543 / 2000000000000000 : ℝ) ≤
      (-(3764166476338037308167 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (304545109974543 / 2000000000000000 : ℚ))
        (r' := (304545109974543 / 250000000000000 : ℚ))
        (U := (-(3764166476338037308167 / 2000000000000000000000 : ℚ)))
        (U' := (394716605461962691833 / 2000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (3729493959969 / 16000000000000 : ℚ))
      (s := (287513113601961 / 2000000000000000 : ℚ))
      (q := (304545109974543 / 2000000000000000 : ℚ))
      (U := (-(3764166476338037308167 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_281_8 :
    Uω (aρ 8) (bρ 8) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(885200539449577683937 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1093718921142253 / 10000000000000000 : ℝ) ≤
      (-(885200539449577683937 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1093718921142253 / 10000000000000000 : ℚ))
        (r' := (1093718921142253 / 625000000000000 : ℚ))
        (U := (-(885200539449577683937 / 400000000000000000000 : ℚ)))
        (U' := (223834949030422316063 / 400000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (3729493959969 / 16000000000000 : ℚ))
      (s := (863093961888881 / 10000000000000000 : ℚ))
      (q := (1093718921142253 / 10000000000000000 : ℚ))
      (U := (-(885200539449577683937 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_281_9 :
    Uω (aρ 9) (bρ 9) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_281_10 :
    Uω (aρ 10) (bρ 10) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_281_11 :
    Uω (aρ 11) (bρ 11) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_281_12 :
    Uω (aρ 12) (bρ 12) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_281_13 :
    Uω (aρ 13) (bρ 13) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_281_14 :
    Uω (aρ 14) (bρ 14) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_281_15 :
    Uω (aρ 15) (bρ 15) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_281_16 :
    Uω (aρ 16) (bρ 16) (3729493959969 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_281 :
    Uρ (3729493959969 / 16000000000000 : ℝ) ≤
      (-(18391299973504200398809 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_281_1 U_281_2 U_281_3 U_281_4 U_281_5 U_281_6 U_281_7 U_281_8 U_281_9 U_281_10
    U_281_11 U_281_12 U_281_13 U_281_14 U_281_15 U_281_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_282_1 :
    Uω (aρ 1) (bρ 1) (299724321481 / 1280000000000 : ℝ) ≤
      (-(1849642486269237145517 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9108112175886401 / 40000000000000000 : ℝ) ≤
      (-(1849642486269237145517 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9108112175886401 / 40000000000000000 : ℚ))
        (r' := (9108112175886401 / 5000000000000000 : ℚ))
        (U := (-(1849642486269237145517 / 1250000000000000000000 : ℚ)))
        (U' := (749659439855762854483 / 1250000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (299724321481 / 1280000000000 : ℚ))
      (s := (71154907639309 / 312500000000000 : ℚ))
      (q := (9108112175886401 / 40000000000000000 : ℚ))
      (U := (-(1849642486269237145517 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_282_2 :
    Uω (aρ 2) (bρ 2) (299724321481 / 1280000000000 : ℝ) ≤
      (-(14903849687665541604669 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9011436425144511 / 40000000000000000 : ℝ) ≤
      (-(14903849687665541604669 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9011436425144511 / 40000000000000000 : ℚ))
        (r' := (9011436425144511 / 5000000000000000 : ℚ))
        (U := (-(14903849687665541604669 / 10000000000000000000000 : ℚ)))
        (U' := (5890565721334458395331 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (299724321481 / 1280000000000 : ℚ))
      (s := (2252388181596943 / 10000000000000000 : ℚ))
      (q := (9011436425144511 / 40000000000000000 : ℚ))
      (U := (-(14903849687665541604669 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_282_3 :
    Uω (aρ 3) (bρ 3) (299724321481 / 1280000000000 : ℝ) ≤
      (-(3024390301891908800277 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (70536185247759 / 320000000000000 : ℝ) ≤
      (-(3024390301891908800277 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (70536185247759 / 320000000000000 : ℚ))
        (r' := (70536185247759 / 40000000000000 : ℚ))
        (U := (-(3024390301891908800277 / 2000000000000000000000 : ℚ)))
        (U' := (1134492779908091199723 / 2000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (299724321481 / 1280000000000 : ℚ))
      (s := (17620621226877 / 80000000000000 : ℚ))
      (q := (70536185247759 / 320000000000000 : ℚ))
      (U := (-(3024390301891908800277 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_282_4 :
    Uω (aρ 4) (bρ 4) (299724321481 / 1280000000000 : ℝ) ≤
      (-(193738000068022755659 / 125000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8490734013170131 / 40000000000000000 : ℝ) ≤
      (-(193738000068022755659 / 125000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8490734013170131 / 40000000000000000 : ℚ))
        (r' := (8490734013170131 / 5000000000000000 : ℚ))
        (U := (-(193738000068022755659 / 125000000000000000000 : ℚ)))
        (U' := (66192192544477244341 / 125000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (299724321481 / 1280000000000 : ℚ))
      (s := (2117727263024753 / 10000000000000000 : ℚ))
      (q := (8490734013170131 / 40000000000000000 : ℚ))
      (U := (-(193738000068022755659 / 125000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_282_5 :
    Uω (aρ 5) (bρ 5) (299724321481 / 1280000000000 : ℝ) ≤
      (-(402846244571714183917 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7984438621375987 / 40000000000000000 : ℝ) ≤
      (-(402846244571714183917 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7984438621375987 / 40000000000000000 : ℚ))
        (r' := (7984438621375987 / 5000000000000000 : ℚ))
        (U := (-(402846244571714183917 / 250000000000000000000 : ℚ)))
        (U' := (117014140653285816083 / 250000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (299724321481 / 1280000000000 : ℚ))
      (s := (1982769486462681 / 10000000000000000 : ℚ))
      (q := (7984438621375987 / 40000000000000000 : ℚ))
      (U := (-(402846244571714183917 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_282_6 :
    Uω (aρ 6) (bρ 6) (299724321481 / 1280000000000 : ℝ) ≤
      (-(17102112138147452632809 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7233103806245339 / 40000000000000000 : ℝ) ≤
      (-(17102112138147452632809 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7233103806245339 / 40000000000000000 : ℚ))
        (r' := (7233103806245339 / 5000000000000000 : ℚ))
        (U := (-(17102112138147452632809 / 10000000000000000000000 : ℚ)))
        (U' := (3692303270852547367191 / 10000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (299724321481 / 1280000000000 : ℚ))
      (s := (1774342454037357 / 10000000000000000 : ℚ))
      (q := (7233103806245339 / 40000000000000000 : ℚ))
      (U := (-(17102112138147452632809 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_282_7 :
    Uω (aρ 7) (bρ 7) (299724321481 / 1280000000000 : ℝ) ≤
      (-(1171685462072131543447 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1227211842480363 / 8000000000000000 : ℝ) ≤
      (-(1171685462072131543447 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1227211842480363 / 8000000000000000 : ℚ))
        (r' := (1227211842480363 / 1000000000000000 : ℚ))
        (U := (-(1171685462072131543447 / 625000000000000000000 : ℚ)))
        (U' := (127965500990368456553 / 625000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (299724321481 / 1280000000000 : ℚ))
      (s := (289896307575119 / 2000000000000000 : ℚ))
      (q := (1227211842480363 / 8000000000000000 : ℚ))
      (U := (-(1171685462072131543447 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_282_8 :
    Uω (aρ 8) (bρ 8) (299724321481 / 1280000000000 : ℝ) ≤
      (-(11003813586334001811501 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4428747159444107 / 40000000000000000 : ℝ) ≤
      (-(11003813586334001811501 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4428747159444107 / 40000000000000000 : ℚ))
        (r' := (4428747159444107 / 2500000000000000 : ℚ))
        (U := (-(11003813586334001811501 / 5000000000000000000000 : ℚ)))
        (U' := (2859130019665998188499 / 5000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (299724321481 / 1280000000000 : ℚ))
      (s := (879367162736741 / 10000000000000000 : ℚ))
      (q := (4428747159444107 / 40000000000000000 : ℚ))
      (U := (-(11003813586334001811501 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_282_9 :
    Uω (aρ 9) (bρ 9) (299724321481 / 1280000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_282_10 :
    Uω (aρ 10) (bρ 10) (299724321481 / 1280000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_282_11 :
    Uω (aρ 11) (bρ 11) (299724321481 / 1280000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_282_12 :
    Uω (aρ 12) (bρ 12) (299724321481 / 1280000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_282_13 :
    Uω (aρ 13) (bρ 13) (299724321481 / 1280000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_282_14 :
    Uω (aρ 14) (bρ 14) (299724321481 / 1280000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_282_15 :
    Uω (aρ 15) (bρ 15) (299724321481 / 1280000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_282_16 :
    Uω (aρ 16) (bρ 16) (299724321481 / 1280000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_282 :
    Uρ (299724321481 / 1280000000000 : ℝ) ≤
      (-(18358822832970896564511 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_282_1 U_282_2 U_282_3 U_282_4 U_282_5 U_282_6 U_282_7 U_282_8 U_282_9 U_282_10
    U_282_11 U_282_12 U_282_13 U_282_14 U_282_15 U_282_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_283_1 :
    Uω (aρ 1) (bρ 1) (29403234977 / 125000000000 : ℝ) ≤
      (-(14750421189550824741283 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4575381822976329 / 20000000000000000 : ℝ) ≤
      (-(14750421189550824741283 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4575381822976329 / 20000000000000000 : ℚ))
        (r' := (4575381822976329 / 2500000000000000 : ℚ))
        (U := (-(14750421189550824741283 / 10000000000000000000000 : ℚ)))
        (U' := (6043994219449175258717 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (29403234977 / 125000000000 : ℚ))
      (s := (2287620242901329 / 10000000000000000 : ℚ))
      (q := (4575381822976329 / 20000000000000000 : ℚ))
      (U := (-(14750421189550824741283 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_283_2 :
    Uω (aρ 2) (bρ 2) (29403234977 / 125000000000 : ℝ) ≤
      (-(7428311312201253933377 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4527047723342681 / 20000000000000000 : ℝ) ≤
      (-(7428311312201253933377 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4527047723342681 / 20000000000000000 : ℚ))
        (r' := (4527047723342681 / 2500000000000000 : ℚ))
        (U := (-(7428311312201253933377 / 5000000000000000000000 : ℚ)))
        (U' := (2968896392298746066623 / 5000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (29403234977 / 125000000000 : ℚ))
      (s := (2263055155777681 / 10000000000000000 : ℚ))
      (q := (4527047723342681 / 20000000000000000 : ℚ))
      (U := (-(7428311312201253933377 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_283_3 :
    Uω (aρ 3) (bρ 3) (29403234977 / 125000000000 : ℝ) ≤
      (-(7536829563360700704481 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4429852820324179 / 20000000000000000 : ℝ) ≤
      (-(7536829563360700704481 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4429852820324179 / 20000000000000000 : ℚ))
        (r' := (4429852820324179 / 2500000000000000 : ℚ))
        (U := (-(7536829563360700704481 / 5000000000000000000000 : ℚ)))
        (U' := (2860378141139299295519 / 5000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (29403234977 / 125000000000 : ℚ))
      (s := (2213256359109179 / 10000000000000000 : ℚ))
      (q := (4429852820324179 / 20000000000000000 : ℚ))
      (U := (-(7536829563360700704481 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_283_4 :
    Uω (aρ 4) (bρ 4) (29403234977 / 125000000000 : ℝ) ≤
      (-(1931102244940006175991 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2133370868734877 / 10000000000000000 : ℝ) ≤
      (-(1931102244940006175991 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2133370868734877 / 10000000000000000 : ℚ))
        (r' := (2133370868734877 / 1250000000000000 : ℚ))
        (U := (-(1931102244940006175991 / 1250000000000000000000 : ℚ)))
        (U' := (668199681184993824009 / 1250000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (29403234977 / 125000000000 : ℚ))
      (s := (1064219728659877 / 5000000000000000 : ℚ))
      (q := (2133370868734877 / 10000000000000000 : ℚ))
      (U := (-(1931102244940006175991 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_283_5 :
    Uω (aρ 5) (bρ 5) (29403234977 / 125000000000 : ℝ) ≤
      (-(16060219807321465949653 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4013687087452027 / 20000000000000000 : ℝ) ≤
      (-(16060219807321465949653 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4013687087452027 / 20000000000000000 : ℚ))
        (r' := (4013687087452027 / 2500000000000000 : ℚ))
        (U := (-(16060219807321465949653 / 10000000000000000000000 : ℚ)))
        (U' := (4734195601678534050347 / 10000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (29403234977 / 125000000000 : ℚ))
      (s := (1993574726637027 / 10000000000000000 : ℚ))
      (q := (4013687087452027 / 20000000000000000 : ℚ))
      (U := (-(16060219807321465949653 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_283_6 :
    Uω (aρ 6) (bρ 6) (29403234977 / 125000000000 : ℝ) ≤
      (-(8521102954091416726939 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (454785290815107 / 2500000000000000 : ℝ) ≤
      (-(8521102954091416726939 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (454785290815107 / 2500000000000000 : ℚ))
        (r' := (454785290815107 / 312500000000000 : ℚ))
        (U := (-(8521102954091416726939 / 5000000000000000000000 : ℚ)))
        (U' := (1876104750408583273061 / 5000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (29403234977 / 125000000000 : ℚ))
      (s := (55794073151433 / 312500000000000 : ℚ))
      (q := (454785290815107 / 2500000000000000 : ℚ))
      (U := (-(8521102954091416726939 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_283_7 :
    Uω (aρ 7) (bρ 7) (29403234977 / 125000000000 : ℝ) ≤
      (-(18673706669854913901521 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12072612293191 / 78125000000000 : ℝ) ≤
      (-(18673706669854913901521 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12072612293191 / 78125000000000 : ℚ))
        (r' := (12072612293191 / 9765625000000 : ℚ))
        (U := (-(18673706669854913901521 / 10000000000000000000000 : ℚ)))
        (U' := (2120708739145086098479 / 10000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (29403234977 / 125000000000 : ℚ))
      (s := (182672267767737 / 1250000000000000 : ℚ))
      (q := (12072612293191 / 78125000000000 : ℚ))
      (U := (-(18673706669854913901521 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_283_8 :
    Uω (aρ 8) (bρ 8) (29403234977 / 125000000000 : ℝ) ≤
      (-(21887473556177965593987 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2241140564584159 / 20000000000000000 : ℝ) ≤
      (-(21887473556177965593987 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2241140564584159 / 20000000000000000 : ℚ))
        (r' := (2241140564584159 / 1250000000000000 : ℚ))
        (U := (-(21887473556177965593987 / 10000000000000000000000 : ℚ)))
        (U' := (5838413655822034406013 / 10000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (29403234977 / 125000000000 : ℚ))
      (s := (895471611009159 / 10000000000000000 : ℚ))
      (q := (2241140564584159 / 20000000000000000 : ℚ))
      (U := (-(21887473556177965593987 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_283_9 :
    Uω (aρ 9) (bρ 9) (29403234977 / 125000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_283_10 :
    Uω (aρ 10) (bρ 10) (29403234977 / 125000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_283_11 :
    Uω (aρ 11) (bρ 11) (29403234977 / 125000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_283_12 :
    Uω (aρ 12) (bρ 12) (29403234977 / 125000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_283_13 :
    Uω (aρ 13) (bρ 13) (29403234977 / 125000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_283_14 :
    Uω (aρ 14) (bρ 14) (29403234977 / 125000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_283_15 :
    Uω (aρ 15) (bρ 15) (29403234977 / 125000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_283_16 :
    Uω (aρ 16) (bρ 16) (29403234977 / 125000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_283 :
    Uρ (29403234977 / 125000000000 : ℝ) ≤
      (-(3665335590052395257373 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_283_1 U_283_2 U_283_3 U_283_4 U_283_5 U_283_6 U_283_7 U_283_8 U_283_9 U_283_10
    U_283_11 U_283_12 U_283_13 U_283_14 U_283_15 U_283_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_284_1 :
    Uω (aρ 1) (bρ 1) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(2940783950288045734059 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1838683020747251 / 8000000000000000 : ℝ) ≤
      (-(2940783950288045734059 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1838683020747251 / 8000000000000000 : ℚ))
        (r' := (1838683020747251 / 1000000000000000 : ℚ))
        (U := (-(2940783950288045734059 / 2000000000000000000000 : ℚ)))
        (U' := (1218099131511954265941 / 2000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (7561348271199 / 32000000000000 : ℚ))
      (s := (28728542940043 / 125000000000000 : ℚ))
      (q := (1838683020747251 / 8000000000000000 : ℚ))
      (U := (-(2940783950288045734059 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_284_2 :
    Uω (aρ 2) (bρ 2) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(7404808822111749557067 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9096754384969207 / 40000000000000000 : ℝ) ≤
      (-(7404808822111749557067 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9096754384969207 / 40000000000000000 : ℚ))
        (r' := (9096754384969207 / 5000000000000000 : ℚ))
        (U := (-(7404808822111749557067 / 5000000000000000000000 : ℚ)))
        (U' := (2992398882388250442933 / 5000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (7561348271199 / 32000000000000 : ℚ))
      (s := (568430522082479 / 2500000000000000 : ℚ))
      (q := (9096754384969207 / 40000000000000000 : ℚ))
      (U := (-(7404808822111749557067 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_284_3 :
    Uω (aρ 3) (bρ 3) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(15025599187597887615541 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8902387815003059 / 40000000000000000 : ℝ) ≤
      (-(15025599187597887615541 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8902387815003059 / 40000000000000000 : ℚ))
        (r' := (8902387815003059 / 5000000000000000 : ℚ))
        (U := (-(15025599187597887615541 / 10000000000000000000000 : ℚ)))
        (U' := (5768816221402112384459 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (7561348271199 / 32000000000000 : ℚ))
      (s := (1111967454848421 / 5000000000000000 : ℚ))
      (q := (8902387815003059 / 40000000000000000 : ℚ))
      (U := (-(15025599187597887615541 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_284_4 :
    Uω (aρ 4) (bρ 4) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(15398848036234854074413 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8576231944333977 / 40000000000000000 : ℝ) ≤
      (-(15398848036234854074413 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8576231944333977 / 40000000000000000 : ℚ))
        (r' := (8576231944333977 / 5000000000000000 : ℚ))
        (U := (-(15398848036234854074413 / 10000000000000000000000 : ℚ)))
        (U' := (5395567372765145925587 / 10000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (7561348271199 / 32000000000000 : ℚ))
      (s := (2139151155427301 / 10000000000000000 : ℚ))
      (q := (8576231944333977 / 40000000000000000 : ℚ))
      (U := (-(15398848036234854074413 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_284_5 :
    Uω (aρ 5) (bρ 5) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(3201375940674537947543 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8070306671596673 / 40000000000000000 : ℝ) ≤
      (-(3201375940674537947543 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8070306671596673 / 40000000000000000 : ℚ))
        (r' := (8070306671596673 / 5000000000000000 : ℚ))
        (U := (-(3201375940674537947543 / 2000000000000000000000 : ℚ)))
        (U' := (957507141125462052457 / 2000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (7561348271199 / 32000000000000 : ℚ))
      (s := (2004378438393649 / 10000000000000000 : ℚ))
      (q := (8070306671596673 / 40000000000000000 : ℚ))
      (U := (-(3201375940674537947543 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_284_6 :
    Uω (aρ 6) (bρ 6) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(16982669814435490042889 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7320015693491687 / 40000000000000000 : ℝ) ≤
      (-(16982669814435490042889 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7320015693491687 / 40000000000000000 : ℚ))
        (r' := (7320015693491687 / 5000000000000000 : ℚ))
        (U := (-(16982669814435490042889 / 10000000000000000000000 : ℚ)))
        (U' := (3811745594564509957111 / 10000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (7561348271199 / 32000000000000 : ℚ))
      (s := (449118331120289 / 2500000000000000 : ℚ))
      (q := (7320015693491687 / 40000000000000000 : ℚ))
      (U := (-(16982669814435490042889 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_284_7 :
    Uω (aρ 7) (bρ 7) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(18601039457942155663267 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6226257982895227 / 40000000000000000 : ℝ) ≤
      (-(18601039457942155663267 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6226257982895227 / 40000000000000000 : ℚ))
        (r' := (6226257982895227 / 5000000000000000 : ℚ))
        (U := (-(18601039457942155663267 / 10000000000000000000000 : ℚ)))
        (U' := (2193375951057844336733 / 10000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (7561348271199 / 32000000000000 : ℚ))
      (s := (736627924971463 / 5000000000000000 : ℚ))
      (q := (6226257982895227 / 40000000000000000 : ℚ))
      (U := (-(18601039457942155663267 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_284_8 :
    Uω (aρ 8) (bρ 8) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(5442362793886692937687 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36283963877359 / 320000000000000 : ℝ) ≤
      (-(5442362793886692937687 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (36283963877359 / 320000000000000 : ℚ))
        (r' := (36283963877359 / 20000000000000 : ℚ))
        (U := (-(5442362793886692937687 / 2500000000000000000000 : ℚ)))
        (U' := (1489109009113307062313 / 2500000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (7561348271199 / 32000000000000 : ℚ))
      (s := (3645665008681 / 40000000000000 : ℚ))
      (q := (36283963877359 / 320000000000000 : ℚ))
      (U := (-(5442362793886692937687 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_284_9 :
    Uω (aρ 9) (bρ 9) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_284_10 :
    Uω (aρ 10) (bρ 10) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_284_11 :
    Uω (aρ 11) (bρ 11) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_284_12 :
    Uω (aρ 12) (bρ 12) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_284_13 :
    Uω (aρ 13) (bρ 13) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_284_14 :
    Uω (aρ 14) (bρ 14) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_284_15 :
    Uω (aρ 15) (bρ 15) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_284_16 :
    Uω (aρ 16) (bρ 16) (7561348271199 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_284 :
    Uρ (7561348271199 / 32000000000000 : ℝ) ≤
      (-(9147427256802812168183 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_284_1 U_284_2 U_284_3 U_284_4 U_284_5 U_284_6 U_284_7 U_284_8 U_284_9 U_284_10
    U_284_11 U_284_12 U_284_13 U_284_14 U_284_15 U_284_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_285_1 :
    Uω (aρ 1) (bρ 1) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(3664408391079400055809 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4618033274703681 / 20000000000000000 : ℝ) ≤
      (-(3664408391079400055809 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4618033274703681 / 20000000000000000 : ℚ))
        (r' := (4618033274703681 / 2500000000000000 : ℚ))
        (U := (-(3664408391079400055809 / 2500000000000000000000 : ℚ)))
        (U' := (1534195461170599944191 / 2500000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (3797734194143 / 16000000000000 : ℚ))
      (s := (1154473310724653 / 5000000000000000 : ℚ))
      (q := (4618033274703681 / 20000000000000000 : ℚ))
      (U := (-(3664408391079400055809 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_285_2 :
    Uω (aρ 2) (bρ 2) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(461338520855661178501 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (571213327572647 / 2500000000000000 : ℝ) ≤
      (-(461338520855661178501 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (571213327572647 / 2500000000000000 : ℚ))
        (r' := (571213327572647 / 312500000000000 : ℚ))
        (U := (-(461338520855661178501 / 312500000000000000000 : ℚ)))
        (U' := (188486960675588821499 / 312500000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (3797734194143 / 16000000000000 : ℚ))
      (s := (2284388979836801 / 10000000000000000 : ℚ))
      (q := (571213327572647 / 2500000000000000 : ℚ))
      (U := (-(461338520855661178501 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_285_3 :
    Uω (aρ 3) (bρ 3) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(14977769461876843290263 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (894506968348281 / 4000000000000000 : ℝ) ≤
      (-(14977769461876843290263 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (894506968348281 / 4000000000000000 : ℚ))
        (r' := (894506968348281 / 500000000000000 : ℚ))
        (U := (-(14977769461876843290263 / 10000000000000000000000 : ℚ)))
        (U' := (5816645947123156709737 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (3797734194143 / 16000000000000 : ℚ))
      (s := (223461330734703 / 1000000000000000 : ℚ))
      (q := (894506968348281 / 4000000000000000 : ℚ))
      (U := (-(14977769461876843290263 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_285_4 :
    Uω (aρ 4) (bρ 4) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(7674563852708070316761 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2154744859046769 / 10000000000000000 : ℝ) ≤
      (-(7674563852708070316761 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2154744859046769 / 10000000000000000 : ℚ))
        (r' := (2154744859046769 / 1250000000000000 : ℚ))
        (U := (-(7674563852708070316761 / 5000000000000000000000 : ℚ)))
        (U' := (2722643851791929683239 / 5000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (3797734194143 / 16000000000000 : ℚ))
      (s := (2149862364764163 / 10000000000000000 : ℚ))
      (q := (2154744859046769 / 10000000000000000 : ℚ))
      (U := (-(7674563852708070316761 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_285_5 :
    Uω (aρ 5) (bρ 5) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(3190765262861868759431 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1014154520077303 / 5000000000000000 : ℝ) ≤
      (-(3190765262861868759431 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1014154520077303 / 5000000000000000 : ℚ))
        (r' := (1014154520077303 / 625000000000000 : ℚ))
        (U := (-(3190765262861868759431 / 2000000000000000000000 : ℚ)))
        (U' := (968117818938131240569 / 2000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (3797734194143 / 16000000000000 : ℚ))
      (s := (2015180646314837 / 10000000000000000 : ℚ))
      (q := (1014154520077303 / 5000000000000000 : ℚ))
      (U := (-(3190765262861868759431 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_285_6 :
    Uω (aρ 6) (bρ 6) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(8461749575806555752881 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3681728553827143 / 20000000000000000 : ℝ) ≤
      (-(8461749575806555752881 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3681728553827143 / 20000000000000000 : ℚ))
        (r' := (3681728553827143 / 2500000000000000 : ℚ))
        (U := (-(8461749575806555752881 / 5000000000000000000000 : ℚ)))
        (U' := (1935458128693444247119 / 5000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (3797734194143 / 16000000000000 : ℚ))
      (s := (56485359217899 / 312500000000000 : ℚ))
      (q := (3681728553827143 / 20000000000000000 : ℚ))
      (U := (-(8461749575806555752881 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_285_7 :
    Uω (aρ 7) (bρ 7) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(18528955308340390514393 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (627130158553129 / 4000000000000000 : ℝ) ≤
      (-(18528955308340390514393 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (627130158553129 / 4000000000000000 : ℚ))
        (r' := (627130158553129 / 500000000000000 : ℚ))
        (U := (-(18528955308340390514393 / 10000000000000000000000 : ℚ)))
        (U' := (2265460100659609485607 / 10000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (3797734194143 / 16000000000000 : ℚ))
      (s := (148511511467127 / 1000000000000000 : ℚ))
      (q := (627130158553129 / 4000000000000000 : ℚ))
      (U := (-(18528955308340390514393 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_285_8 :
    Uω (aρ 8) (bρ 8) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(21653466102551587295531 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2294203357321019 / 20000000000000000 : ℝ) ≤
      (-(21653466102551587295531 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2294203357321019 / 20000000000000000 : ℚ))
        (r' := (2294203357321019 / 1250000000000000 : ℚ))
        (U := (-(21653466102551587295531 / 10000000000000000000000 : ℚ)))
        (U' := (6072421109448412704469 / 10000000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (3797734194143 / 16000000000000 : ℚ))
      (s := (231802332641661 / 2500000000000000 : ℚ))
      (q := (2294203357321019 / 20000000000000000 : ℚ))
      (U := (-(21653466102551587295531 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_285_9 :
    Uω (aρ 9) (bρ 9) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_285_10 :
    Uω (aρ 10) (bρ 10) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_285_11 :
    Uω (aρ 11) (bρ 11) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_285_12 :
    Uω (aρ 12) (bρ 12) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_285_13 :
    Uω (aρ 13) (bρ 13) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_285_14 :
    Uω (aρ 14) (bρ 14) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_285_15 :
    Uω (aρ 15) (bρ 15) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_285_16 :
    Uω (aρ 16) (bρ 16) (3797734194143 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_285 :
    Uρ (3797734194143 / 16000000000000 : ℝ) ≤
      (-(18263342418928709501953 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_285_1 U_285_2 U_285_3 U_285_4 U_285_5 U_285_6 U_285_7 U_285_8 U_285_9 U_285_10
    U_285_11 U_285_12 U_285_13 U_285_14 U_285_15 U_285_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_286_1 :
    Uω (aρ 1) (bρ 1) (383185431123 / 1600000000000 : ℝ) ≤
      (-(728284951777396434499 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4660684702538611 / 20000000000000000 : ℝ) ≤
      (-(728284951777396434499 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4660684702538611 / 20000000000000000 : ℚ))
        (r' := (4660684702538611 / 2500000000000000 : ℚ))
        (U := (-(728284951777396434499 / 500000000000000000000 : ℚ)))
        (U' := (311435818672603565501 / 500000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (383185431123 / 1600000000000 : ℚ))
      (s := (2330272976104861 / 10000000000000000 : ℚ))
      (q := (4660684702538611 / 20000000000000000 : ℚ))
      (U := (-(728284951777396434499 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_286_2 :
    Uω (aρ 2) (bρ 2) (383185431123 / 1600000000000 : ℝ) ≤
      (-(14669914549627046428131 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4612365355916907 / 20000000000000000 : ℝ) ≤
      (-(14669914549627046428131 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4612365355916907 / 20000000000000000 : ℚ))
        (r' := (4612365355916907 / 2500000000000000 : ℚ))
        (U := (-(14669914549627046428131 / 10000000000000000000000 : ℚ)))
        (U' := (6124500859372953571869 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (383185431123 / 1600000000000 : ℚ))
      (s := (2305722641993157 / 10000000000000000 : ℚ))
      (q := (4612365355916907 / 20000000000000000 : ℚ))
      (U := (-(14669914549627046428131 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_286_3 :
    Uω (aρ 3) (bρ 3) (383185431123 / 1600000000000 : ℝ) ≤
      (-(1488279188913710560159 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2257608130047833 / 10000000000000000 : ℝ) ≤
      (-(1488279188913710560159 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2257608130047833 / 10000000000000000 : ℚ))
        (r' := (2257608130047833 / 1250000000000000 : ℚ))
        (U := (-(1488279188913710560159 / 1000000000000000000000 : ℚ)))
        (U' := (591162351986289439841 / 1000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (383185431123 / 1600000000000 : ℚ))
      (s := (563992413130479 / 2500000000000000 : ℚ))
      (q := (2257608130047833 / 10000000000000000 : ℚ))
      (U := (-(1488279188913710560159 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_286_4 :
    Uω (aρ 4) (bρ 4) (383185431123 / 1600000000000 : ℝ) ≤
      (-(7625212945029603857267 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4352235772568247 / 20000000000000000 : ℝ) ≤
      (-(7625212945029603857267 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4352235772568247 / 20000000000000000 : ℚ))
        (r' := (4352235772568247 / 2500000000000000 : ℚ))
        (U := (-(7625212945029603857267 / 5000000000000000000000 : ℚ)))
        (U' := (2771994759470396142733 / 5000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (383185431123 / 1600000000000 : ℚ))
      (s := (2171283346059497 / 10000000000000000 : ℚ))
      (q := (4352235772568247 / 20000000000000000 : ℚ))
      (U := (-(7625212945029603857267 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_286_5 :
    Uω (aρ 5) (bρ 5) (383185431123 / 1600000000000 : ℝ) ≤
      (-(1981070914050747589499 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (51244289419121 / 250000000000000 : ℝ) ≤
      (-(1981070914050747589499 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (51244289419121 / 250000000000000 : ℚ))
        (r' := (51244289419121 / 31250000000000 : ℚ))
        (U := (-(1981070914050747589499 / 1250000000000000000000 : ℚ)))
        (U' := (618231012074252410501 / 1250000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (383185431123 / 1600000000000 : ℚ))
      (s := (203678064635593 / 1000000000000000 : ℚ))
      (q := (51244289419121 / 250000000000000 : ℚ))
      (U := (-(1981070914050747589499 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_286_6 :
    Uω (aρ 6) (bρ 6) (383185431123 / 1600000000000 : ℝ) ≤
      (-(16806235754814884325851 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3725155877604123 / 20000000000000000 : ℝ) ≤
      (-(16806235754814884325851 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3725155877604123 / 20000000000000000 : ℚ))
        (r' := (3725155877604123 / 2500000000000000 : ℚ))
        (U := (-(16806235754814884325851 / 10000000000000000000000 : ℚ)))
        (U' := (3988179654185115674149 / 10000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (383185431123 / 1600000000000 : ℚ))
      (s := (1829633745570373 / 10000000000000000 : ℚ))
      (q := (3725155877604123 / 20000000000000000 : ℚ))
      (U := (-(16806235754814884325851 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_286_7 :
    Uω (aρ 7) (bρ 7) (383185431123 / 1600000000000 : ℝ) ≤
      (-(18386495852461762688133 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1590320402548059 / 10000000000000000 : ℝ) ≤
      (-(18386495852461762688133 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1590320402548059 / 10000000000000000 : ℚ))
        (r' := (1590320402548059 / 1250000000000000 : ℚ))
        (U := (-(18386495852461762688133 / 10000000000000000000000 : ℚ)))
        (U' := (2407919556538237311867 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (383185431123 / 1600000000000 : ℚ))
      (s := (47149376681949 / 312500000000000 : ℚ))
      (q := (1590320402548059 / 10000000000000000 : ℚ))
      (U := (-(18386495852461762688133 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_286_8 :
    Uω (aρ 8) (bρ 8) (383185431123 / 1600000000000 : ℝ) ≤
      (-(2678408166937960326061 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2346689798958173 / 20000000000000000 : ℝ) ≤
      (-(2678408166937960326061 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2346689798958173 / 20000000000000000 : ℚ))
        (r' := (2346689798958173 / 1250000000000000 : ℚ))
        (U := (-(2678408166937960326061 / 1250000000000000000000 : ℚ)))
        (U' := (787327734562039673939 / 1250000000000000000000 : ℚ))
        4 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (383185431123 / 1600000000000 : ℚ))
      (s := (958370699024423 / 10000000000000000 : ℚ))
      (q := (2346689798958173 / 20000000000000000 : ℚ))
      (U := (-(2678408166937960326061 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_286_9 :
    Uω (aρ 9) (bρ 9) (383185431123 / 1600000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_286_10 :
    Uω (aρ 10) (bρ 10) (383185431123 / 1600000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_286_11 :
    Uω (aρ 11) (bρ 11) (383185431123 / 1600000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_286_12 :
    Uω (aρ 12) (bρ 12) (383185431123 / 1600000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_286_13 :
    Uω (aρ 13) (bρ 13) (383185431123 / 1600000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_286_14 :
    Uω (aρ 14) (bρ 14) (383185431123 / 1600000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_286_15 :
    Uω (aρ 15) (bρ 15) (383185431123 / 1600000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_286_16 :
    Uω (aρ 16) (bρ 16) (383185431123 / 1600000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_286 :
    Uρ (383185431123 / 1600000000000 : ℝ) ≤
      (-(3640242994400076007859 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_286_1 U_286_2 U_286_3 U_286_4 U_286_5 U_286_6 U_286_7 U_286_8 U_286_9 U_286_10
    U_286_11 U_286_12 U_286_13 U_286_14 U_286_15 U_286_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_287_1 :
    Uω (aρ 1) (bρ 1) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(7237301029131155242153 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4703336107131151 / 20000000000000000 : ℝ) ≤
      (-(7237301029131155242153 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4703336107131151 / 20000000000000000 : ℚ))
        (r' := (4703336107131151 / 2500000000000000 : ℚ))
        (U := (-(7237301029131155242153 / 5000000000000000000000 : ℚ)))
        (U' := (3159906675368844757847 / 5000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (3865974428317 / 16000000000000 : ℚ))
      (s := (1175799653759013 / 5000000000000000 : ℚ))
      (q := (4703336107131151 / 20000000000000000 : ℚ))
      (U := (-(7237301029131155242153 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_287_2 :
    Uω (aρ 2) (bρ 2) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(3644463051331309478819 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (931004786760537 / 4000000000000000 : ℝ) ≤
      (-(3644463051331309478819 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (931004786760537 / 4000000000000000 : ℚ))
        (r' := (931004786760537 / 500000000000000 : ℚ))
        (U := (-(3644463051331309478819 / 2500000000000000000000 : ℚ)))
        (U' := (1554140800918690521181 / 2500000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (3865974428317 / 16000000000000 : ℚ))
      (s := (58176403667489 / 250000000000000 : ℚ))
      (q := (931004786760537 / 4000000000000000 : ℚ))
      (U := (-(3644463051331309478819 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_287_3 :
    Uω (aρ 3) (bρ 3) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(2957741839148582854709 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4557897092353209 / 20000000000000000 : ℝ) ≤
      (-(2957741839148582854709 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4557897092353209 / 20000000000000000 : ℚ))
        (r' := (4557897092353209 / 2500000000000000 : ℚ))
        (U := (-(2957741839148582854709 / 2000000000000000000000 : ℚ)))
        (U' := (1201141242651417145291 / 2000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (3865974428317 / 16000000000000 : ℚ))
      (s := (569331352900021 / 2500000000000000 : ℚ))
      (q := (4557897092353209 / 20000000000000000 : ℚ))
      (U := (-(2957741839148582854709 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_287_4 :
    Uω (aρ 4) (bρ 4) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(378817325494630744883 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1098744989336193 / 5000000000000000 : ℝ) ≤
      (-(378817325494630744883 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1098744989336193 / 5000000000000000 : ℚ))
        (r' := (1098744989336193 / 625000000000000 : ℚ))
        (U := (-(378817325494630744883 / 250000000000000000000 : ℚ)))
        (U' := (141043059730369255117 / 250000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (3865974428317 / 16000000000000 : ℚ))
      (s := (2192702457656647 / 10000000000000000 : ℚ))
      (q := (1098744989336193 / 5000000000000000 : ℚ))
      (U := (-(378817325494630744883 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_287_5 :
    Uω (aρ 5) (bρ 5) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(3936104641443346695053 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (828492498694077 / 4000000000000000 : ℝ) ≤
      (-(3936104641443346695053 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (828492498694077 / 4000000000000000 : ℚ))
        (r' := (828492498694077 / 500000000000000 : ℚ))
        (U := (-(3936104641443346695053 / 2500000000000000000000 : ℚ)))
        (U' := (1262499210806653304947 / 2500000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (3865974428317 / 16000000000000 : ℚ))
      (s := (102918745655863 / 500000000000000 : ℚ))
      (q := (828492498694077 / 4000000000000000 : ℚ))
      (U := (-(3936104641443346695053 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_287_6 :
    Uω (aρ 6) (bρ 6) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(8345189935393049647993 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3768564974754009 / 20000000000000000 : ℝ) ≤
      (-(8345189935393049647993 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3768564974754009 / 20000000000000000 : ℚ))
        (r' := (3768564974754009 / 2500000000000000 : ℚ))
        (U := (-(8345189935393049647993 / 5000000000000000000000 : ℚ)))
        (U' := (2052017769106950352007 / 5000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (3865974428317 / 16000000000000 : ℚ))
      (s := (462929442385221 / 2500000000000000 : ℚ))
      (q := (3768564974754009 / 20000000000000000 : ℚ))
      (U := (-(8345189935393049647993 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_287_7 :
    Uω (aρ 7) (bρ 7) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(18246250365212857194421 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (129022484854003 / 800000000000000 : ℝ) ≤
      (-(18246250365212857194421 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (129022484854003 / 800000000000000 : ℚ))
        (r' := (129022484854003 / 100000000000000 : ℚ))
        (U := (-(18246250365212857194421 / 10000000000000000000000 : ℚ)))
        (U' := (2548165043787142805579 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (3865974428317 / 16000000000000 : ℚ))
      (s := (30647525937939 / 200000000000000 : ℚ))
      (q := (129022484854003 / 800000000000000 : ℚ))
      (U := (-(18246250365212857194421 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_287_8 :
    Uω (aρ 8) (bρ 8) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(1060412185914542412997 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2398654369369711 / 20000000000000000 : ℝ) ≤
      (-(1060412185914542412997 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2398654369369711 / 20000000000000000 : ℚ))
        (r' := (2398654369369711 / 1250000000000000 : ℚ))
        (U := (-(1060412185914542412997 / 500000000000000000000 : ℚ)))
        (U' := (325882174685457587003 / 500000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (3865974428317 / 16000000000000 : ℚ))
      (s := (494505098128293 / 5000000000000000 : ℚ))
      (q := (2398654369369711 / 20000000000000000 : ℚ))
      (U := (-(1060412185914542412997 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_287_9 :
    Uω (aρ 9) (bρ 9) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_287_10 :
    Uω (aρ 10) (bρ 10) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_287_11 :
    Uω (aρ 11) (bρ 11) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_287_12 :
    Uω (aρ 12) (bρ 12) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_287_13 :
    Uω (aρ 13) (bρ 13) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_287_14 :
    Uω (aρ 14) (bρ 14) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_287_15 :
    Uω (aρ 15) (bρ 15) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_287_16 :
    Uω (aρ 16) (bρ 16) (3865974428317 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_287 :
    Uρ (3865974428317 / 16000000000000 : ℝ) ≤
      (-(9070113256560938488283 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_287_1 U_287_2 U_287_3 U_287_4 U_287_5 U_287_6 U_287_7 U_287_8 U_287_9 U_287_10
    U_287_11 U_287_12 U_287_13 U_287_14 U_287_15 U_287_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_288_1 :
    Uω (aρ 1) (bρ 1) (975023636351 / 4000000000000 : ℝ) ≤
      (-(7192163754279661846917 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4745987489107963 / 20000000000000000 : ℝ) ≤
      (-(7192163754279661846917 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4745987489107963 / 20000000000000000 : ℚ))
        (r' := (4745987489107963 / 2500000000000000 : ℚ))
        (U := (-(7192163754279661846917 / 5000000000000000000000 : ℚ)))
        (U' := (3205043950220338153083 / 5000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (975023636351 / 4000000000000 : ℚ))
      (s := (2372925616315463 / 10000000000000000 : ℚ))
      (q := (4745987489107963 / 20000000000000000 : ℚ))
      (U := (-(7192163754279661846917 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_288_2 :
    Uω (aρ 2) (bρ 2) (975023636351 / 4000000000000 : ℝ) ≤
      (-(7243315004429613191293 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2348841179264741 / 10000000000000000 : ℝ) ≤
      (-(7243315004429613191293 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2348841179264741 / 10000000000000000 : ℚ))
        (r' := (2348841179264741 / 1250000000000000 : ℚ))
        (U := (-(7243315004429613191293 / 5000000000000000000000 : ℚ)))
        (U' := (3153892700070386808707 / 5000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (975023636351 / 4000000000000 : ℚ))
      (s := (1174194749123491 / 5000000000000000 : ℚ))
      (q := (2348841179264741 / 10000000000000000 : ℚ))
      (U := (-(7243315004429613191293 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_288_3 :
    Uω (aρ 3) (bρ 3) (975023636351 / 4000000000000 : ℝ) ≤
      (-(14695504652313017170091 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2300288677424663 / 10000000000000000 : ℝ) ≤
      (-(14695504652313017170091 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2300288677424663 / 10000000000000000 : ℚ))
        (r' := (2300288677424663 / 1250000000000000 : ℚ))
        (U := (-(14695504652313017170091 / 10000000000000000000000 : ℚ)))
        (U' := (6098910756686982829909 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (975023636351 / 4000000000000 : ℚ))
      (s := (1149340300458413 / 5000000000000000 : ℚ))
      (q := (2300288677424663 / 10000000000000000 : ℚ))
      (U := (-(14695504652313017170091 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_288_4 :
    Uω (aρ 4) (bρ 4) (975023636351 / 4000000000000 : ℝ) ≤
      (-(15055910174395545613739 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2218861163342389 / 10000000000000000 : ℝ) ≤
      (-(15055910174395545613739 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2218861163342389 / 10000000000000000 : ℚ))
        (r' := (2218861163342389 / 1250000000000000 : ℚ))
        (U := (-(15055910174395545613739 / 10000000000000000000000 : ℚ)))
        (U' := (5738505234604454386261 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (975023636351 / 4000000000000 : ℚ))
      (s := (1107059876908639 / 5000000000000000 : ℚ))
      (q := (2218861163342389 / 10000000000000000 : ℚ))
      (U := (-(15055910174395545613739 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_288_5 :
    Uω (aρ 5) (bρ 5) (975023636351 / 4000000000000 : ℝ) ≤
      (-(7820678307979677280879 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1046344069675191 / 5000000000000000 : ℝ) ≤
      (-(7820678307979677280879 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1046344069675191 / 5000000000000000 : ℚ))
        (r' := (1046344069675191 / 625000000000000 : ℚ))
        (U := (-(7820678307979677280879 / 5000000000000000000000 : ℚ)))
        (U' := (2576529396520322719121 / 5000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (975023636351 / 4000000000000 : ℚ))
      (s := (259995453146033 / 1250000000000000 : ℚ))
      (q := (1046344069675191 / 5000000000000000 : ℚ))
      (U := (-(7820678307979677280879 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_288_6 :
    Uω (aρ 6) (bρ 6) (975023636351 / 4000000000000 : ℝ) ≤
      (-(8287948505380436413979 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (762391297944483 / 4000000000000000 : ℝ) ≤
      (-(8287948505380436413979 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (762391297944483 / 4000000000000000 : ℚ))
        (r' := (762391297944483 / 500000000000000 : ℚ))
        (U := (-(8287948505380436413979 / 5000000000000000000000 : ℚ)))
        (U' := (2109259199119563586021 / 5000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (975023636351 / 4000000000000 : ℚ))
      (s := (374756842265983 / 2000000000000000 : ℚ))
      (q := (762391297944483 / 4000000000000000 : ℚ))
      (U := (-(8287948505380436413979 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_288_7 :
    Uω (aρ 7) (bρ 7) (975023636351 / 4000000000000 : ℝ) ≤
      (-(2263518134952506017373 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (408802233372463 / 2500000000000000 : ℝ) ≤
      (-(2263518134952506017373 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (408802233372463 / 2500000000000000 : ℚ))
        (r' := (408802233372463 / 312500000000000 : ℚ))
        (U := (-(2263518134952506017373 / 1250000000000000000000 : ℚ)))
        (U' := (335783791172493982627 / 1250000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (975023636351 / 4000000000000 : ℚ))
      (s := (388976742336801 / 2500000000000000 : ℚ))
      (q := (408802233372463 / 2500000000000000 : ℚ))
      (U := (-(2263518134952506017373 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_288_8 :
    Uω (aρ 8) (bρ 8) (975023636351 / 4000000000000 : ℝ) ≤
      (-(5248963545902056685773 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2450144136751753 / 20000000000000000 : ℝ) ≤
      (-(5248963545902056685773 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2450144136751753 / 20000000000000000 : ℚ))
        (r' := (2450144136751753 / 1250000000000000 : ℚ))
        (U := (-(5248963545902056685773 / 2500000000000000000000 : ℚ)))
        (U' := (1682508257097943314227 / 2500000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (975023636351 / 4000000000000 : ℚ))
      (s := (1019174890459253 / 10000000000000000 : ℚ))
      (q := (2450144136751753 / 20000000000000000 : ℚ))
      (U := (-(5248963545902056685773 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_288_9 :
    Uω (aρ 9) (bρ 9) (975023636351 / 4000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_288_10 :
    Uω (aρ 10) (bρ 10) (975023636351 / 4000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_288_11 :
    Uω (aρ 11) (bρ 11) (975023636351 / 4000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_288_12 :
    Uω (aρ 12) (bρ 12) (975023636351 / 4000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_288_13 :
    Uω (aρ 13) (bρ 13) (975023636351 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_288_14 :
    Uω (aρ 14) (bρ 14) (975023636351 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_288_15 :
    Uω (aρ 15) (bρ 15) (975023636351 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_288_16 :
    Uω (aρ 16) (bρ 16) (975023636351 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_288 :
    Uρ (975023636351 / 4000000000000 : ℝ) ≤
      (-(1130019727831504586083 / 625000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_288_1 U_288_2 U_288_3 U_288_4 U_288_5 U_288_6 U_288_7 U_288_8 U_288_9 U_288_10
    U_288_11 U_288_12 U_288_13 U_288_14 U_288_15 U_288_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_289_1 :
    Uω (aρ 1) (bρ 1) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(2858972133708537061617 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (598579856134173 / 2500000000000000 : ℝ) ≤
      (-(2858972133708537061617 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (598579856134173 / 2500000000000000 : ℚ))
        (r' := (598579856134173 / 312500000000000 : ℚ))
        (U := (-(2858972133708537061617 / 2000000000000000000000 : ℚ)))
        (U' := (1299910948091462938383 / 2000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (3934214662491 / 16000000000000 : ℚ))
      (s := (2394251903101509 / 10000000000000000 : ℚ))
      (q := (598579856134173 / 2500000000000000 : ℚ))
      (U := (-(2858972133708537061617 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_289_2 :
    Uω (aρ 2) (bρ 2) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(3599058189717142384657 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2370170317116863 / 10000000000000000 : ℝ) ≤
      (-(3599058189717142384657 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2370170317116863 / 10000000000000000 : ℚ))
        (r' := (2370170317116863 / 1250000000000000 : ℚ))
        (U := (-(3599058189717142384657 / 2500000000000000000000 : ℚ)))
        (U' := (1599545662532857615343 / 2500000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (3934214662491 / 16000000000000 : ℚ))
      (s := (2369722700771851 / 10000000000000000 : ℚ))
      (q := (2370170317116863 / 10000000000000000 : ℚ))
      (U := (-(3599058189717142384657 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_289_3 :
    Uω (aρ 3) (bρ 3) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(7301580997444027247323 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4643257063317437 / 20000000000000000 : ℝ) ≤
      (-(7301580997444027247323 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4643257063317437 / 20000000000000000 : ℚ))
        (r' := (4643257063317437 / 2500000000000000 : ℚ))
        (U := (-(7301580997444027247323 / 5000000000000000000000 : ℚ)))
        (U' := (3095626707055972752677 / 5000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (3934214662491 / 16000000000000 : ℚ))
      (s := (1160017618102781 / 5000000000000000 : ℚ))
      (q := (4643257063317437 / 20000000000000000 : ℚ))
      (U := (-(7301580997444027247323 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_289_4 :
    Uω (aρ 4) (bρ 4) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(1496005898479066858877 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4480462932766027 / 20000000000000000 : ℝ) ≤
      (-(1496005898479066858877 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4480462932766027 / 20000000000000000 : ℚ))
        (r' := (4480462932766027 / 2500000000000000 : ℚ))
        (U := (-(1496005898479066858877 / 1000000000000000000000 : ℚ)))
        (U' := (583435642420933141123 / 1000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (3934214662491 / 16000000000000 : ℚ))
      (s := (139720955419947 / 625000000000000 : ℚ))
      (q := (4480462932766027 / 20000000000000000 : ℚ))
      (U := (-(1496005898479066858877 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_289_5 :
    Uω (aρ 5) (bρ 5) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(3884839687161393204871 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4228284680407637 / 20000000000000000 : ℝ) ≤
      (-(3884839687161393204871 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4228284680407637 / 20000000000000000 : ℚ))
        (r' := (4228284680407637 / 2500000000000000 : ℚ))
        (U := (-(3884839687161393204871 / 2500000000000000000000 : ℚ)))
        (U' := (1313764165088606795129 / 2500000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (3934214662491 / 16000000000000 : ℚ))
      (s := (1050773476847881 / 5000000000000000 : ℚ))
      (q := (4228284680407637 / 20000000000000000 : ℚ))
      (U := (-(3884839687161393204871 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_289_6 :
    Uω (aρ 6) (bρ 6) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(16462753974742707140679 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3855331036449663 / 20000000000000000 : ℝ) ≤
      (-(16462753974742707140679 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3855331036449663 / 20000000000000000 : ℚ))
        (r' := (3855331036449663 / 2500000000000000 : ℚ))
        (U := (-(16462753974742707140679 / 10000000000000000000000 : ℚ)))
        (U' := (4331661434257292859321 / 10000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (3934214662491 / 16000000000000 : ℚ))
      (s := (473958421219447 / 2500000000000000 : ℚ))
      (q := (3855331036449663 / 20000000000000000 : ℚ))
      (U := (-(16462753974742707140679 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_289_7 :
    Uω (aρ 7) (bρ 7) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(17972110093080970712811 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3315210972743653 / 20000000000000000 : ℝ) ≤
      (-(17972110093080970712811 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3315210972743653 / 20000000000000000 : ℚ))
        (r' := (3315210972743653 / 2500000000000000 : ℚ))
        (U := (-(17972110093080970712811 / 10000000000000000000000 : ℚ)))
        (U' := (2822305315919029287189 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (3934214662491 / 16000000000000 : ℚ))
      (s := (789687500965889 / 5000000000000000 : ℚ))
      (q := (3315210972743653 / 20000000000000000 : ℚ))
      (U := (-(17972110093080970712811 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_289_8 :
    Uω (aρ 8) (bρ 8) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(519740407477164840823 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2501200065417611 / 20000000000000000 : ℝ) ≤
      (-(519740407477164840823 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2501200065417611 / 20000000000000000 : ℚ))
        (r' := (2501200065417611 / 2500000000000000 : ℚ))
        (U := (-(519740407477164840823 / 250000000000000000000 : ℚ)))
        (U' := (119977747835159177 / 250000000000000000000 : ℚ))
        3 2 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (3934214662491 / 16000000000000 : ℚ))
      (s := (131113218243217 / 1250000000000000 : ℚ))
      (q := (2501200065417611 / 20000000000000000 : ℚ))
      (U := (-(519740407477164840823 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_289_9 :
    Uω (aρ 9) (bρ 9) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_289_10 :
    Uω (aρ 10) (bρ 10) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_289_11 :
    Uω (aρ 11) (bρ 11) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_289_12 :
    Uω (aρ 12) (bρ 12) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_289_13 :
    Uω (aρ 13) (bρ 13) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_289_14 :
    Uω (aρ 14) (bρ 14) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_289_15 :
    Uω (aρ 15) (bρ 15) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_289_16 :
    Uω (aρ 16) (bρ 16) (3934214662491 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_289 :
    Uρ (3934214662491 / 16000000000000 : ℝ) ≤
      (-(1126339213224684761437 / 625000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_289_1 U_289_2 U_289_3 U_289_4 U_289_5 U_289_6 U_289_7 U_289_8 U_289_9 U_289_10
    U_289_11 U_289_12 U_289_13 U_289_14 U_289_15 U_289_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_290_1 :
    Uω (aρ 1) (bρ 1) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(14206187211916833637463 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (966258037522081 / 4000000000000000 : ℝ) ≤
      (-(14206187211916833637463 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (966258037522081 / 4000000000000000 : ℚ))
        (r' := (966258037522081 / 500000000000000 : ℚ))
        (U := (-(14206187211916833637463 / 10000000000000000000000 : ℚ)))
        (U' := (6588228197083166362537 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1984167389789 / 8000000000000 : ℚ))
      (s := (483115633691831 / 2000000000000000 : ℚ))
      (q := (966258037522081 / 4000000000000000 : ℚ))
      (U := (-(14206187211916833637463 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_290_2 :
    Uω (aρ 2) (bρ 2) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(14306645663022064867043 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4782998764904191 / 20000000000000000 : ℝ) ≤
      (-(14306645663022064867043 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4782998764904191 / 20000000000000000 : ℚ))
        (r' := (4782998764904191 / 2500000000000000 : ℚ))
        (U := (-(14306645663022064867043 / 10000000000000000000000 : ℚ)))
        (U' := (6487769745977935132957 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1984167389789 / 8000000000000 : ℚ))
      (s := (2391055758262941 / 10000000000000000 : ℚ))
      (q := (4782998764904191 / 20000000000000000 : ℚ))
      (U := (-(14306645663022064867043 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_290_3 :
    Uω (aρ 3) (bρ 3) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(1813958175975205347013 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (146435507278643 / 625000000000000 : ℝ) ≤
      (-(1813958175975205347013 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (146435507278643 / 625000000000000 : ℚ))
        (r' := (146435507278643 / 78125000000000 : ℚ))
        (U := (-(1813958175975205347013 / 1250000000000000000000 : ℚ)))
        (U' := (785343750149794652987 / 1250000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1984167389789 / 8000000000000 : ℚ))
      (s := (1170694666312663 / 5000000000000000 : ℚ))
      (q := (146435507278643 / 625000000000000 : ℚ))
      (U := (-(1813958175975205347013 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_290_4 :
    Uω (aρ 4) (bρ 4) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(92907010073051215021 / 62500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2261600912890833 / 10000000000000000 : ℝ) ≤
      (-(92907010073051215021 / 62500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2261600912890833 / 10000000000000000 : ℚ))
        (r' := (2261600912890833 / 1250000000000000 : ℚ))
        (U := (-(92907010073051215021 / 62500000000000000000 : ℚ)))
        (U' := (37058086233198784979 / 62500000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1984167389789 / 8000000000000 : ℚ))
      (s := (282118638319427 / 1250000000000000 : ℚ))
      (q := (2261600912890833 / 10000000000000000 : ℚ))
      (U := (-(92907010073051215021 / 62500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_290_5 :
    Uω (aρ 5) (bρ 5) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(15438402962172249138387 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2135593931387483 / 10000000000000000 : ℝ) ≤
      (-(15438402962172249138387 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2135593931387483 / 10000000000000000 : ℚ))
        (r' := (2135593931387483 / 1250000000000000 : ℚ))
        (U := (-(15438402962172249138387 / 10000000000000000000000 : ℚ)))
        (U' := (5356012446827750861613 / 10000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1984167389789 / 8000000000000 : ℚ))
      (s := (530781265720929 / 2500000000000000 : ℚ))
      (q := (2135593931387483 / 10000000000000000 : ℚ))
      (U := (-(15438402962172249138387 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_290_6 :
    Uω (aρ 6) (bρ 6) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(4087729696628356463639 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (60917018752829 / 312500000000000 : ℝ) ≤
      (-(4087729696628356463639 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (60917018752829 / 312500000000000 : ℚ))
        (r' := (60917018752829 / 39062500000000 : ℚ))
        (U := (-(4087729696628356463639 / 2500000000000000000000 : ℚ)))
        (U' := (1110874155621643536361 / 2500000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1984167389789 / 8000000000000 : ℚ))
      (s := (958933387714903 / 5000000000000000 : ℚ))
      (q := (60917018752829 / 312500000000000 : ℚ))
      (U := (-(4087729696628356463639 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_290_7 :
    Uω (aρ 7) (bρ 7) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(1783807909004666494059 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (335994419017261 / 2000000000000000 : ℝ) ≤
      (-(1783807909004666494059 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (335994419017261 / 2000000000000000 : ℚ))
        (r' := (335994419017261 / 250000000000000 : ℚ))
        (U := (-(1783807909004666494059 / 1000000000000000000000 : ℚ)))
        (U' := (295633631895333505941 / 1000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (1984167389789 / 8000000000000 : ℚ))
      (s := (20034789327267 / 125000000000000 : ℚ))
      (q := (335994419017261 / 2000000000000000 : ℚ))
      (U := (-(1783807909004666494059 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_290_8 :
    Uω (aρ 8) (bρ 8) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(1286819084048231859999 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2551858043370813 / 20000000000000000 : ℝ) ≤
      (-(1286819084048231859999 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2551858043370813 / 20000000000000000 : ℚ))
        (r' := (2551858043370813 / 2500000000000000 : ℚ))
        (U := (-(1286819084048231859999 / 625000000000000000000 : ℚ)))
        (U' := (12831879014268140001 / 625000000000000000000 : ℚ))
        3 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (1984167389789 / 8000000000000 : ℚ))
      (s := (1078238650719563 / 10000000000000000 : ℚ))
      (q := (2551858043370813 / 20000000000000000 : ℚ))
      (U := (-(1286819084048231859999 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_290_9 :
    Uω (aρ 9) (bρ 9) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_290_10 :
    Uω (aρ 10) (bρ 10) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_290_11 :
    Uω (aρ 11) (bρ 11) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_290_12 :
    Uω (aρ 12) (bρ 12) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_290_13 :
    Uω (aρ 13) (bρ 13) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_290_14 :
    Uω (aρ 14) (bρ 14) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_290_15 :
    Uω (aρ 15) (bρ 15) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_290_16 :
    Uω (aρ 16) (bρ 16) (1984167389789 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_290 :
    Uρ (1984167389789 / 8000000000000 : ℝ) ≤
      (-(8981756148083042841929 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_290_1 U_290_2 U_290_3 U_290_4 U_290_5 U_290_6 U_290_7 U_290_8 U_290_9 U_290_10
    U_290_11 U_290_12 U_290_13 U_290_14 U_290_15 U_290_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_291_1 :
    Uω (aρ 1) (bρ 1) (504571876719 / 2000000000000 : ℝ) ≤
      (-(3507791254907928832507 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4916592802630059 / 20000000000000000 : ℝ) ≤
      (-(3507791254907928832507 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4916592802630059 / 20000000000000000 : ℚ))
        (r' := (4916592802630059 / 2500000000000000 : ℚ))
        (U := (-(3507791254907928832507 / 2500000000000000000000 : ℚ)))
        (U' := (1690812597342071167493 / 2500000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (504571876719 / 2000000000000 : ℚ))
      (s := (2458230637120059 / 10000000000000000 : ℚ))
      (q := (4916592802630059 / 20000000000000000 : ℚ))
      (U := (-(3507791254907928832507 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_291_2 :
    Uω (aρ 2) (bρ 2) (504571876719 / 2000000000000 : ℝ) ≤
      (-(7064922361463546649243 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4868314606399477 / 20000000000000000 : ℝ) ≤
      (-(7064922361463546649243 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4868314606399477 / 20000000000000000 : ℚ))
        (r' := (4868314606399477 / 2500000000000000 : ℚ))
        (U := (-(7064922361463546649243 / 5000000000000000000000 : ℚ)))
        (U' := (3332285343036453350757 / 5000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (504571876719 / 2000000000000 : ℚ))
      (s := (2433721453399477 / 10000000000000000 : ℚ))
      (q := (4868314606399477 / 20000000000000000 : ℚ))
      (U := (-(7064922361463546649243 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_291_3 :
    Uω (aρ 3) (bρ 3) (504571876719 / 2000000000000 : ℝ) ≤
      (-(14331149326100729740711 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2385646506713341 / 10000000000000000 : ℝ) ≤
      (-(14331149326100729740711 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2385646506713341 / 10000000000000000 : ℚ))
        (r' := (2385646506713341 / 1250000000000000 : ℚ))
        (U := (-(14331149326100729740711 / 10000000000000000000000 : ℚ)))
        (U' := (6463266082899270259289 / 10000000000000000000000 : ℚ))
        3 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (504571876719 / 2000000000000 : ℚ))
      (s := (1192047983388341 / 5000000000000000 : ℚ))
      (q := (2385646506713341 / 10000000000000000 : ℚ))
      (U := (-(14331149326100729740711 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_291_4 :
    Uω (aρ 4) (bρ 4) (504571876719 / 2000000000000 : ℝ) ≤
      (-(14677919486345039845707 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2304337332011151 / 10000000000000000 : ℝ) ≤
      (-(14677919486345039845707 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2304337332011151 / 10000000000000000 : ℚ))
        (r' := (2304337332011151 / 1250000000000000 : ℚ))
        (U := (-(14677919486345039845707 / 10000000000000000000000 : ℚ)))
        (U' := (6116495922654960154293 / 10000000000000000000000 : ℚ))
        3 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (504571876719 / 2000000000000 : ℚ))
      (s := (1149885899218651 / 5000000000000000 : ℚ))
      (q := (2304337332011151 / 10000000000000000 : ℚ))
      (U := (-(14677919486345039845707 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_291_5 :
    Uω (aρ 5) (bρ 5) (504571876719 / 2000000000000 : ℝ) ≤
      (-(3047906602216523433211 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2178489596664727 / 10000000000000000 : ℝ) ≤
      (-(3047906602216523433211 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2178489596664727 / 10000000000000000 : ℚ))
        (r' := (2178489596664727 / 1250000000000000 : ℚ))
        (U := (-(3047906602216523433211 / 2000000000000000000000 : ℚ)))
        (U' := (1110976479583476566789 / 2000000000000000000000 : ℚ))
        3 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (504571876719 / 2000000000000 : ℚ))
      (s := (1083133123539727 / 5000000000000000 : ℚ))
      (q := (2178489596664727 / 10000000000000000 : ℚ))
      (U := (-(3047906602216523433211 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_291_6 :
    Uω (aρ 6) (bρ 6) (504571876719 / 2000000000000 : ℝ) ≤
      (-(2016381225759584278767 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3985358586130907 / 20000000000000000 : ℝ) ≤
      (-(2016381225759584278767 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3985358586130907 / 20000000000000000 : ℚ))
        (r' := (3985358586130907 / 2500000000000000 : ℚ))
        (U := (-(2016381225759584278767 / 1250000000000000000000 : ℚ)))
        (U' := (582920700365415721233 / 1250000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (504571876719 / 2000000000000 : ℚ))
      (s := (1961886015020907 / 10000000000000000 : ℚ))
      (q := (3985358586130907 / 20000000000000000 : ℚ))
      (U := (-(2016381225759584278767 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_291_7 :
    Uω (aρ 7) (bρ 7) (504571876719 / 2000000000000 : ℝ) ≤
      (-(8787890108594326096779 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (689848230502033 / 4000000000000000 : ℝ) ≤
      (-(8787890108594326096779 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (689848230502033 / 4000000000000000 : ℚ))
        (r' := (689848230502033 / 500000000000000 : ℚ))
        (U := (-(8787890108594326096779 / 5000000000000000000000 : ℚ)))
        (U' := (1609317595905673903221 / 5000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (504571876719 / 2000000000000 : ℚ))
      (s := (329885992432033 / 2000000000000000 : ℚ))
      (q := (689848230502033 / 4000000000000000 : ℚ))
      (U := (-(8787890108594326096779 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_291_8 :
    Uω (aρ 8) (bρ 8) (504571876719 / 2000000000000 : ℝ) ≤
      (-(20203793397973935609921 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2652103060454627 / 20000000000000000 : ℝ) ≤
      (-(20203793397973935609921 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2652103060454627 / 20000000000000000 : ℚ))
        (r' := (2652103060454627 / 2500000000000000 : ℚ))
        (U := (-(20203793397973935609921 / 10000000000000000000000 : ℚ)))
        (U' := (590622011026064390079 / 10000000000000000000000 : ℚ))
        3 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (504571876719 / 2000000000000 : ℚ))
      (s := (1135833521444627 / 10000000000000000 : ℚ))
      (q := (2652103060454627 / 20000000000000000 : ℚ))
      (U := (-(20203793397973935609921 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_291_9 :
    Uω (aρ 9) (bρ 9) (504571876719 / 2000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_291_10 :
    Uω (aρ 10) (bρ 10) (504571876719 / 2000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_291_11 :
    Uω (aρ 11) (bρ 11) (504571876719 / 2000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_291_12 :
    Uω (aρ 12) (bρ 12) (504571876719 / 2000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_291_13 :
    Uω (aρ 13) (bρ 13) (504571876719 / 2000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_291_14 :
    Uω (aρ 14) (bρ 14) (504571876719 / 2000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_291_15 :
    Uω (aρ 15) (bρ 15) (504571876719 / 2000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_291_16 :
    Uω (aρ 16) (bρ 16) (504571876719 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_291 :
    Uρ (504571876719 / 2000000000000 : ℝ) ≤
      (-(8925212957824183781139 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_291_1 U_291_2 U_291_3 U_291_4 U_291_5 U_291_6 U_291_7 U_291_8 U_291_9 U_291_10
    U_291_11 U_291_12 U_291_13 U_291_14 U_291_15 U_291_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
