/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U39) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_472_1 :
    Uω (aρ 1) (bρ 1) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(3266333803415444261449 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8325490568660087 / 16000000000000000 : ℝ) ≤
      (-(3266333803415444261449 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8325490568660087 / 16000000000000000 : ℚ))
        (r' := (8325490568660087 / 8000000000000000 : ℚ))
        (U := (-(3266333803415444261449 / 5000000000000000000000 : ℚ)))
        (U' := (199402098084555738551 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (520340053593839 / 1000000000000000 : ℚ))
      (q := (8325490568660087 / 16000000000000000 : ℚ))
      (U := (-(3266333803415444261449 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_2 :
    Uω (aρ 2) (bρ 2) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(3289393613990012216949 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41435910640050719 / 80000000000000000 : ℝ) ≤
      (-(3289393613990012216949 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41435910640050719 / 80000000000000000 : ℚ))
        (r' := (41435910640050719 / 40000000000000000 : ℚ))
        (U := (-(3289393613990012216949 / 5000000000000000000000 : ℚ)))
        (U' := (176342287509987783051 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (5179283997635961 / 10000000000000000 : ℚ))
      (q := (41435910640050719 / 80000000000000000 : ℚ))
      (U := (-(3289393613990012216949 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_3 :
    Uω (aρ 3) (bρ 3) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(3335860642552980259753 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41052613736908707 / 80000000000000000 : ℝ) ≤
      (-(3335860642552980259753 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41052613736908707 / 80000000000000000 : ℚ))
        (r' := (41052613736908707 / 40000000000000000 : ℚ))
        (U := (-(3335860642552980259753 / 5000000000000000000000 : ℚ)))
        (U' := (129875258947019740247 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (2565427939100229 / 5000000000000000 : ℚ))
      (q := (41052613736908707 / 80000000000000000 : ℚ))
      (U := (-(3335860642552980259753 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_4 :
    Uω (aρ 4) (bρ 4) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(853520683420242002753 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40415367151409243 / 80000000000000000 : ℝ) ≤
      (-(853520683420242002753 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (40415367151409243 / 80000000000000000 : ℚ))
        (r' := (40415367151409243 / 40000000000000000 : ℚ))
        (U := (-(853520683420242002753 / 1250000000000000000000 : ℚ)))
        (U' := (12913291954757997247 / 1250000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (157807450402831 / 312500000000000 : ℚ))
      (q := (40415367151409243 / 80000000000000000 : ℚ))
      (U := (-(853520683420242002753 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_5 :
    Uω (aρ 5) (bρ 5) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(3535812079804980335119 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (39443300810923579 / 80000000000000000 : ℝ) ≤
      (-(3535812079804980335119 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (39443300810923579 / 80000000000000000 : ℚ))
        (r' := (39443300810923579 / 20000000000000000 : ℚ))
        (U := (-(3535812079804980335119 / 5000000000000000000000 : ℚ)))
        (U' := (3395659723195019664881 / 5000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (307813234194011 / 625000000000000 : ℚ))
      (q := (39443300810923579 / 80000000000000000 : ℚ))
      (U := (-(3535812079804980335119 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_6 :
    Uω (aρ 6) (bρ 6) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(743247428260968271397 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7609072561782843 / 16000000000000000 : ℝ) ≤
      (-(743247428260968271397 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7609072561782843 / 16000000000000000 : ℚ))
        (r' := (7609072561782843 / 4000000000000000 : ℚ))
        (U := (-(743247428260968271397 / 1000000000000000000000 : ℚ)))
        (U' := (643046932339031728603 / 1000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (948553524348367 / 2000000000000000 : ℚ))
      (q := (7609072561782843 / 16000000000000000 : ℚ))
      (U := (-(743247428260968271397 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_7 :
    Uω (aρ 7) (bρ 7) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(397457265176319725381 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7225917325218623 / 16000000000000000 : ℝ) ≤
      (-(397457265176319725381 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7225917325218623 / 16000000000000000 : ℚ))
        (r' := (7225917325218623 / 4000000000000000 : ℚ))
        (U := (-(397457265176319725381 / 500000000000000000000 : ℚ)))
        (U' := (295689915123680274619 / 500000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (56093561959957 / 125000000000000 : ℚ))
      (q := (7225917325218623 / 16000000000000000 : ℚ))
      (U := (-(397457265176319725381 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_8 :
    Uω (aρ 8) (bρ 8) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(8671834233232153227217 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33610657723676827 / 80000000000000000 : ℝ) ≤
      (-(8671834233232153227217 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (33610657723676827 / 80000000000000000 : ℚ))
        (r' := (33610657723676827 / 20000000000000000 : ℚ))
        (U := (-(8671834233232153227217 / 10000000000000000000000 : ℚ)))
        (U' := (5191109372767846772783 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (517661797816561 / 1250000000000000 : ℚ))
      (q := (33610657723676827 / 80000000000000000 : ℚ))
      (U := (-(8671834233232153227217 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_9 :
    Uω (aρ 9) (bρ 9) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(1209062573808391051687 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30410154283032899 / 80000000000000000 : ℝ) ≤
      (-(1209062573808391051687 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30410154283032899 / 80000000000000000 : ℚ))
        (r' := (30410154283032899 / 20000000000000000 : ℚ))
        (U := (-(1209062573808391051687 / 1250000000000000000000 : ℚ)))
        (U' := (523805376941608948313 / 1250000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (1841067075365753 / 5000000000000000 : ℚ))
      (q := (30410154283032899 / 80000000000000000 : ℚ))
      (U := (-(1209062573808391051687 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_10 :
    Uω (aρ 10) (bρ 10) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(11074084550028256930173 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5286626166611991 / 16000000000000000 : ℝ) ≤
      (-(11074084550028256930173 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5286626166611991 / 16000000000000000 : ℚ))
        (r' := (5286626166611991 / 4000000000000000 : ℚ))
        (U := (-(11074084550028256930173 / 10000000000000000000000 : ℚ)))
        (U' := (2788859055971743069827 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (307643732173327 / 1000000000000000 : ℚ))
      (q := (5286626166611991 / 16000000000000000 : ℚ))
      (U := (-(11074084550028256930173 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_11 :
    Uω (aρ 11) (bρ 11) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(263285150516408844729 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21447345430718583 / 80000000000000000 : ℝ) ≤
      (-(263285150516408844729 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21447345430718583 / 80000000000000000 : ℚ))
        (r' := (21447345430718583 / 20000000000000000 : ℚ))
        (U := (-(263285150516408844729 / 200000000000000000000 : ℚ)))
        (U' := (13973721603591155271 / 200000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (2248467597352927 / 10000000000000000 : ℚ))
      (q := (21447345430718583 / 80000000000000000 : ℚ))
      (U := (-(263285150516408844729 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_12 :
    Uω (aρ 12) (bρ 12) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(3509569916371714106323 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13835554275365503 / 80000000000000000 : ℝ) ≤
      (-(3509569916371714106323 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13835554275365503 / 80000000000000000 : ℚ))
        (r' := (13835554275365503 / 10000000000000000 : ℚ))
        (U := (-(3509569916371714106323 / 2000000000000000000000 : ℚ)))
        (U' := (649313165428285893677 / 2000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (33714943315019 / 64000000000000 : ℚ))
      (s := (769219905199657 / 10000000000000000 : ℚ))
      (q := (13835554275365503 / 80000000000000000 : ℚ))
      (U := (-(3509569916371714106323 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_472_13 :
    Uω (aρ 13) (bρ 13) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_472_14 :
    Uω (aρ 14) (bρ 14) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_472_15 :
    Uω (aρ 15) (bρ 15) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_472_16 :
    Uω (aρ 16) (bρ 16) (33714943315019 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_472 :
    Uρ (33714943315019 / 64000000000000 : ℝ) ≤
      (-(10078300210227161819509 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_472_1 U_472_2 U_472_3 U_472_4 U_472_5 U_472_6 U_472_7 U_472_8 U_472_9 U_472_10
    U_472_11 U_472_12 U_472_13 U_472_14 U_472_15 U_472_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_473_1 :
    Uω (aρ 1) (bρ 1) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(6508707550010153423257 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4172731204067239 / 8000000000000000 : ℝ) ≤
      (-(6508707550010153423257 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4172731204067239 / 8000000000000000 : ℚ))
        (r' := (4172731204067239 / 4000000000000000 : ℚ))
        (U := (-(6508707550010153423257 / 10000000000000000000000 : ℚ)))
        (U' := (422764252989846576743 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (521588300996341 / 1000000000000000 : ℚ))
      (q := (4172731204067239 / 8000000000000000 : ℚ))
      (U := (-(6508707550010153423257 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_2 :
    Uω (aρ 2) (bρ 2) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(3277357870479055754481 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20767886591173289 / 40000000000000000 : ℝ) ≤
      (-(3277357870479055754481 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20767886591173289 / 40000000000000000 : ℚ))
        (r' := (20767886591173289 / 20000000000000000 : ℚ))
        (U := (-(3277357870479055754481 / 5000000000000000000000 : ℚ)))
        (U' := (188378031020944245519 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (5191767307891957 / 10000000000000000 : ℚ))
      (q := (20767886591173289 / 40000000000000000 : ℚ))
      (U := (-(3277357870479055754481 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_3 :
    Uω (aρ 3) (bρ 3) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(830927859826774090171 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20576243167316043 / 40000000000000000 : ℝ) ≤
      (-(830927859826774090171 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20576243167316043 / 40000000000000000 : ℚ))
        (r' := (20576243167316043 / 20000000000000000 : ℚ))
        (U := (-(830927859826774090171 / 1250000000000000000000 : ℚ)))
        (U' := (35506115548225909829 / 1250000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (2571670851156667 / 5000000000000000 : ℚ))
      (q := (20576243167316043 / 40000000000000000 : ℚ))
      (U := (-(830927859826774090171 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_4 :
    Uω (aρ 4) (bρ 4) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(6803477725022190286487 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20257633416314663 / 40000000000000000 : ℝ) ≤
      (-(6803477725022190286487 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20257633416314663 / 40000000000000000 : ℚ))
        (r' := (20257633416314663 / 20000000000000000 : ℚ))
        (U := (-(6803477725022190286487 / 10000000000000000000000 : ℚ)))
        (U' := (127994077977809713513 / 10000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (1265582751969411 / 2500000000000000 : ℚ))
      (q := (20257633416314663 / 40000000000000000 : ℚ))
      (U := (-(6803477725022190286487 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_5 :
    Uω (aρ 5) (bρ 5) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(704631153085188042397 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19771634321509881 / 40000000000000000 : ℝ) ≤
      (-(704631153085188042397 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19771634321509881 / 40000000000000000 : ℚ))
        (r' := (19771634321509881 / 10000000000000000 : ℚ))
        (U := (-(704631153085188042397 / 1000000000000000000000 : ℚ)))
        (U' := (681663207514811957603 / 1000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (4937521379810253 / 10000000000000000 : ℚ))
      (q := (19771634321509881 / 40000000000000000 : ℚ))
      (U := (-(704631153085188042397 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_6 :
    Uω (aρ 6) (bρ 6) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(7406190390433035913379 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19072746181188913 / 40000000000000000 : ℝ) ≤
      (-(7406190390433035913379 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19072746181188913 / 40000000000000000 : ℚ))
        (r' := (19072746181188913 / 10000000000000000 : ℚ))
        (U := (-(7406190390433035913379 / 10000000000000000000000 : ℚ)))
        (U' := (6456753215566964086621 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (4755317684789769 / 10000000000000000 : ℚ))
      (q := (19072746181188913 / 40000000000000000 : ℚ))
      (U := (-(7406190390433035913379 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_7 :
    Uω (aρ 7) (bρ 7) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(7921368550378337604691 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3623008239469197 / 8000000000000000 : ℝ) ≤
      (-(7921368550378337604691 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3623008239469197 / 8000000000000000 : ℚ))
        (r' := (3623008239469197 / 2000000000000000 : ℚ))
        (U := (-(7921368550378337604691 / 10000000000000000000000 : ℚ)))
        (U' := (5941575055621662395309 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (900025314725661 / 2000000000000000 : ℚ))
      (q := (3623008239469197 / 8000000000000000 : ℚ))
      (U := (-(7921368550378337604691 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_8 :
    Uω (aρ 8) (bρ 8) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(4320869877513572204633 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16855979799603761 / 40000000000000000 : ℝ) ≤
      (-(4320869877513572204633 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16855979799603761 / 40000000000000000 : ℚ))
        (r' := (16855979799603761 / 10000000000000000 : ℚ))
        (U := (-(4320869877513572204633 / 5000000000000000000000 : ℚ)))
        (U' := (2610601925486427795367 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (4154137526097193 / 10000000000000000 : ℚ))
      (q := (16855979799603761 / 40000000000000000 : ℚ))
      (U := (-(4320869877513572204633 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_9 :
    Uω (aρ 9) (bρ 9) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(1927732381998579928349 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (610264650713451 / 1600000000000000 : ℝ) ≤
      (-(1927732381998579928349 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (610264650713451 / 1600000000000000 : ℚ))
        (r' := (610264650713451 / 400000000000000 : ℚ))
        (U := (-(1927732381998579928349 / 2000000000000000000000 : ℚ)))
        (U' := (844856339201420071651 / 2000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (73908427771469 / 200000000000000 : ℚ))
      (q := (610264650713451 / 1600000000000000 : ℚ))
      (U := (-(1927732381998579928349 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_10 :
    Uω (aρ 10) (bρ 10) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(11033604756957846854013 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13270174230327283 / 40000000000000000 : ℝ) ≤
      (-(11033604756957846854013 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13270174230327283 / 40000000000000000 : ℚ))
        (r' := (13270174230327283 / 10000000000000000 : ℚ))
        (U := (-(11033604756957846854013 / 10000000000000000000000 : ℚ)))
        (U' := (2829338849042153145987 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (1545379701656977 / 5000000000000000 : ℚ))
      (q := (13270174230327283 / 40000000000000000 : ℚ))
      (U := (-(11033604756957846854013 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_11 :
    Uω (aρ 11) (bρ 11) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(262179094799017356733 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10783141901968263 / 40000000000000000 : ℝ) ≤
      (-(262179094799017356733 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10783141901968263 / 40000000000000000 : ℚ))
        (r' := (10783141901968263 / 10000000000000000 : ℚ))
        (U := (-(262179094799017356733 / 200000000000000000000 : ℚ)))
        (U' := (15079777320982643267 / 200000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (566429966334861 / 2500000000000000 : ℚ))
      (q := (10783141901968263 / 40000000000000000 : ℚ))
      (U := (-(262179094799017356733 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_12 :
    Uω (aρ 12) (bρ 12) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(17389943031897199826591 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7027880383189607 / 40000000000000000 : ℝ) ≤
      (-(17389943031897199826591 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7027880383189607 / 40000000000000000 : ℚ))
        (r' := (7027880383189607 / 5000000000000000 : ℚ))
        (U := (-(17389943031897199826591 / 10000000000000000000000 : ℚ)))
        (U' := (3404472377102800173409 / 10000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (16897415098527 / 32000000000000 : ℚ))
      (s := (202947300658779 / 2500000000000000 : ℚ))
      (q := (7027880383189607 / 40000000000000000 : ℚ))
      (U := (-(17389943031897199826591 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_473_13 :
    Uω (aρ 13) (bρ 13) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_473_14 :
    Uω (aρ 14) (bρ 14) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_473_15 :
    Uω (aρ 15) (bρ 15) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_473_16 :
    Uω (aρ 16) (bρ 16) (16897415098527 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_473 :
    Uρ (16897415098527 / 32000000000000 : ℝ) ≤
      (-(1255512523990723562393 / 1250000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_473_1 U_473_2 U_473_3 U_473_4 U_473_5 U_473_6 U_473_7 U_473_8 U_473_9 U_473_10
    U_473_11 U_473_12 U_473_13 U_473_14 U_473_15 U_473_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_474_1 :
    Uω (aρ 1) (bρ 1) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(25939219060423466283 / 40000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41827171235204113 / 80000000000000000 : ℝ) ≤
      (-(25939219060423466283 / 40000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41827171235204113 / 80000000000000000 : ℚ))
        (r' := (41827171235204113 / 40000000000000000 : ℚ))
        (U := (-(25939219060423466283 / 40000000000000000000 : ℚ)))
        (U' := (1786668151576533717 / 40000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (1307091370819593 / 2500000000000000 : ℚ))
      (q := (41827171235204113 / 80000000000000000 : ℚ))
      (U := (-(25939219060423466283 / 40000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_2 :
    Uω (aρ 2) (bρ 2) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(1306140412601594962099 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8327127141148561 / 16000000000000000 : ℝ) ≤
      (-(1306140412601594962099 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8327127141148561 / 16000000000000000 : ℚ))
        (r' := (8327127141148561 / 8000000000000000 : ℚ))
        (U := (-(1306140412601594962099 / 2000000000000000000000 : ℚ)))
        (U' := (80153947998405037901 / 2000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (1040850122684609 / 2000000000000000 : ℚ))
      (q := (8327127141148561 / 16000000000000000 : ℚ))
      (U := (-(1306140412601594962099 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_3 :
    Uω (aρ 3) (bρ 3) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(3311591693361606929099 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41252358864580941 / 80000000000000000 : ℝ) ≤
      (-(3311591693361606929099 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41252358864580941 / 80000000000000000 : ℚ))
        (r' := (41252358864580941 / 40000000000000000 : ℚ))
        (U := (-(3311591693361606929099 / 5000000000000000000000 : ℚ)))
        (U' := (154144208138393070901 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (5155827509482579 / 10000000000000000 : ℚ))
      (q := (41252358864580941 / 80000000000000000 : ℚ))
      (U := (-(3311591693361606929099 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_4 :
    Uω (aρ 4) (bρ 4) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(677885083085293050957 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40615166311687373 / 80000000000000000 : ℝ) ≤
      (-(677885083085293050957 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (40615166311687373 / 80000000000000000 : ℚ))
        (r' := (40615166311687373 / 40000000000000000 : ℚ))
        (U := (-(677885083085293050957 / 1000000000000000000000 : ℚ)))
        (U' := (15262097214706949043 / 1000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (5074823552324187 / 10000000000000000 : ℚ))
      (q := (40615166311687373 / 80000000000000000 : ℚ))
      (U := (-(677885083085293050957 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_5 :
    Uω (aρ 5) (bρ 5) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(28084251809523764379 / 40000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (39643235923632449 / 80000000000000000 : ℝ) ≤
      (-(28084251809523764379 / 40000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (39643235923632449 / 80000000000000000 : ℚ))
        (r' := (39643235923632449 / 20000000000000000 : ℚ))
        (U := (-(28084251809523764379 / 40000000000000000000 : ℚ)))
        (U' := (27367522614476235621 / 40000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (309376929665341 / 625000000000000 : ℚ))
      (q := (39643235923632449 / 80000000000000000 : ℚ))
      (U := (-(28084251809523764379 / 40000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_6 :
    Uω (aρ 6) (bρ 6) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(1475995154688466043879 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (38245620493287529 / 80000000000000000 : ℝ) ≤
      (-(1475995154688466043879 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (38245620493287529 / 80000000000000000 : ℚ))
        (r' := (38245620493287529 / 20000000000000000 : ℚ))
        (U := (-(1475995154688466043879 / 2000000000000000000000 : ℚ)))
        (U' := (1296593566511533956121 / 2000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (2383933696099613 / 5000000000000000 : ℚ))
      (q := (38245620493287529 / 80000000000000000 : ℚ))
      (U := (-(1475995154688466043879 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_7 :
    Uω (aρ 7) (bρ 7) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(7893669714757767057957 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36330574615994797 / 80000000000000000 : ℝ) ≤
      (-(7893669714757767057957 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (36330574615994797 / 80000000000000000 : ℚ))
        (r' := (36330574615994797 / 20000000000000000 : ℚ))
        (U := (-(7893669714757767057957 / 10000000000000000000000 : ℚ)))
        (U' := (5969273891242232942043 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (4512767303636043 / 10000000000000000 : ℚ))
      (q := (36330574615994797 / 80000000000000000 : ℚ))
      (U := (-(7893669714757767057957 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_8 :
    Uω (aρ 8) (bρ 8) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(8611738167075583192321 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33813252703021321 / 80000000000000000 : ℝ) ≤
      (-(8611738167075583192321 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (33813252703021321 / 80000000000000000 : ℚ))
        (r' := (33813252703021321 / 20000000000000000 : ℚ))
        (U := (-(8611738167075583192321 / 10000000000000000000000 : ℚ)))
        (U' := (5251205438924416807679 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (2083489238366337 / 5000000000000000 : ℚ))
      (q := (33813252703021321 / 80000000000000000 : ℚ))
      (U := (-(8611738167075583192321 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_9 :
    Uω (aρ 9) (bρ 9) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(9604944656117145227967 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30616288416902789 / 80000000000000000 : ℝ) ≤
      (-(9604944656117145227967 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30616288416902789 / 80000000000000000 : ℚ))
        (r' := (30616288416902789 / 20000000000000000 : ℚ))
        (U := (-(9604944656117145227967 / 10000000000000000000000 : ℚ)))
        (U' := (4257998949882854772033 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (3708703033563041 / 10000000000000000 : ℚ))
      (q := (30616288416902789 / 80000000000000000 : ℚ))
      (U := (-(9604944656117145227967 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_10 :
    Uω (aρ 10) (bρ 10) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(5496656002181523759141 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5329500512359669 / 16000000000000000 : ℝ) ≤
      (-(5496656002181523759141 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5329500512359669 / 16000000000000000 : ℚ))
        (r' := (5329500512359669 / 4000000000000000 : ℚ))
        (U := (-(5496656002181523759141 / 5000000000000000000000 : ℚ)))
        (U' := (1434815800818476240859 / 5000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (310506560328193 / 1000000000000000 : ℚ))
      (q := (5329500512359669 / 16000000000000000 : ℚ))
      (U := (-(5496656002181523759141 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_11 :
    Uω (aρ 11) (bρ 11) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(13054070711118162002301 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4336994733821961 / 16000000000000000 : ℝ) ≤
      (-(13054070711118162002301 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4336994733821961 / 16000000000000000 : ℚ))
        (r' := (4336994733821961 / 4000000000000000 : ℚ))
        (U := (-(13054070711118162002301 / 10000000000000000000000 : ℚ)))
        (U' := (808872894881837997699 / 10000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (456582001262959 / 2000000000000000 : ℚ))
      (q := (4336994733821961 / 16000000000000000 : ℚ))
      (U := (-(13054070711118162002301 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_12 :
    Uω (aρ 12) (bρ 12) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(17239930913919872437509 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14268203677230981 / 80000000000000000 : ℝ) ≤
      (-(17239930913919872437509 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (14268203677230981 / 80000000000000000 : ℚ))
        (r' := (14268203677230981 / 10000000000000000 : ℚ))
        (U := (-(17239930913919872437509 / 10000000000000000000000 : ℚ)))
        (U' := (3554484495080127562491 / 10000000000000000000000 : ℚ))
        3 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (33874717079089 / 64000000000000 : ℚ))
      (s := (852417605030089 / 10000000000000000 : ℚ))
      (q := (14268203677230981 / 80000000000000000 : ℚ))
      (U := (-(17239930913919872437509 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_474_13 :
    Uω (aρ 13) (bρ 13) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_474_14 :
    Uω (aρ 14) (bρ 14) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_474_15 :
    Uω (aρ 15) (bρ 15) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_474_16 :
    Uω (aρ 16) (bρ 16) (33874717079089 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_474 :
    Uρ (33874717079089 / 64000000000000 : ℝ) ≤
      (-(2002109681776138421131 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_474_1 U_474_2 U_474_3 U_474_4 U_474_5 U_474_6 U_474_7 U_474_8 U_474_9 U_474_10
    U_474_11 U_474_12 U_474_13 U_474_14 U_474_15 U_474_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_475_1 :
    Uω (aρ 1) (bρ 1) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(6460958978972525251067 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5240878803364487 / 10000000000000000 : ℝ) ≤
      (-(6460958978972525251067 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5240878803364487 / 10000000000000000 : ℚ))
        (r' := (5240878803364487 / 5000000000000000 : ℚ))
        (U := (-(6460958978972525251067 / 10000000000000000000000 : ℚ)))
        (U' := (470512824027474748933 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (5240847955888349 / 10000000000000000 : ℚ))
      (q := (5240878803364487 / 10000000000000000 : ℚ))
      (U := (-(6460958978972525251067 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_2 :
    Uω (aρ 2) (bρ 2) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(3253372958554693937133 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1043387455259377 / 2000000000000000 : ℝ) ≤
      (-(3253372958554693937133 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1043387455259377 / 2000000000000000 : ℚ))
        (r' := (1043387455259377 / 1000000000000000 : ℚ))
        (U := (-(3253372958554693937133 / 5000000000000000000000 : ℚ)))
        (U' := (212362942945306062867 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (1043346782852629 / 2000000000000000 : ℚ))
      (q := (1043387455259377 / 2000000000000000 : ℚ))
      (U := (-(3253372958554693937133 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_3 :
    Uω (aρ 3) (bρ 3) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(1649750631088205402597 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10338057831811619 / 20000000000000000 : ℝ) ≤
      (-(1649750631088205402597 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10338057831811619 / 20000000000000000 : ℚ))
        (r' := (10338057831811619 / 10000000000000000 : ℚ))
        (U := (-(1649750631088205402597 / 2500000000000000000000 : ℚ)))
        (U' := (83117319661794597403 / 2500000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (2584156649915497 / 5000000000000000 : ℚ))
      (q := (10338057831811619 / 20000000000000000 : ℚ))
      (U := (-(1649750631088205402597 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_4 :
    Uω (aρ 4) (bρ 4) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(3377142242700800895389 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2544691599379543 / 5000000000000000 : ℝ) ≤
      (-(3377142242700800895389 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2544691599379543 / 5000000000000000 : ℚ))
        (r' := (2544691599379543 / 2500000000000000 : ℚ))
        (U := (-(3377142242700800895389 / 5000000000000000000000 : ℚ)))
        (U' := (88593658799199104611 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (5087316046602547 / 10000000000000000 : ℚ))
      (q := (2544691599379543 / 5000000000000000 : ℚ))
      (U := (-(3377142242700800895389 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_5 :
    Uω (aρ 5) (bρ 5) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(1748969525043867698289 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9935800664233037 / 20000000000000000 : ℝ) ≤
      (-(1748969525043867698289 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9935800664233037 / 20000000000000000 : ℚ))
        (r' := (9935800664233037 / 5000000000000000 : ℚ))
        (U := (-(1748969525043867698289 / 2500000000000000000000 : ℚ)))
        (U' := (1716766376456132301711 / 2500000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (1240635058163103 / 2500000000000000 : ℚ))
      (q := (9935800664233037 / 20000000000000000 : ℚ))
      (U := (-(1748969525043867698289 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_6 :
    Uω (aρ 6) (bρ 6) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(3676915032743383951457 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2396609200802933 / 5000000000000000 : ℝ) ≤
      (-(3676915032743383951457 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2396609200802933 / 5000000000000000 : ℚ))
        (r' := (2396609200802933 / 1250000000000000 : ℚ))
        (U := (-(3676915032743383951457 / 5000000000000000000000 : ℚ)))
        (U' := (3254556770256616048543 / 5000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (4780416746771107 / 10000000000000000 : ℚ))
      (q := (2396609200802933 / 5000000000000000 : ℚ))
      (U := (-(3676915032743383951457 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_7 :
    Uω (aρ 7) (bρ 7) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(7866048355351224914357 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4553882914965921 / 10000000000000000 : ℝ) ≤
      (-(7866048355351224914357 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4553882914965921 / 10000000000000000 : ℚ))
        (r' := (4553882914965921 / 2500000000000000 : ℚ))
        (U := (-(7866048355351224914357 / 10000000000000000000000 : ℚ)))
        (U' := (5996895250648775085643 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (4525407154251217 / 10000000000000000 : ℚ))
      (q := (4553882914965921 / 10000000000000000 : ℚ))
      (U := (-(7866048355351224914357 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_8 :
    Uω (aρ 8) (bρ 8) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(858182888206397318407 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4239317139495231 / 10000000000000000 : ℝ) ≤
      (-(858182888206397318407 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4239317139495231 / 10000000000000000 : ℚ))
        (r' := (4239317139495231 / 2500000000000000 : ℚ))
        (U := (-(858182888206397318407 / 1000000000000000000000 : ℚ)))
        (U' := (528111472393602681593 / 1000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (4179817254649837 / 10000000000000000 : ℚ))
      (q := (4239317139495231 / 10000000000000000 : ℚ))
      (U := (-(858182888206397318407 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_9 :
    Uω (aρ 9) (bρ 9) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(2392836977549402281269 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1919957635388529 / 5000000000000000 : ℝ) ≤
      (-(2392836977549402281269 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1919957635388529 / 5000000000000000 : ℚ))
        (r' := (1919957635388529 / 1250000000000000 : ℚ))
        (U := (-(2392836977549402281269 / 2500000000000000000000 : ℚ)))
        (U' := (1072898923950597718731 / 2500000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (3721979145573491 / 10000000000000000 : ℚ))
      (q := (1919957635388529 / 5000000000000000 : ℚ))
      (U := (-(2392836977549402281269 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_10 :
    Uω (aρ 10) (bρ 10) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(10953204368456377232327 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (267545940105391 / 800000000000000 : ℝ) ≤
      (-(10953204368456377232327 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (267545940105391 / 800000000000000 : ℚ))
        (r' := (267545940105391 / 200000000000000 : ℚ))
        (U := (-(10953204368456377232327 / 10000000000000000000000 : ℚ)))
        (U' := (2909739237543622767673 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (62387122802983 / 200000000000000 : ℚ))
      (q := (267545940105391 / 800000000000000 : ℚ))
      (U := (-(10953204368456377232327 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_11 :
    Uω (aρ 11) (bρ 11) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(3249899421236699954177 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2725427574771609 / 10000000000000000 : ℝ) ≤
      (-(3249899421236699954177 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2725427574771609 / 10000000000000000 : ℚ))
        (r' := (2725427574771609 / 2500000000000000 : ℚ))
        (U := (-(3249899421236699954177 / 2500000000000000000000 : ℚ)))
        (U' := (215836480263300045823 / 2500000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (2300039413262593 / 10000000000000000 : ℚ))
      (q := (2725427574771609 / 10000000000000000 : ℚ))
      (U := (-(3249899421236699954177 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_12 :
    Uω (aρ 12) (bρ 12) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(854838257289714201947 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1809243093871961 / 10000000000000000 : ℝ) ≤
      (-(854838257289714201947 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1809243093871961 / 10000000000000000 : ℚ))
        (r' := (1809243093871961 / 1250000000000000 : ℚ))
        (U := (-(854838257289714201947 / 500000000000000000000 : ℚ)))
        (U' := (184882513160285798053 / 500000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (8488650990281 / 16000000000000 : ℚ))
      (s := (891370548148297 / 10000000000000000 : ℚ))
      (q := (1809243093871961 / 10000000000000000 : ℚ))
      (U := (-(854838257289714201947 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_475_13 :
    Uω (aρ 13) (bρ 13) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_475_14 :
    Uω (aρ 14) (bρ 14) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_475_15 :
    Uω (aρ 15) (bρ 15) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_475_16 :
    Uω (aρ 16) (bρ 16) (8488650990281 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_475 :
    Uρ (8488650990281 / 16000000000000 : ℝ) ≤
      (-(9977570086192114256609 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_475_1 U_475_2 U_475_3 U_475_4 U_475_5 U_475_6 U_475_7 U_475_8 U_475_9 U_475_10
    U_475_11 U_475_12 U_475_13 U_475_14 U_475_15 U_475_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_476_1 :
    Uω (aρ 1) (bρ 1) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(6437169920414059672691 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (42026889615827843 / 80000000000000000 : ℝ) ≤
      (-(6437169920414059672691 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (42026889615827843 / 80000000000000000 : ℚ))
        (r' := (42026889615827843 / 40000000000000000 : ℚ))
        (U := (-(6437169920414059672691 / 10000000000000000000000 : ℚ)))
        (U' := (494301882585940327309 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (5253330427798367 / 10000000000000000 : ℚ))
      (q := (42026889615827843 / 80000000000000000 : ℚ))
      (U := (-(6437169920414059672691 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_2 :
    Uω (aρ 2) (bρ 2) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(6482847028228737411169 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41835360696377779 / 80000000000000000 : ℝ) ≤
      (-(6482847028228737411169 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41835360696377779 / 80000000000000000 : ℚ))
        (r' := (41835360696377779 / 40000000000000000 : ℚ))
        (U := (-(6482847028228737411169 / 10000000000000000000000 : ℚ)))
        (U' := (448624774771262588831 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (5229217210445851 / 10000000000000000 : ℚ))
      (q := (41835360696377779 / 80000000000000000 : ℚ))
      (U := (-(6482847028228737411169 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_3 :
    Uω (aρ 3) (bρ 3) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(6574880008487592758289 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41452103723115147 / 80000000000000000 : ℝ) ≤
      (-(6574880008487592758289 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41452103723115147 / 80000000000000000 : ℚ))
        (r' := (41452103723115147 / 40000000000000000 : ℚ))
        (U := (-(6574880008487592758289 / 10000000000000000000000 : ℚ)))
        (U' := (356591794512407241711 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (5180799073480193 / 10000000000000000 : ℚ))
      (q := (41452103723115147 / 80000000000000000 : ℚ))
      (U := (-(6574880008487592758289 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_4 :
    Uω (aρ 4) (bρ 4) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(105152787365977387829 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1632598586770399 / 3200000000000000 : ℝ) ≤
      (-(105152787365977387829 / 156250000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1632598586770399 / 3200000000000000 : ℚ))
        (r' := (1632598586770399 / 1600000000000000 : ℚ))
        (U := (-(105152787365977387829 / 156250000000000000000 : ℚ)))
        (U' := (3151459555897612171 / 156250000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (25499042455407 / 50000000000000 : ℚ))
      (q := (1632598586770399 / 3200000000000000 : ℚ))
      (U := (-(105152787365977387829 / 156250000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_5 :
    Uω (aρ 5) (bρ 5) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(1742689163167899786689 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (39843168847047383 / 80000000000000000 : ℝ) ≤
      (-(1742689163167899786689 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (39843168847047383 / 80000000000000000 : ℚ))
        (r' := (39843168847047383 / 20000000000000000 : ℚ))
        (U := (-(1742689163167899786689 / 2500000000000000000000 : ℚ)))
        (U' := (1723046738332100213311 / 2500000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (1243762363715813 / 2500000000000000 : ℚ))
      (q := (39843168847047383 / 80000000000000000 : ℚ))
      (U := (-(1742689163167899786689 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_6 :
    Uω (aρ 6) (bρ 6) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(7327752903325907666223 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (38445872532141979 / 80000000000000000 : ℝ) ≤
      (-(7327752903325907666223 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (38445872532141979 / 80000000000000000 : ℚ))
        (r' := (38445872532141979 / 20000000000000000 : ℚ))
        (U := (-(7327752903325907666223 / 10000000000000000000000 : ℚ)))
        (U' := (6535190702674092333777 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (4792965751276901 / 10000000000000000 : ℚ))
      (q := (38445872532141979 / 80000000000000000 : ℚ))
      (U := (-(7327752903325907666223 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_7 :
    Uω (aρ 7) (bρ 7) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(244953251082135055187 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36531548535282223 / 80000000000000000 : ℝ) ≤
      (-(244953251082135055187 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (36531548535282223 / 80000000000000000 : ℚ))
        (r' := (36531548535282223 / 20000000000000000 : ℚ))
        (U := (-(244953251082135055187 / 312500000000000000000 : ℚ)))
        (U' := (188263736605364944813 / 312500000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (2269023066410981 / 5000000000000000 : ℚ))
      (q := (36531548535282223 / 80000000000000000 : ℚ))
      (U := (-(244953251082135055187 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_8 :
    Uω (aρ 8) (bρ 8) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(855201131837044779203 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (34015812917868879 / 80000000000000000 : ℝ) ≤
      (-(855201131837044779203 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (34015812917868879 / 80000000000000000 : ℚ))
        (r' := (34015812917868879 / 20000000000000000 : ℚ))
        (U := (-(855201131837044779203 / 1000000000000000000000 : ℚ)))
        (U' := (531093228762955220797 / 1000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (2096326939904313 / 5000000000000000 : ℚ))
      (q := (34015812917868879 / 80000000000000000 : ℚ))
      (U := (-(855201131837044779203 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_9 :
    Uω (aρ 9) (bρ 9) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(190757415289597866371 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30822334019602451 / 80000000000000000 : ℝ) ≤
      (-(190757415289597866371 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30822334019602451 / 80000000000000000 : ℚ))
        (r' := (30822334019602451 / 20000000000000000 : ℚ))
        (U := (-(190757415289597866371 / 200000000000000000000 : ℚ)))
        (U' := (86501456830402133629 / 200000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (3735249783602019 / 10000000000000000 : ℚ))
      (q := (30822334019602451 / 80000000000000000 : ℚ))
      (U := (-(190757415289597866371 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_10 :
    Uω (aρ 10) (bρ 10) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(10913279957409600345849 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26861623664032427 / 80000000000000000 : ℝ) ≤
      (-(10913279957409600345849 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26861623664032427 / 80000000000000000 : ℚ))
        (r' := (26861623664032427 / 20000000000000000 : ℚ))
        (U := (-(10913279957409600345849 / 10000000000000000000000 : ℚ)))
        (U' := (2949663648590399654151 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (3133631228204513 / 10000000000000000 : ℚ))
      (q := (26861623664032427 / 80000000000000000 : ℚ))
      (U := (-(10913279957409600345849 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_11 :
    Uω (aρ 11) (bρ 11) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(6472764072437904424893 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21921629978898067 / 80000000000000000 : ℝ) ≤
      (-(6472764072437904424893 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (21921629978898067 / 80000000000000000 : ℚ))
        (r' := (21921629978898067 / 20000000000000000 : ℚ))
        (U := (-(6472764072437904424893 / 5000000000000000000000 : ℚ)))
        (U' := (458707730562095575107 / 5000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (2317109433125923 / 10000000000000000 : ℚ))
      (q := (21921629978898067 / 80000000000000000 : ℚ))
      (U := (-(6472764072437904424893 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_12 :
    Uω (aρ 12) (bρ 12) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(16959611872217714546673 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14673827234924079 / 80000000000000000 : ℝ) ≤
      (-(16959611872217714546673 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (14673827234924079 / 80000000000000000 : ℚ))
        (r' := (14673827234924079 / 10000000000000000 : ℚ))
        (U := (-(16959611872217714546673 / 10000000000000000000000 : ℚ)))
        (U' := (3834803536782285453327 / 10000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (34034490843159 / 64000000000000 : ℚ))
      (s := (464429421908713 / 5000000000000000 : ℚ))
      (q := (14673827234924079 / 80000000000000000 : ℚ))
      (U := (-(16959611872217714546673 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_476_13 :
    Uω (aρ 13) (bρ 13) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_476_14 :
    Uω (aρ 14) (bρ 14) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_476_15 :
    Uω (aρ 15) (bρ 15) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_476_16 :
    Uω (aρ 16) (bρ 16) (34034490843159 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_476 :
    Uρ (34034490843159 / 64000000000000 : ℝ) ≤
      (-(62156909653359306433 / 62500000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_476_1 U_476_2 U_476_3 U_476_4 U_476_5 U_476_6 U_476_7 U_476_8 U_476_9 U_476_10
    U_476_11 U_476_12 U_476_13 U_476_14 U_476_15 U_476_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_477_1 :
    Uω (aρ 1) (bρ 1) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(1603359330041331640883 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4212674880195987 / 8000000000000000 : ℝ) ≤
      (-(1603359330041331640883 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4212674880195987 / 8000000000000000 : ℚ))
        (r' := (4212674880195987 / 4000000000000000 : ℚ))
        (U := (-(1603359330041331640883 / 2500000000000000000000 : ℚ)))
        (U' := (129508620708668359117 / 2500000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (1053162579802681 / 2000000000000000 : ℚ))
      (q := (4212674880195987 / 8000000000000000 : ℚ))
      (U := (-(1603359330041331640883 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_2 :
    Uω (aρ 2) (bρ 2) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(6459005123300066603403 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4193522316388401 / 8000000000000000 : ℝ) ≤
      (-(6459005123300066603403 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4193522316388401 / 8000000000000000 : ℚ))
        (r' := (4193522316388401 / 4000000000000000 : ℚ))
        (U := (-(6459005123300066603403 / 10000000000000000000000 : ℚ)))
        (U' := (472466679699933396597 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (131042512550111 / 250000000000000 : ℚ))
      (q := (4193522316388401 / 8000000000000000 : ℚ))
      (U := (-(6459005123300066603403 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_3 :
    Uω (aρ 3) (bρ 3) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(1310163111631396293071 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20775988026334369 / 40000000000000000 : ℝ) ≤
      (-(1310163111631396293071 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20775988026334369 / 40000000000000000 : ℚ))
        (r' := (20775988026334369 / 20000000000000000 : ℚ))
        (U := (-(1310163111631396293071 / 2000000000000000000000 : ℚ)))
        (U' := (76131248968603706929 / 2000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (2596642415275311 / 5000000000000000 : ℚ))
      (q := (20775988026334369 / 40000000000000000 : ℚ))
      (U := (-(1310163111631396293071 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_4 :
    Uω (aρ 4) (bρ 4) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(6705332253855386408567 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20457431775354757 / 40000000000000000 : ℝ) ≤
      (-(6705332253855386408567 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20457431775354757 / 40000000000000000 : ℚ))
        (r' := (20457431775354757 / 20000000000000000 : ℚ))
        (U := (-(6705332253855386408567 / 10000000000000000000000 : ℚ)))
        (U' := (226139549144613591433 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (639037610765727 / 1250000000000000 : ℚ))
      (q := (20457431775354757 / 40000000000000000 : ℚ))
      (U := (-(6705332253855386408567 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_5 :
    Uω (aρ 5) (bρ 5) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(3472849145369206145161 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19971567249032607 / 40000000000000000 : ℝ) ≤
      (-(3472849145369206145161 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19971567249032607 / 40000000000000000 : ℚ))
        (r' := (19971567249032607 / 10000000000000000 : ℚ))
        (U := (-(3472849145369206145161 / 5000000000000000000000 : ℚ)))
        (U' := (3458622657630793854839 / 5000000000000000000000 : ℚ))
        2 15 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (4987558542299741 / 10000000000000000 : ℚ))
      (q := (19971567249032607 / 40000000000000000 : ℚ))
      (U := (-(3472849145369206145161 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_6 :
    Uω (aρ 6) (bρ 6) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(7301743926598747382951 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3854599646214253 / 8000000000000000 : ℝ) ≤
      (-(7301743926598747382951 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3854599646214253 / 8000000000000000 : ℚ))
        (r' := (3854599646214253 / 2000000000000000 : ℚ))
        (U := (-(7301743926598747382951 / 10000000000000000000000 : ℚ)))
        (U' := (6561199679401252617049 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (480551440845907 / 1000000000000000 : ℚ))
      (q := (3854599646214253 / 8000000000000000 : ℚ))
      (U := (-(7301743926598747382951 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_7 :
    Uω (aρ 7) (bρ 7) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(1562207263759628217761 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18316015145861673 / 40000000000000000 : ℝ) ≤
      (-(1562207263759628217761 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (18316015145861673 / 40000000000000000 : ℚ))
        (r' := (18316015145861673 / 10000000000000000 : ℚ))
        (U := (-(1562207263759628217761 / 2000000000000000000000 : ℚ)))
        (U' := (1210381457440371782239 / 2000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (2275342123307137 / 5000000000000000 : ℚ))
      (q := (18316015145861673 / 40000000000000000 : ℚ))
      (U := (-(1562207263759628217761 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_8 :
    Uω (aρ 8) (bρ 8) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(8522284899989832254591 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17058540093797051 / 40000000000000000 : ℝ) ≤
      (-(8522284899989832254591 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (17058540093797051 / 40000000000000000 : ℚ))
        (r' := (17058540093797051 / 10000000000000000 : ℚ))
        (U := (-(8522284899989832254591 / 10000000000000000000000 : ℚ)))
        (U' := (5340658706010167745409 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (4205488371921963 / 10000000000000000 : ℚ))
      (q := (17058540093797051 / 40000000000000000 : ℚ))
      (U := (-(8522284899989832254591 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_9 :
    Uω (aρ 9) (bρ 9) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(950451232191955561317 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3092532420961119 / 8000000000000000 : ℝ) ≤
      (-(950451232191955561317 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3092532420961119 / 8000000000000000 : ℚ))
        (r' := (3092532420961119 / 2000000000000000 : ℚ))
        (U := (-(950451232191955561317 / 1000000000000000000000 : ℚ)))
        (U' := (435843128408044438683 / 1000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (749703001157247 / 2000000000000000 : ℚ))
      (q := (3092532420961119 / 8000000000000000 : ℚ))
      (U := (-(950451232191955561317 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_10 :
    Uω (aρ 10) (bρ 10) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(10873536910612324331361 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2696859236296747 / 8000000000000000 : ℝ) ≤
      (-(10873536910612324331361 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2696859236296747 / 8000000000000000 : ℚ))
        (r' := (2696859236296747 / 2000000000000000 : ℚ))
        (U := (-(10873536910612324331361 / 10000000000000000000000 : ℚ)))
        (U' := (2989406695387675668639 / 10000000000000000000000 : ℚ))
        2 8 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (629578215524061 / 2000000000000000 : ℚ))
      (q := (2696859236296747 / 8000000000000000 : ℚ))
      (U := (-(10873536910612324331361 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_11 :
    Uω (aρ 11) (bρ 11) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(12891854801988329159687 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11019803511520029 / 40000000000000000 : ℝ) ≤
      (-(12891854801988329159687 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11019803511520029 / 40000000000000000 : ℚ))
        (r' := (11019803511520029 / 10000000000000000 : ℚ))
        (U := (-(12891854801988329159687 / 10000000000000000000000 : ℚ)))
        (U' := (971088804011670840313 / 10000000000000000000000 : ℚ))
        2 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (583530342210863 / 2500000000000000 : ℚ))
      (q := (11019803511520029 / 40000000000000000 : ℚ))
      (U := (-(12891854801988329159687 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_12 :
    Uω (aρ 12) (bρ 12) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(2103474338028338746597 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7434266967437877 / 40000000000000000 : ℝ) ≤
      (-(2103474338028338746597 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7434266967437877 / 40000000000000000 : ℚ))
        (r' := (7434266967437877 / 5000000000000000 : ℚ))
        (U := (-(2103474338028338746597 / 1250000000000000000000 : ℚ)))
        (U' := (495827588096661253403 / 1250000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (17057188862597 / 32000000000000 : ℚ))
      (s := (60315824592961 / 625000000000000 : ℚ))
      (q := (7434266967437877 / 40000000000000000 : ℚ))
      (U := (-(2103474338028338746597 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_477_13 :
    Uω (aρ 13) (bρ 13) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_477_14 :
    Uω (aρ 14) (bρ 14) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_477_15 :
    Uω (aρ 15) (bρ 15) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_477_16 :
    Uω (aρ 16) (bρ 16) (17057188862597 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_477 :
    Uρ (17057188862597 / 32000000000000 : ℝ) ≤
      (-(2478276551493754470733 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_477_1 U_477_2 U_477_3 U_477_4 U_477_5 U_477_6 U_477_7 U_477_8 U_477_9 U_477_10
    U_477_11 U_477_12 U_477_13 U_477_14 U_477_15 U_477_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_478_1 :
    Uω (aρ 1) (bρ 1) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(6389760910873824690131 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (42226607985331693 / 80000000000000000 : ℝ) ≤
      (-(6389760910873824690131 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (42226607985331693 / 80000000000000000 : ℚ))
        (r' := (42226607985331693 / 40000000000000000 : ℚ))
        (U := (-(6389760910873824690131 / 10000000000000000000000 : ℚ)))
        (U' := (541710892126175309869 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (659786921192299 / 1250000000000000 : ℚ))
      (q := (42226607985331693 / 80000000000000000 : ℚ))
      (U := (-(6389760910873824690131 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_2 :
    Uω (aρ 2) (bρ 2) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(6435219931206354359771 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8407017122605121 / 16000000000000000 : ℝ) ≤
      (-(6435219931206354359771 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8407017122605121 / 16000000000000000 : ℚ))
        (r' := (8407017122605121 / 8000000000000000 : ℚ))
        (U := (-(6435219931206354359771 / 10000000000000000000000 : ℚ)))
        (U' := (496251871793645640229 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (525418378897187 / 1000000000000000 : ℚ))
      (q := (8407017122605121 / 16000000000000000 : ℚ))
      (U := (-(6435219931206354359771 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_3 :
    Uω (aρ 3) (bρ 3) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(6526808894415663314091 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41651848316384409 / 80000000000000000 : ℝ) ≤
      (-(6526808894415663314091 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41651848316384409 / 80000000000000000 : ℚ))
        (r' := (41651848316384409 / 40000000000000000 : ℚ))
        (U := (-(6526808894415663314091 / 10000000000000000000000 : ℚ)))
        (U' := (404662908584336685909 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (5205770571161571 / 10000000000000000 : ℚ))
      (q := (41651848316384409 / 80000000000000000 : ℚ))
      (U := (-(6526808894415663314091 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_4 :
    Uω (aρ 4) (bρ 4) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(1670236444950892870231 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41014762235867349 / 80000000000000000 : ℝ) ≤
      (-(1670236444950892870231 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41014762235867349 / 80000000000000000 : ℚ))
        (r' := (41014762235867349 / 40000000000000000 : ℚ))
        (U := (-(1670236444950892870231 / 2500000000000000000000 : ℚ)))
        (U' := (62631505799107129769 / 2500000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (2562396616048653 / 5000000000000000 : ℚ))
      (q := (41014762235867349 / 80000000000000000 : ℚ))
      (U := (-(1670236444950892870231 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_5 :
    Uω (aρ 5) (bρ 5) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(3460351350126436706987 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40043099614031753 / 80000000000000000 : ℝ) ≤
      (-(3460351350126436706987 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (40043099614031753 / 80000000000000000 : ℚ))
        (r' := (40043099614031753 / 40000000000000000 : ℚ))
        (U := (-(3460351350126436706987 / 5000000000000000000000 : ℚ)))
        (U' := (5384551373563293013 / 5000000000000000000000 : ℚ))
        1 2 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (5000067495973407 / 10000000000000000 : ℚ))
      (q := (40043099614031753 / 80000000000000000 : ℚ))
      (U := (-(3460351350126436706987 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_6 :
    Uω (aρ 6) (bρ 6) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(7275802777793215124253 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (38646119013703849 / 80000000000000000 : ℝ) ≤
      (-(7275802777793215124253 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (38646119013703849 / 80000000000000000 : ℚ))
        (r' := (38646119013703849 / 20000000000000000 : ℚ))
        (U := (-(7275802777793215124253 / 10000000000000000000000 : ℚ)))
        (U' := (6587140828206784875747 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (4818062721031431 / 10000000000000000 : ℚ))
      (q := (38646119013703849 / 80000000000000000 : ℚ))
      (U := (-(7275802777793215124253 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_7 :
    Uω (aρ 7) (bρ 7) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(194591119444156857651 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36732508617790769 / 80000000000000000 : ℝ) ≤
      (-(194591119444156857651 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (36732508617790769 / 80000000000000000 : ℚ))
        (r' := (36732508617790769 / 20000000000000000 : ℚ))
        (U := (-(194591119444156857651 / 250000000000000000000 : ℚ)))
        (U' := (151982470705843142349 / 250000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (4563321502813161 / 10000000000000000 : ℚ))
      (q := (36732508617790769 / 80000000000000000 : ℚ))
      (U := (-(194591119444156857651 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_8 :
    Uω (aρ 8) (bρ 8) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(8492649056459973840639 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1368733560120661 / 3200000000000000 : ℝ) ≤
      (-(8492649056459973840639 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1368733560120661 / 3200000000000000 : ℚ))
        (r' := (1368733560120661 / 800000000000000 : ℚ))
        (U := (-(8492649056459973840639 / 10000000000000000000000 : ℚ)))
        (U' := (5370294549540026159361 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (10545801876149 / 25000000000000 : ℚ))
      (q := (1368733560120661 / 3200000000000000 : ℚ))
      (U := (-(8492649056459973840639 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_9 :
    Uω (aρ 9) (bρ 9) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(9471271696007942156663 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6205658593083737 / 16000000000000000 : ℝ) ≤
      (-(9471271696007942156663 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6205658593083737 / 16000000000000000 : ℚ))
        (r' := (6205658593083737 / 4000000000000000 : ℚ))
        (U := (-(9471271696007942156663 / 10000000000000000000000 : ℚ)))
        (U' := (4391671909992057843337 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (188088743471007 / 500000000000000 : ℚ))
      (q := (6205658593083737 / 16000000000000000 : ℚ))
      (U := (-(9471271696007942156663 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_10 :
    Uω (aρ 10) (bρ 10) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(5416986698976334785817 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27075500931979433 / 80000000000000000 : ℝ) ≤
      (-(5416986698976334785817 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27075500931979433 / 80000000000000000 : ℚ))
        (r' := (27075500931979433 / 20000000000000000 : ℚ))
        (U := (-(5416986698976334785817 / 5000000000000000000000 : ℚ)))
        (U' := (1514485104023665214183 / 5000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (3162135894555327 / 10000000000000000 : ℚ))
      (q := (27075500931979433 / 80000000000000000 : ℚ))
      (U := (-(5416986698976334785817 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_11 :
    Uω (aρ 11) (bρ 11) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(12838570585395820165127 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22157356774028233 / 80000000000000000 : ℝ) ≤
      (-(12838570585395820165127 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (22157356774028233 / 80000000000000000 : ℚ))
        (r' := (22157356774028233 / 20000000000000000 : ℚ))
        (U := (-(12838570585395820165127 / 10000000000000000000000 : ℚ)))
        (U' := (1024373020604179834873 / 10000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (2351076481272527 / 10000000000000000 : ℚ))
      (q := (22157356774028233 / 80000000000000000 : ℚ))
      (U := (-(12838570585395820165127 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_12 :
    Uω (aρ 12) (bρ 12) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(4175188987432682907409 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15058626839837021 / 80000000000000000 : ℝ) ≤
      (-(4175188987432682907409 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (15058626839837021 / 80000000000000000 : ℚ))
        (r' := (15058626839837021 / 10000000000000000 : ℚ))
        (U := (-(4175188987432682907409 / 2500000000000000000000 : ℚ)))
        (U' := (1023414864817317092591 / 2500000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (34194264607229 / 64000000000000 : ℚ))
      (s := (250023523602431 / 2500000000000000 : ℚ))
      (q := (15058626839837021 / 80000000000000000 : ℚ))
      (U := (-(4175188987432682907409 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_478_13 :
    Uω (aρ 13) (bρ 13) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_478_14 :
    Uω (aρ 14) (bρ 14) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_478_15 :
    Uω (aρ 15) (bρ 15) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_478_16 :
    Uω (aρ 16) (bρ 16) (34194264607229 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_478 :
    Uρ (34194264607229 / 64000000000000 : ℝ) ≤
      (-(123519148321299201723 / 125000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_478_1 U_478_2 U_478_3 U_478_4 U_478_5 U_478_6 U_478_7 U_478_8 U_478_9 U_478_10
    U_478_11 U_478_12 U_478_13 U_478_14 U_478_15 U_478_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_479_1 :
    Uω (aρ 1) (bρ 1) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(637794369480791432831 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (84553075151977277 / 160000000000000000 : ℝ) ≤
      (-(637794369480791432831 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (84553075151977277 / 160000000000000000 : ℚ))
        (r' := (84553075151977277 / 80000000000000000 : ℚ))
        (U := (-(637794369480791432831 / 1000000000000000000000 : ℚ)))
        (U' := (55352810819208567169 / 1000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (1321134151135911 / 2500000000000000 : ℚ))
      (q := (84553075151977277 / 160000000000000000 : ℚ))
      (U := (-(637794369480791432831 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_2 :
    Uω (aρ 2) (bρ 2) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(321167425913844597629 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (84170033661501037 / 160000000000000000 : ℝ) ≤
      (-(321167425913844597629 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (84170033661501037 / 160000000000000000 : ℚ))
        (r' := (84170033661501037 / 80000000000000000 : ℚ))
        (U := (-(321167425913844597629 / 500000000000000000000 : ℚ)))
        (U' := (25406164236155402371 / 500000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (2630212715372057 / 5000000000000000 : ℚ))
      (q := (84170033661501037 / 160000000000000000 : ℚ))
      (U := (-(321167425913844597629 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_3 :
    Uω (aρ 3) (bρ 3) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(1302965429178912640407 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16680713769480353 / 32000000000000000 : ℝ) ≤
      (-(1302965429178912640407 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16680713769480353 / 32000000000000000 : ℚ))
        (r' := (16680713769480353 / 16000000000000000 : ℚ))
        (U := (-(1302965429178912640407 / 2000000000000000000000 : ℚ)))
        (U' := (83328931421087359593 / 2000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (1042402687066341 / 2000000000000000 : ℚ))
      (q := (16680713769480353 / 32000000000000000 : ℚ))
      (U := (-(1302965429178912640407 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_4 :
    Uω (aρ 4) (bρ 4) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(3334387412826117338583 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (82129423010569821 / 160000000000000000 : ℝ) ≤
      (-(3334387412826117338583 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (82129423010569821 / 160000000000000000 : ℚ))
        (r' := (82129423010569821 / 80000000000000000 : ℚ))
        (U := (-(3334387412826117338583 / 5000000000000000000000 : ℚ)))
        (U' := (131348488673882661417 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (641379923349089 / 1250000000000000 : ℚ))
      (q := (82129423010569821 / 160000000000000000 : ℚ))
      (U := (-(3334387412826117338583 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_5 :
    Uω (aρ 5) (bρ 5) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(276329133748210301077 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (80186163945248261 / 160000000000000000 : ℝ) ≤
      (-(276329133748210301077 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (80186163945248261 / 160000000000000000 : ℚ))
        (r' := (80186163945248261 / 80000000000000000 : ℚ))
        (U := (-(276329133748210301077 / 400000000000000000000 : ℚ)))
        (U' := (929738371789698923 / 400000000000000000000 : ℚ))
        1 2 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (5006321922962517 / 10000000000000000 : ℚ))
      (q := (80186163945248261 / 160000000000000000 : ℚ))
      (U := (-(276329133748210301077 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_6 :
    Uω (aρ 6) (bρ 6) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(7262857527910127196811 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (77392359551862197 / 160000000000000000 : ℝ) ≤
      (-(7262857527910127196811 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (77392359551862197 / 160000000000000000 : ℚ))
        (r' := (77392359551862197 / 40000000000000000 : ℚ))
        (U := (-(7262857527910127196811 / 10000000000000000000000 : ℚ)))
        (U' := (6600086078089872803189 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (4824336748929259 / 10000000000000000 : ℚ))
      (q := (77392359551862197 / 160000000000000000 : ℚ))
      (U := (-(7262857527910127196811 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_7 :
    Uω (aρ 7) (bρ 7) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(7769977439395536664309 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (73565493006656277 / 160000000000000000 : ℝ) ≤
      (-(7769977439395536664309 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (73565493006656277 / 160000000000000000 : ℚ))
        (r' := (73565493006656277 / 40000000000000000 : ℚ))
        (U := (-(7769977439395536664309 / 10000000000000000000000 : ℚ)))
        (U' := (6092966166604463335691 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (4569639811538519 / 10000000000000000 : ℚ))
      (q := (73565493006656277 / 160000000000000000 : ℚ))
      (U := (-(7769977439395536664309 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_8 :
    Uω (aρ 8) (bρ 8) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(8477864923492468921267 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (68537930528878301 / 160000000000000000 : ℝ) ≤
      (-(8477864923492468921267 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (68537930528878301 / 160000000000000000 : ℚ))
        (r' := (68537930528878301 / 40000000000000000 : ℚ))
        (U := (-(8477864923492468921267 / 10000000000000000000000 : ℚ)))
        (U' := (5385078682507531078733 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (264046009572267 / 625000000000000 : ℚ))
      (q := (68537930528878301 / 160000000000000000 : ℚ))
      (U := (-(8477864923492468921267 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_9 :
    Uω (aρ 9) (bρ 9) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(9454695290100289161531 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (62159538752414389 / 160000000000000000 : ℝ) ≤
      (-(9454695290100289161531 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (62159538752414389 / 160000000000000000 : ℚ))
        (r' := (62159538752414389 / 40000000000000000 : ℚ))
        (U := (-(9454695290100289161531 / 10000000000000000000000 : ℚ)))
        (U' := (4408248315899710838469 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (3768402809458283 / 10000000000000000 : ℚ))
      (q := (62159538752414389 / 160000000000000000 : ℚ))
      (U := (-(9454695290100289161531 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_10 :
    Uω (aρ 10) (bρ 10) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(10814258403181725422127 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54257865842343221 / 160000000000000000 : ℝ) ≤
      (-(10814258403181725422127 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54257865842343221 / 160000000000000000 : ℚ))
        (r' := (54257865842343221 / 40000000000000000 : ℚ))
        (U := (-(10814258403181725422127 / 10000000000000000000000 : ℚ)))
        (U' := (3048685202818274577873 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (3169252729194387 / 10000000000000000 : ℚ))
      (q := (54257865842343221 / 160000000000000000 : ℚ))
      (U := (-(10814258403181725422127 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_11 :
    Uω (aρ 11) (bρ 11) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(12812072247175655142927 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (44432295892864621 / 160000000000000000 : ℝ) ≤
      (-(12812072247175655142927 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (44432295892864621 / 160000000000000000 : ℚ))
        (r' := (44432295892864621 / 40000000000000000 : ℚ))
        (U := (-(12812072247175655142927 / 10000000000000000000000 : ℚ)))
        (U' := (1050871358824344857073 / 10000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (1179766555857281 / 5000000000000000 : ℚ))
      (q := (44432295892864621 / 160000000000000000 : ℚ))
      (U := (-(12812072247175655142927 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_12 :
    Uω (aρ 12) (bρ 12) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(16638879770636086593247 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30304185472766581 / 160000000000000000 : ℝ) ≤
      (-(16638879770636086593247 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30304185472766581 / 160000000000000000 : ℚ))
        (r' := (30304185472766581 / 20000000000000000 : ℚ))
        (U := (-(16638879770636086593247 / 10000000000000000000000 : ℚ)))
        (U' := (4155535638363913406753 / 10000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (68468416096493 / 128000000000000 : ℚ))
      (s := (1017219405887307 / 10000000000000000 : ℚ))
      (q := (30304185472766581 / 160000000000000000 : ℚ))
      (U := (-(16638879770636086593247 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_479_13 :
    Uω (aρ 13) (bρ 13) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_479_14 :
    Uω (aρ 14) (bρ 14) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_479_15 :
    Uω (aρ 15) (bρ 15) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_479_16 :
    Uω (aρ 16) (bρ 16) (68468416096493 / 128000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_479 :
    Uρ (68468416096493 / 128000000000000 : ℝ) ≤
      (-(2466473327665301070027 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_479_1 U_479_2 U_479_3 U_479_4 U_479_5 U_479_6 U_479_7 U_479_8 U_479_9 U_479_10
    U_479_11 U_479_12 U_479_13 U_479_14 U_479_15 U_479_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_480_1 :
    Uω (aρ 1) (bρ 1) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(10185824683330590031 / 16000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1322702098936339 / 2500000000000000 : ℝ) ≤
      (-(10185824683330590031 / 16000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1322702098936339 / 2500000000000000 : ℚ))
        (r' := (1322702098936339 / 1250000000000000 : ℚ))
        (U := (-(10185824683330590031 / 16000000000000000000 : ℚ)))
        (U' := (904530201469409969 / 16000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (1322694459844553 / 2500000000000000 : ℚ))
      (q := (1322702098936339 / 2500000000000000 : ℚ))
      (U := (-(10185824683330590031 / 16000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_2 :
    Uω (aρ 2) (bρ 2) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(1602872795690252040067 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10533737010983287 / 20000000000000000 : ℝ) ≤
      (-(1602872795690252040067 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10533737010983287 / 20000000000000000 : ℚ))
        (r' := (10533737010983287 / 10000000000000000 : ℚ))
        (U := (-(1602872795690252040067 / 2500000000000000000000 : ℚ)))
        (U' := (129995155059747959933 / 2500000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (5266667071380787 / 10000000000000000 : ℚ))
      (q := (10533737010983287 / 20000000000000000 : ℚ))
      (U := (-(1602872795690252040067 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_3 :
    Uω (aρ 3) (bρ 3) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(6502859740324113881097 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10437930128683687 / 20000000000000000 : ℝ) ≤
      (-(6502859740324113881097 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10437930128683687 / 20000000000000000 : ℚ))
        (r' := (10437930128683687 / 10000000000000000 : ℚ))
        (U := (-(6502859740324113881097 / 10000000000000000000000 : ℚ)))
        (U' := (428612062675886118903 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (5218256295431187 / 10000000000000000 : ℚ))
      (q := (10437930128683687 / 20000000000000000 : ℚ))
      (U := (-(6502859740324113881097 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_4 :
    Uω (aρ 4) (bρ 4) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(6656618678513322478103 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5139332590770681 / 10000000000000000 : ℝ) ≤
      (-(6656618678513322478103 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5139332590770681 / 10000000000000000 : ℚ))
        (r' := (5139332590770681 / 5000000000000000 : ℚ))
        (U := (-(6656618678513322478103 / 10000000000000000000000 : ℚ)))
        (U' := (274853124486677521897 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (2568642764676931 / 5000000000000000 : ℚ))
      (q := (5139332590770681 / 10000000000000000 : ℚ))
      (U := (-(6656618678513322478103 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_5 :
    Uω (aρ 5) (bρ 5) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(21549279880243073947 / 31250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2508941512434543 / 5000000000000000 : ℝ) ≤
      (-(21549279880243073947 / 31250000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2508941512434543 / 5000000000000000 : ℚ))
        (r' := (2508941512434543 / 2500000000000000 : ℚ))
        (U := (-(21549279880243073947 / 31250000000000000000 : ℚ)))
        (U' := (111569504131926053 / 31250000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (626572039610709 / 1250000000000000 : ℚ))
      (q := (2508941512434543 / 5000000000000000 : ℚ))
      (U := (-(21549279880243073947 / 31250000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_6 :
    Uω (aρ 6) (bρ 6) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(7249929102216071350707 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4843280024696013 / 10000000000000000 : ℝ) ≤
      (-(7249929102216071350707 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4843280024696013 / 10000000000000000 : ℚ))
        (r' := (4843280024696013 / 2500000000000000 : ℚ))
        (U := (-(7249929102216071350707 / 10000000000000000000000 : ℚ)))
        (U' := (6613014503783928649293 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (2415305345839763 / 5000000000000000 : ℚ))
      (q := (4843280024696013 / 10000000000000000 : ℚ))
      (U := (-(7249929102216071350707 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_7 :
    Uω (aρ 7) (bρ 7) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(7756328985092475948893 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2302061471369069 / 5000000000000000 : ℝ) ≤
      (-(7756328985092475948893 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2302061471369069 / 5000000000000000 : ℚ))
        (r' := (2302061471369069 / 1250000000000000 : ℚ))
        (U := (-(7756328985092475948893 / 10000000000000000000000 : ℚ)))
        (U' := (6106614620907524051107 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (17874835580171 / 39062500000000 : ℚ))
      (q := (2302061471369069 / 5000000000000000 : ℚ))
      (U := (-(7756328985092475948893 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_8 :
    Uω (aρ 8) (bρ 8) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(8463103222789283762703 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8579897360264411 / 20000000000000000 : ℝ) ≤
      (-(8463103222789283762703 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8579897360264411 / 20000000000000000 : ℚ))
        (r' := (8579897360264411 / 5000000000000000 : ℚ))
        (U := (-(8463103222789283762703 / 10000000000000000000000 : ℚ)))
        (U' := (5399840383210716237297 / 10000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (4231151034651911 / 10000000000000000 : ℚ))
      (q := (8579897360264411 / 20000000000000000 : ℚ))
      (U := (-(8463103222789283762703 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_9 :
    Uω (aρ 9) (bρ 9) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(4719074005300819373633 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1945702532055567 / 5000000000000000 : ℝ) ≤
      (-(4719074005300819373633 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1945702532055567 / 5000000000000000 : ℚ))
        (r' := (1945702532055567 / 1250000000000000 : ℚ))
        (U := (-(4719074005300819373633 / 5000000000000000000000 : ℚ)))
        (U' := (2212397797699180626367 / 5000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (471878678871221 / 1250000000000000 : ℚ))
      (q := (1945702532055567 / 5000000000000000 : ℚ))
      (U := (-(4719074005300819373633 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_10 :
    Uω (aρ 10) (bρ 10) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(10794587619119258863077 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3397793772506151 / 10000000000000000 : ℝ) ≤
      (-(10794587619119258863077 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3397793772506151 / 10000000000000000 : ℚ))
        (r' := (3397793772506151 / 2500000000000000 : ℚ))
        (U := (-(10794587619119258863077 / 10000000000000000000000 : ℚ)))
        (U' := (3068355986880741136923 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (1588182940627401 / 5000000000000000 : ℚ))
      (q := (3397793772506151 / 10000000000000000 : ℚ))
      (U := (-(10794587619119258863077 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_11 :
    Uω (aρ 11) (bρ 11) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(12785668633140302686513 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5568721028559307 / 20000000000000000 : ℝ) ≤
      (-(12785668633140302686513 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5568721028559307 / 20000000000000000 : ℚ))
        (r' := (5568721028559307 / 5000000000000000 : ℚ))
        (U := (-(12785668633140302686513 / 10000000000000000000000 : ℚ)))
        (U' := (1077274972859697313487 / 10000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (2367975991006807 / 10000000000000000 : ℚ))
      (q := (5568721028559307 / 20000000000000000 : ℚ))
      (U := (-(12785668633140302686513 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_12 :
    Uω (aρ 12) (bρ 12) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(8289014659856279049473 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (476392968685189 / 2500000000000000 : ℝ) ≤
      (-(8289014659856279049473 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (476392968685189 / 2500000000000000 : ℚ))
        (r' := (476392968685189 / 312500000000000 : ℚ))
        (U := (-(8289014659856279049473 / 5000000000000000000000 : ℚ)))
        (U' := (2108193044643720950527 / 5000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (2142134468079 / 4000000000000 : ℚ))
      (s := (258524702153503 / 2500000000000000 : ℚ))
      (q := (476392968685189 / 2500000000000000 : ℚ))
      (U := (-(8289014659856279049473 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_480_13 :
    Uω (aρ 13) (bρ 13) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_480_14 :
    Uω (aρ 14) (bρ 14) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_480_15 :
    Uω (aρ 15) (bρ 15) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_480_16 :
    Uω (aρ 16) (bρ 16) (2142134468079 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_480 :
    Uρ (2142134468079 / 4000000000000 : ℝ) ≤
      (-(2462587192580934883643 / 2500000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_480_1 U_480_2 U_480_3 U_480_4 U_480_5 U_480_6 U_480_7 U_480_8 U_480_9 U_480_10
    U_480_11 U_480_12 U_480_13 U_480_14 U_480_15 U_480_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_481_1 :
    Uω (aρ 1) (bρ 1) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(635435107480579353849 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (84752793510513459 / 160000000000000000 : ℝ) ≤
      (-(635435107480579353849 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (84752793510513459 / 160000000000000000 : ℚ))
        (r' := (84752793510513459 / 80000000000000000 : ℚ))
        (U := (-(635435107480579353849 / 1000000000000000000000 : ℚ)))
        (U' := (57712072819420646151 / 1000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (2648509537021349 / 5000000000000000 : ℚ))
      (q := (84752793510513459 / 160000000000000000 : ℚ))
      (U := (-(635435107480579353849 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_2 :
    Uω (aρ 2) (bρ 2) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(799955986413626136757 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (84369758505179243 / 160000000000000000 : ℝ) ≤
      (-(799955986413626136757 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (84369758505179243 / 160000000000000000 : ℚ))
        (r' := (84369758505179243 / 80000000000000000 : ℚ))
        (U := (-(799955986413626136757 / 1250000000000000000000 : ℚ)))
        (U' := (66477988961373863243 / 1250000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (5272908710885921 / 10000000000000000 : ℚ))
      (q := (84369758505179243 / 160000000000000000 : ℚ))
      (U := (-(799955986413626136757 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_3 :
    Uω (aρ 3) (bρ 3) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(6490906643397133693603 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (83603313179088739 / 160000000000000000 : ℝ) ≤
      (-(6490906643397133693603 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (83603313179088739 / 160000000000000000 : ℚ))
        (r' := (83603313179088739 / 80000000000000000 : ℚ))
        (U := (-(6490906643397133693603 / 10000000000000000000000 : ℚ)))
        (U' := (440565159602866306397 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (326531196967163 / 625000000000000 : ℚ))
      (q := (83603313179088739 / 160000000000000000 : ℚ))
      (U := (-(6490906643397133693603 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_4 :
    Uω (aρ 4) (bρ 4) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(6644477302373994372467 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16465843959474311 / 32000000000000000 : ℝ) ≤
      (-(6644477302373994372467 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16465843959474311 / 32000000000000000 : ℚ))
        (r' := (16465843959474311 / 16000000000000000 : ℚ))
        (U := (-(6644477302373994372467 / 10000000000000000000000 : ℚ)))
        (U' := (286994500626005627533 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (16073536436953 / 31250000000000 : ℚ))
      (q := (16465843959474311 / 32000000000000000 : ℚ))
      (U := (-(6644477302373994372467 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_5 :
    Uω (aρ 5) (bρ 5) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(6883326315246774074947 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (80386092587023787 / 160000000000000000 : ℝ) ≤
      (-(6883326315246774074947 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (80386092587023787 / 160000000000000000 : ℚ))
        (r' := (80386092587023787 / 80000000000000000 : ℚ))
        (U := (-(6883326315246774074947 / 10000000000000000000000 : ℚ)))
        (U' := (48145487753225925053 / 10000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (5018830677866489 / 10000000000000000 : ℚ))
      (q := (80386092587023787 / 160000000000000000 : ℚ))
      (U := (-(6883326315246774074947 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_6 :
    Uω (aρ 6) (bρ 6) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(7237017456809963206417 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (77592600559880403 / 160000000000000000 : ℝ) ≤
      (-(7237017456809963206417 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (77592600559880403 / 160000000000000000 : ℚ))
        (r' := (77592600559880403 / 40000000000000000 : ℚ))
        (U := (-(7237017456809963206417 / 10000000000000000000000 : ℚ)))
        (U' := (6625926149190036793583 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (2418442274806783 / 5000000000000000 : ℚ))
      (q := (77592600559880403 / 160000000000000000 : ℚ))
      (U := (-(7237017456809963206417 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_7 :
    Uω (aρ 7) (bρ 7) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(7742699362116177004641 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (73766439474050131 / 160000000000000000 : ℝ) ≤
      (-(7742699362116177004641 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (73766439474050131 / 160000000000000000 : ℚ))
        (r' := (73766439474050131 / 40000000000000000 : ℚ))
        (U := (-(7742699362116177004641 / 10000000000000000000000 : ℚ)))
        (U' := (6120244243883822995359 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (2291137897322391 / 5000000000000000 : ℚ))
      (q := (73766439474050131 / 160000000000000000 : ℚ))
      (U := (-(7742699362116177004641 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_8 :
    Uω (aρ 8) (bρ 8) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(33793455538278231109 / 40000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (68740423084680027 / 160000000000000000 : ℝ) ≤
      (-(33793455538278231109 / 40000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (68740423084680027 / 160000000000000000 : ℚ))
        (r' := (68740423084680027 / 40000000000000000 : ℚ))
        (U := (-(33793455538278231109 / 40000000000000000000 : ℚ)))
        (U' := (21658318885721768891 / 40000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (4237565397313519 / 10000000000000000 : ℚ))
      (q := (68740423084680027 / 160000000000000000 : ℚ))
      (U := (-(33793455538278231109 / 40000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_9 :
    Uω (aρ 9) (bρ 9) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(9421629749586235676443 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12473082561275951 / 32000000000000000 : ℝ) ≤
      (-(9421629749586235676443 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12473082561275951 / 32000000000000000 : ℚ))
        (r' := (12473082561275951 / 8000000000000000 : ℚ))
        (U := (-(9421629749586235676443 / 10000000000000000000000 : ℚ)))
        (U' := (4441313856413764323557 / 10000000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (756330948177197 / 2000000000000000 : ℚ))
      (q := (12473082561275951 / 32000000000000000 : ℚ))
      (U := (-(9421629749586235676443 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_10 :
    Uω (aρ 10) (bρ 10) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(10774960825271525424907 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10894301122940959 / 32000000000000000 : ℝ) ≤
      (-(10774960825271525424907 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10894301122940959 / 32000000000000000 : ℚ))
        (r' := (10894301122940959 / 8000000000000000 : ℚ))
        (U := (-(10774960825271525424907 / 10000000000000000000000 : ℚ)))
        (U' := (3087982780728474575093 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (636695075084323 / 2000000000000000 : ℚ))
      (q := (10894301122940959 / 32000000000000000 : ℚ))
      (U := (-(10774960825271525424907 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_11 :
    Uω (aρ 11) (bρ 11) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(6379679458388677789959 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (44667131727406203 / 160000000000000000 : ℝ) ≤
      (-(6379679458388677789959 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (44667131727406203 / 160000000000000000 : ℚ))
        (r' := (44667131727406203 / 40000000000000000 : ℚ))
        (U := (-(6379679458388677789959 / 5000000000000000000000 : ℚ)))
        (U' := (551792344611322210041 / 5000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (2376405265714291 / 10000000000000000 : ℚ))
      (q := (44667131727406203 / 160000000000000000 : ℚ))
      (U := (-(6379679458388677789959 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_12 :
    Uω (aρ 12) (bρ 12) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(3303631472747489113263 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30672242057537979 / 160000000000000000 : ℝ) ≤
      (-(3303631472747489113263 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (30672242057537979 / 160000000000000000 : ℚ))
        (r' := (30672242057537979 / 20000000000000000 : ℚ))
        (U := (-(3303631472747489113263 / 2000000000000000000000 : ℚ)))
        (U' := (855251609052510886737 / 2000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (68628189860563 / 128000000000000 : ℚ))
      (s := (1050744153665763 / 10000000000000000 : ℚ))
      (q := (30672242057537979 / 160000000000000000 : ℚ))
      (U := (-(3303631472747489113263 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_481_13 :
    Uω (aρ 13) (bρ 13) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_481_14 :
    Uω (aρ 14) (bρ 14) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_481_15 :
    Uω (aρ 15) (bρ 15) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_481_16 :
    Uω (aρ 16) (bρ 16) (68628189860563 / 128000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_481 :
    Uρ (68628189860563 / 128000000000000 : ℝ) ≤
      (-(4917447403195761472373 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_481_1 U_481_2 U_481_3 U_481_4 U_481_5 U_481_6 U_481_7 U_481_8 U_481_9 U_481_10
    U_481_11 U_481_12 U_481_13 U_481_14 U_481_15 U_481_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_482_1 :
    Uω (aρ 1) (bρ 1) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(3171287802603740539783 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (42426326343872691 / 80000000000000000 : ℝ) ≤
      (-(3171287802603740539783 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (42426326343872691 / 80000000000000000 : ℚ))
        (r' := (42426326343872691 / 40000000000000000 : ℚ))
        (U := (-(3171287802603740539783 / 5000000000000000000000 : ℚ)))
        (U' := (294448098896259460217 / 5000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (662907538567213 / 1250000000000000 : ℚ))
      (q := (42426326343872691 / 80000000000000000 : ℚ))
      (U := (-(3171287802603740539783 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_2 :
    Uω (aρ 2) (bρ 2) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(159695465267239470827 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (42234810456735991 / 80000000000000000 : ℝ) ≤
      (-(159695465267239470827 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (42234810456735991 / 80000000000000000 : ℚ))
        (r' := (42234810456735991 / 40000000000000000 : ℚ))
        (U := (-(159695465267239470827 / 250000000000000000000 : ℚ)))
        (U' := (13591329807760529173 / 250000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (5279150349263529 / 10000000000000000 : ℚ))
      (q := (42234810456735991 / 80000000000000000 : ℚ))
      (U := (-(159695465267239470827 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_3 :
    Uω (aρ 3) (bρ 3) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(1619741955232353905561 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41851592648187839 / 80000000000000000 : ℝ) ≤
      (-(1619741955232353905561 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41851592648187839 / 80000000000000000 : ℚ))
        (r' := (41851592648187839 / 40000000000000000 : ℚ))
        (U := (-(1619741955232353905561 / 2500000000000000000000 : ℚ)))
        (U' := (113125995517646094439 / 2500000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (5230742003476491 / 10000000000000000 : ℚ))
      (q := (41851592648187839 / 80000000000000000 : ℚ))
      (U := (-(1619741955232353905561 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_4 :
    Uω (aρ 4) (bρ 4) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(6632350661352732514341 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13188658887367 / 25600000000000 : ℝ) ≤
      (-(6632350661352732514341 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13188658887367 / 25600000000000 : ℚ))
        (r' := (13188658887367 / 12800000000000 : ℚ))
        (U := (-(6632350661352732514341 / 10000000000000000000000 : ℚ)))
        (U' := (299121141647267485659 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (20599111113 / 40000000000 : ℚ))
      (q := (13188658887367 / 25600000000000 : ℚ))
      (U := (-(6632350661352732514341 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_5 :
    Uω (aρ 5) (bρ 5) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(3435449282817292923889 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40243028256793767 / 80000000000000000 : ℝ) ≤
      (-(3435449282817292923889 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (40243028256793767 / 80000000000000000 : ℚ))
        (r' := (40243028256793767 / 40000000000000000 : ℚ))
        (U := (-(3435449282817292923889 / 5000000000000000000000 : ℚ)))
        (U' := (30286618682707076111 / 5000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (5025085006027973 / 10000000000000000 : ℚ))
      (q := (40243028256793767 / 80000000000000000 : ℚ))
      (U := (-(3435449282817292923889 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_6 :
    Uω (aρ 6) (bρ 6) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(3612061273981600181139 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7769272004873171 / 16000000000000000 : ℝ) ≤
      (-(3612061273981600181139 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7769272004873171 / 16000000000000000 : ℚ))
        (r' := (7769272004873171 / 4000000000000000 : ℚ))
        (U := (-(3612061273981600181139 / 5000000000000000000000 : ℚ)))
        (U' := (3319410529018399818861 / 5000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (968631664612199 / 2000000000000000 : ℚ))
      (q := (7769272004873171 / 16000000000000000 : ℚ))
      (U := (-(3612061273981600181139 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_7 :
    Uω (aρ 7) (bρ 7) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(7729088517948928495677 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36933455092172003 / 80000000000000000 : ℝ) ≤
      (-(7729088517948928495677 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (36933455092172003 / 80000000000000000 : ℚ))
        (r' := (36933455092172003 / 20000000000000000 : ℚ))
        (U := (-(7729088517948928495677 / 10000000000000000000000 : ℚ)))
        (U' := (6133855088051071504323 / 10000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (1147148367693133 / 2500000000000000 : ℚ))
      (q := (36933455092172003 / 80000000000000000 : ℚ))
      (U := (-(7729088517948928495677 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_8 :
    Uω (aρ 8) (bρ 8) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(4216823419692748033009 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1376833263107851 / 3200000000000000 : ℝ) ≤
      (-(4216823419692748033009 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1376833263107851 / 3200000000000000 : ℚ))
        (r' := (1376833263107851 / 800000000000000 : ℚ))
        (U := (-(4216823419692748033009 / 5000000000000000000000 : ℚ)))
        (U' := (2714648383307251966991 / 5000000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (5304974054367 / 12500000000000 : ℚ))
      (q := (1376833263107851 / 3200000000000000 : ℚ))
      (U := (-(4216823419692748033009 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_9 :
    Uω (aρ 9) (bρ 9) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(2351285099938865213181 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (31234167074635759 / 80000000000000000 : ℝ) ≤
      (-(2351285099938865213181 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (31234167074635759 / 80000000000000000 : ℚ))
        (r' := (31234167074635759 / 20000000000000000 : ℚ))
        (U := (-(2351285099938865213181 / 2500000000000000000000 : ℚ)))
        (U' := (1114450801561134786819 / 2500000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (3788278746088471 / 10000000000000000 : ℚ))
      (q := (31234167074635759 / 80000000000000000 : ℚ))
      (U := (-(2351285099938865213181 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_10 :
    Uω (aρ 10) (bρ 10) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(84026389085341504191 / 78125000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27289140900890719 / 80000000000000000 : ℝ) ≤
      (-(84026389085341504191 / 78125000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27289140900890719 / 80000000000000000 : ℚ))
        (r' := (27289140900890719 / 20000000000000000 : ℚ))
        (U := (-(84026389085341504191 / 78125000000000000000 : ℚ)))
        (U' := (24277857836533495809 / 78125000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (3190581236147211 / 10000000000000000 : ℚ))
      (q := (27289140900890719 / 80000000000000000 : ℚ))
      (U := (-(84026389085341504191 / 78125000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_11 :
    Uω (aρ 11) (bρ 11) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(2546628456716178291753 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4478438754372667 / 16000000000000000 : ℝ) ≤
      (-(2546628456716178291753 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4478438754372667 / 16000000000000000 : ℚ))
        (r' := (4478438754372667 / 4000000000000000 : ℚ))
        (U := (-(2546628456716178291753 / 2000000000000000000000 : ℚ)))
        (U' := (225960264483821708247 / 2000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (476964216019073 / 2000000000000000 : ℚ))
      (q := (4478438754372667 / 16000000000000000 : ℚ))
      (U := (-(2546628456716178291753 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_12 :
    Uω (aρ 12) (bρ 12) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(16459220212367328245369 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15426774638283691 / 80000000000000000 : ℝ) ≤
      (-(16459220212367328245369 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (15426774638283691 / 80000000000000000 : ℚ))
        (r' := (15426774638283691 / 10000000000000000 : ℚ))
        (U := (-(16459220212367328245369 / 10000000000000000000000 : ℚ)))
        (U' := (4335195196632671754631 / 10000000000000000000000 : ℚ))
        3 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (34354038371299 / 64000000000000 : ℚ))
      (s := (533583196692727 / 5000000000000000 : ℚ))
      (q := (15426774638283691 / 80000000000000000 : ℚ))
      (U := (-(16459220212367328245369 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_482_13 :
    Uω (aρ 13) (bρ 13) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_482_14 :
    Uω (aρ 14) (bρ 14) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_482_15 :
    Uω (aρ 15) (bρ 15) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_482_16 :
    Uω (aρ 16) (bρ 16) (34354038371299 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_482 :
    Uρ (34354038371299 / 64000000000000 : ℝ) ≤
      (-(9819528231062824967897 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_482_1 U_482_2 U_482_3 U_482_4 U_482_5 U_482_6 U_482_7 U_482_8 U_482_9 U_482_10
    U_482_11 U_482_12 U_482_13 U_482_14 U_482_15 U_482_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_483_1 :
    Uω (aρ 1) (bρ 1) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(6330813985629369780369 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (84952511863626233 / 160000000000000000 : ℝ) ≤
      (-(6330813985629369780369 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (84952511863626233 / 160000000000000000 : ℚ))
        (r' := (84952511863626233 / 80000000000000000 : ℚ))
        (U := (-(6330813985629369780369 / 10000000000000000000000 : ℚ)))
        (U' := (600657817370630219631 / 10000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (2654750771431913 / 5000000000000000 : ℚ))
      (q := (84952511863626233 / 160000000000000000 : ℚ))
      (U := (-(6330813985629369780369 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_2 :
    Uω (aρ 2) (bρ 2) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(3188001653894608997351 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (84569483312776481 / 160000000000000000 : ℝ) ≤
      (-(3188001653894608997351 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (84569483312776481 / 160000000000000000 : ℚ))
        (r' := (84569483312776481 / 80000000000000000 : ℚ))
        (U := (-(3188001653894608997351 / 5000000000000000000000 : ℚ)))
        (U' := (277734247605391002649 / 5000000000000000000000 : ℚ))
        1 5 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (5285391986517607 / 10000000000000000 : ℚ))
      (q := (84569483312776481 / 160000000000000000 : ℚ))
      (U := (-(3188001653894608997351 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_3 :
    Uω (aρ 3) (bρ 3) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(3233521619429571196959 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (83803057381445937 / 160000000000000000 : ℝ) ≤
      (-(3233521619429571196959 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (83803057381445937 / 160000000000000000 : ℚ))
        (r' := (83803057381445937 / 80000000000000000 : ℚ))
        (U := (-(3233521619429571196959 / 5000000000000000000000 : ℚ)))
        (U' := (232214282070428803041 / 5000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (5236984851451289 / 10000000000000000 : ℚ))
      (q := (83803057381445937 / 160000000000000000 : ℚ))
      (U := (-(3233521619429571196959 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_4 :
    Uω (aρ 4) (bρ 4) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(6620238719698710557651 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16505803239739541 / 32000000000000000 : ℝ) ≤
      (-(6620238719698710557651 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (16505803239739541 / 32000000000000000 : ℚ))
        (r' := (16505803239739541 / 16000000000000000 : ℚ))
        (U := (-(6620238719698710557651 / 10000000000000000000000 : ℚ)))
        (U' := (311233083301289442349 / 10000000000000000000000 : ℚ))
        1 4 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (128900597116819 / 250000000000000 : ℚ))
      (q := (16505803239739541 / 32000000000000000 : ℚ))
      (U := (-(6620238719698710557651 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_5 :
    Uω (aρ 5) (bρ 5) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(3429243137104443273827 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (80586020178575737 / 160000000000000000 : ℝ) ≤
      (-(3429243137104443273827 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (80586020178575737 / 160000000000000000 : ℚ))
        (r' := (80586020178575737 / 80000000000000000 : ℚ))
        (U := (-(3429243137104443273827 / 5000000000000000000000 : ℚ)))
        (U' := (36492764395556726173 / 5000000000000000000000 : ℚ))
        1 3 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (2515669650746257 / 5000000000000000 : ℚ))
      (q := (80586020178575737 / 160000000000000000 : ℚ))
      (U := (-(3429243137104443273827 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_6 :
    Uω (aρ 6) (bρ 6) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(7211244332118761894243 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (77792838864313353 / 160000000000000000 : ℝ) ≤
      (-(7211244332118761894243 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (77792838864313353 / 160000000000000000 : ℚ))
        (r' := (77792838864313353 / 40000000000000000 : ℚ))
        (U := (-(7211244332118761894243 / 10000000000000000000000 : ℚ)))
        (U' := (6651699273881238105757 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (1212358003087429 / 2500000000000000 : ℚ))
      (q := (77792838864313353 / 160000000000000000 : ℚ))
      (U := (-(7211244332118761894243 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_7 :
    Uω (aρ 7) (bρ 7) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(3857748200147473405413 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (73967379221621257 / 160000000000000000 : ℝ) ≤
      (-(3857748200147473405413 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (73967379221621257 / 160000000000000000 : ℚ))
        (r' := (73967379221621257 / 40000000000000000 : ℚ))
        (U := (-(3857748200147473405413 / 5000000000000000000000 : ℚ)))
        (U' := (3073723602852526594587 / 5000000000000000000000 : ℚ))
        2 13 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 7) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (1148727734443301 / 2500000000000000 : ℚ))
      (q := (73967379221621257 / 160000000000000000 : ℚ))
      (U := (-(3857748200147473405413 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_8 :
    Uω (aρ 8) (bρ 8) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(210473800453005356507 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (68942899112957753 / 160000000000000000 : ℝ) ≤
      (-(210473800453005356507 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (68942899112957753 / 160000000000000000 : ℚ))
        (r' := (68942899112957753 / 40000000000000000 : ℚ))
        (U := (-(210473800453005356507 / 250000000000000000000 : ℚ)))
        (U' := (136099789696994643493 / 250000000000000000000 : ℚ))
        2 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 8) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (2125196287765133 / 5000000000000000 : ℚ))
      (q := (68942899112957753 / 160000000000000000 : ℚ))
      (U := (-(210473800453005356507 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_9 :
    Uω (aρ 9) (bρ 9) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(2347169963608201734619 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (62571245109110529 / 160000000000000000 : ℝ) ≤
      (-(2347169963608201734619 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (62571245109110529 / 160000000000000000 : ℚ))
        (r' := (62571245109110529 / 40000000000000000 : ℚ))
        (U := (-(2347169963608201734619 / 2500000000000000000000 : ℚ)))
        (U' := (1118565937891798265381 / 2500000000000000000000 : ℚ))
        2 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 9) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (3794901453409363 / 10000000000000000 : ℚ))
      (q := (62571245109110529 / 160000000000000000 : ℚ))
      (U := (-(2347169963608201734619 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_10 :
    Uω (aρ 10) (bρ 10) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(10735838335119840614069 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54685029115109073 / 160000000000000000 : ℝ) ≤
      (-(10735838335119840614069 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (54685029115109073 / 160000000000000000 : ℚ))
        (r' := (54685029115109073 / 40000000000000000 : ℚ))
        (U := (-(10735838335119840614069 / 10000000000000000000000 : ℚ)))
        (U' := (3127105270880159385931 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 10) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (3197683487654181 / 10000000000000000 : ℚ))
      (q := (54685029115109073 / 160000000000000000 : ℚ))
      (U := (-(10735838335119840614069 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_11 :
    Uω (aρ 11) (bρ 11) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(12707017930806615344121 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (44901536813439489 / 160000000000000000 : ℝ) ≤
      (-(12707017930806615344121 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (44901536813439489 / 160000000000000000 : ℚ))
        (r' := (44901536813439489 / 40000000000000000 : ℚ))
        (U := (-(12707017930806615344121 / 10000000000000000000000 : ℚ)))
        (U' := (1155925675193384655879 / 10000000000000000000000 : ℚ))
        2 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 11) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (2393223576150483 / 10000000000000000 : ℚ))
      (q := (44901536813439489 / 160000000000000000 : ℚ))
      (U := (-(12707017930806615344121 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_12 :
    Uω (aρ 12) (bρ 12) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(3280235471263865683437 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6206630563877357 / 32000000000000000 : ℝ) ≤
      (-(3280235471263865683437 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6206630563877357 / 32000000000000000 : ℚ))
        (r' := (6206630563877357 / 4000000000000000 : ℚ))
        (U := (-(3280235471263865683437 / 2000000000000000000000 : ℚ)))
        (U' := (878647610536134316563 / 2000000000000000000000 : ℚ))
        3 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 12) (t := (68787963624633 / 128000000000000 : ℚ))
      (s := (216675134715779 / 2000000000000000 : ℚ))
      (q := (6206630563877357 / 32000000000000000 : ℚ))
      (U := (-(3280235471263865683437 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_483_13 :
    Uω (aρ 13) (bρ 13) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_483_14 :
    Uω (aρ 14) (bρ 14) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_483_15 :
    Uω (aρ 15) (bρ 15) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_483_16 :
    Uω (aρ 16) (bρ 16) (68787963624633 / 128000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_483 :
    Uρ (68787963624633 / 128000000000000 : ℝ) ≤
      (-(980424608155701660297 / 1000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_483_1 U_483_2 U_483_3 U_483_4 U_483_5 U_483_6 U_483_7 U_483_8 U_483_9 U_483_10
    U_483_11 U_483_12 U_483_13 U_483_14 U_483_15 U_483_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
