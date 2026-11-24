/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.ArctangentCertificate
import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries
import LeanPool.Zeta5Irrational.Table.LowerCertificate

public import LeanPool.Zeta5Irrational.Energy
import LeanPool.Zeta5Irrational.Certificates
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # V53: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped ArctangentCertificates LogarithmCertificates

lemma V_637 :
    ((1381932097217859613867 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(370162538946138480059 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2147768782037017 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (443598587162207701421 / 1250000000000000000000 : ℝ))) -
              6 * (217697824813350455459 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (4723620598879 / 6400000000000 : ℝ) := by
  have hL1 :
    (1381932097217859613867 / 2500000000000000000000 : ℝ) ≤
      Real.log (11123620598879 / 6400000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (11123620598879 / 6400000000000 : ℚ))
        (L := (1381932097217859613867 / 2500000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (4759620598879 / 6400000000000 : ℝ) ≤
      (-(370162538946138480059 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4759620598879 / 6400000000000 : ℚ))
        (r' := (4759620598879 / 3200000000000 : ℚ))
        (U := (-(370162538946138480059 / 1250000000000000000000 : ℚ)))
        (U' := (496271436428861519941 / 1250000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1046 :
    Real.arctan (8591075128148071 / 23183572044688206 : ℝ) ≤
      (443598587162207701421 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8591075128148071 / 23183572044688206 : ℚ))
        (U := (443598587162207701421 / 1250000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1045 :
    Real.arctan (8591075128148071 / 10000000000000000 : ℝ) ≤
      (2 * (443598587162207701421 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6591786022344103 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8591075128148071 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8591075128148071 / 10000000000000000 : ℝ) /
                (1 + (6591786022344103 / 5000000000000000 : ℝ)) =
              (8591075128148071 / 23183572044688206 : ℝ)
            by
        norm_num];
        exact hau1046)
  have hat1 :
    (Real.pi / 2 - (2 * (443598587162207701421 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8591075128148071 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8591075128148071 : ℝ) =
              (8591075128148071 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1045)
  have hat2 :
    Real.arctan (187500000000000 / 2147768782037017 : ℝ) ≤
      (217697824813350455459 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 2147768782037017 : ℚ))
        (U := (217697824813350455459 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4723620598879 / 6400000000000 : ℚ))
      (lo := (2147768782037017 / 2500000000000000 : ℚ))
      (hi := (8591075128148071 / 10000000000000000 : ℚ))
      (s := (2147768782037017 / 2500000000000000 : ℚ))
      (r₁ := (11123620598879 / 6400000000000 : ℚ))
      (r₂ := (4759620598879 / 6400000000000 : ℚ))
      (z₁ := (10000000000000000 / 8591075128148071 : ℚ))
      (z₂ := (187500000000000 / 2147768782037017 : ℚ))
      (L := (1381932097217859613867 / 2500000000000000000000 : ℚ))
      (U := (-(370162538946138480059 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_638 :
    ((691650816020377922461 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(147425107002328637843 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8596616287992327 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3550382320117678762279 / 10000000000000000000000 : ℝ))) -
              6 * (870232839768089163139 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2956072464119 / 4000000000000 : ℝ) := by
  have hL1 :
    (691650816020377922461 / 1250000000000000000000 : ℝ) ≤
      Real.log (6956072464119 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (6956072464119 / 4000000000000 : ℚ))
        (L := (691650816020377922461 / 1250000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (2978572464119 / 4000000000000 : ℝ) ≤
      (-(147425107002328637843 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2978572464119 / 4000000000000 : ℚ))
        (r' := (2978572464119 / 2000000000000 : ℚ))
        (U := (-(147425107002328637843 / 500000000000000000000 : ℚ)))
        (U' := (199148483147671362157 / 500000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1048 :
    Real.arctan (4298308143996165 / 11593591805741674 : ℝ) ≤
      (3550382320117678762279 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4298308143996165 / 11593591805741674 : ℚ))
        (U := (3550382320117678762279 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1047 :
    Real.arctan (859661628799233 / 1000000000000000 : ℝ) ≤
      (2 * (3550382320117678762279 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3296795902870837 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (859661628799233 / 1000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (859661628799233 / 1000000000000000 : ℝ) /
                (1 + (3296795902870837 / 2500000000000000 : ℝ)) =
              (4298308143996165 / 11593591805741674 : ℝ)
            by
        norm_num];
        exact hau1048)
  have hat1 :
    (Real.pi / 2 - (2 * (3550382320117678762279 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1000000000000000 / 859661628799233 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 859661628799233 : ℝ) =
              (859661628799233 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau1047)
  have hat2 :
    Real.arctan (250000000000000 / 2865538762664109 : ℝ) ≤
      (870232839768089163139 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2865538762664109 : ℚ))
        (U := (870232839768089163139 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2956072464119 / 4000000000000 : ℚ))
      (lo := (8596616287992327 / 10000000000000000 : ℚ))
      (hi := (859661628799233 / 1000000000000000 : ℚ))
      (s := (8596616287992327 / 10000000000000000 : ℚ))
      (r₁ := (6956072464119 / 4000000000000 : ℚ))
      (r₂ := (2978572464119 / 4000000000000 : ℚ))
      (z₁ := (1000000000000000 / 859661628799233 : ℚ))
      (z₂ := (250000000000000 / 2865538762664109 : ℚ))
      (L := (691650816020377922461 / 1250000000000000000000 : ℚ))
      (U := (-(147425107002328637843 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_639 :
    ((1384670417024153405141 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(36696504086374459829 / 125000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8602153878446119 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3551974044421646939057 / 10000000000000000000000 : ℝ))) -
              6 * (21741886334314884711 / 250000000000000000000 : ℝ)))) ≤
      Vfield (23679056431509 / 32000000000000 : ℝ) := by
  have hL1 :
    (1384670417024153405141 / 2500000000000000000000 : ℝ) ≤
      Real.log (55679056431509 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (55679056431509 / 32000000000000 : ℚ))
        (L := (1384670417024153405141 / 2500000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (23859056431509 / 32000000000000 : ℝ) ≤
      (-(36696504086374459829 / 125000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23859056431509 / 32000000000000 : ℚ))
        (r' := (23859056431509 / 16000000000000 : ℚ))
        (U := (-(36696504086374459829 / 125000000000000000000 : ℚ)))
        (U' := (49946893451125540171 / 125000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1050 :
    Real.arctan (4301076939223061 / 11595397094725715 : ℝ) ≤
      (3551974044421646939057 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4301076939223061 / 11595397094725715 : ℚ))
        (U := (3551974044421646939057 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1049 :
    Real.arctan (4301076939223061 / 5000000000000000 : ℝ) ≤
      (2 * (3551974044421646939057 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1319079418945143 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4301076939223061 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4301076939223061 / 5000000000000000 : ℝ) /
                (1 + (1319079418945143 / 1000000000000000 : ℝ)) =
              (4301076939223061 / 11595397094725715 : ℝ)
            by
        norm_num];
        exact hau1050)
  have hat1 :
    (Real.pi / 2 - (2 * (3551974044421646939057 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4301076939223061 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4301076939223061 : ℝ) =
              (4301076939223061 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1049)
  have hat2 :
    Real.arctan (750000000000000 / 8602153878446119 : ℝ) ≤
      (21741886334314884711 / 250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 8602153878446119 : ℚ))
        (U := (21741886334314884711 / 250000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (23679056431509 / 32000000000000 : ℚ))
      (lo := (8602153878446119 / 10000000000000000 : ℚ))
      (hi := (4301076939223061 / 5000000000000000 : ℚ))
      (s := (8602153878446119 / 10000000000000000 : ℚ))
      (r₁ := (55679056431509 / 32000000000000 : ℚ))
      (r₂ := (23859056431509 / 32000000000000 : ℚ))
      (z₁ := (5000000000000000 / 4301076939223061 : ℚ))
      (z₂ := (750000000000000 / 8602153878446119 : ℚ))
      (L := (1384670417024153405141 / 2500000000000000000000 : ℚ))
      (U := (-(36696504086374459829 / 125000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_640 :
    ((1108830762390958605563 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2922954830394664874721 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8607687906398339 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3553563874266416429189 / 10000000000000000000000 : ℝ))) -
              6 * (434559568317348828441 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (11854766575033 / 16000000000000 : ℝ) := by
  have hL1 :
    (1108830762390958605563 / 2000000000000000000000 : ℝ) ≤
      Real.log (27854766575033 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (27854766575033 / 16000000000000 : ℚ))
        (L := (1108830762390958605563 / 2000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (11944766575033 / 16000000000000 : ℝ) ≤
      (-(2922954830394664874721 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11944766575033 / 16000000000000 : ℚ))
        (r' := (11944766575033 / 8000000000000 : ℚ))
        (U := (-(2922954830394664874721 / 10000000000000000000000 : ℚ)))
        (U' := (4008516972605335125279 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1052 :
    Real.arctan (8607687906398342 / 23194403779404215 : ℝ) ≤
      (3553563874266416429189 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8607687906398342 / 23194403779404215 : ℚ))
        (U := (3553563874266416429189 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1051 :
    Real.arctan (4303843953199171 / 5000000000000000 : ℝ) ≤
      (2 * (3553563874266416429189 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2638880755880843 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4303843953199171 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4303843953199171 / 5000000000000000 : ℝ) /
                (1 + (2638880755880843 / 2000000000000000 : ℝ)) =
              (8607687906398342 / 23194403779404215 : ℝ)
            by
        norm_num];
        exact hau1052)
  have hat1 :
    (Real.pi / 2 - (2 * (3553563874266416429189 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4303843953199171 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4303843953199171 : ℝ) =
              (4303843953199171 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1051)
  have hat2 :
    Real.arctan (750000000000000 / 8607687906398339 : ℝ) ≤
      (434559568317348828441 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 8607687906398339 : ℚ))
        (U := (434559568317348828441 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (11854766575033 / 16000000000000 : ℚ))
      (lo := (8607687906398339 / 10000000000000000 : ℚ))
      (hi := (4303843953199171 / 5000000000000000 : ℚ))
      (s := (8607687906398339 / 10000000000000000 : ℚ))
      (r₁ := (27854766575033 / 16000000000000 : ℚ))
      (r₂ := (11944766575033 / 16000000000000 : ℚ))
      (z₁ := (5000000000000000 / 4303843953199171 : ℚ))
      (z₂ := (750000000000000 / 8607687906398339 : ℚ))
      (L := (1108830762390958605563 / 2000000000000000000000 : ℚ))
      (U := (-(2922954830394664874721 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_641 :
    ((2774811481507379783337 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2910205608895841854953 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4306609189357877 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1777575906847914134599 / 5000000000000000000000 : ℝ))) -
              6 * (868563886137522201071 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (23740009868623 / 32000000000000 : ℝ) := by
  have hL1 :
    (2774811481507379783337 / 5000000000000000000000 : ℝ) ≤
      Real.log (55740009868623 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (55740009868623 / 32000000000000 : ℚ))
        (L := (2774811481507379783337 / 5000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (23920009868623 / 32000000000000 : ℝ) ≤
      (-(2910205608895841854953 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23920009868623 / 32000000000000 : ℚ))
        (r' := (23920009868623 / 16000000000000 : ℚ))
        (U := (-(2910205608895841854953 / 10000000000000000000000 : ℚ)))
        (U' := (4021266194104158145047 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1054 :
    Real.arctan (8613218378715757 / 23198012382152354 : ℝ) ≤
      (1777575906847914134599 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8613218378715757 / 23198012382152354 : ℚ))
        (U := (1777575906847914134599 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1053 :
    Real.arctan (8613218378715757 / 10000000000000000 : ℝ) ≤
      (2 * (1777575906847914134599 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6599006191076177 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8613218378715757 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8613218378715757 / 10000000000000000 : ℝ) /
                (1 + (6599006191076177 / 5000000000000000 : ℝ)) =
              (8613218378715757 / 23198012382152354 : ℝ)
            by
        norm_num];
        exact hau1054)
  have hat1 :
    (Real.pi / 2 - (2 * (1777575906847914134599 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8613218378715757 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8613218378715757 : ℝ) =
              (8613218378715757 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1053)
  have hat2 :
    Real.arctan (375000000000000 / 4306609189357877 : ℝ) ≤
      (868563886137522201071 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 4306609189357877 : ℚ))
        (U := (868563886137522201071 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (23740009868623 / 32000000000000 : ℚ))
      (lo := (4306609189357877 / 5000000000000000 : ℚ))
      (hi := (8613218378715757 / 10000000000000000 : ℚ))
      (s := (4306609189357877 / 5000000000000000 : ℚ))
      (r₁ := (55740009868623 / 32000000000000 : ℚ))
      (r₂ := (23920009868623 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 8613218378715757 : ℚ))
      (z₂ := (375000000000000 / 4306609189357877 : ℚ))
      (L := (2774811481507379783337 / 5000000000000000000000 : ℚ))
      (U := (-(2910205608895841854953 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_642 :
    ((5555089124548337093933 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2897472620967558860071 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4309372651121549 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (355673786674076914369 / 1000000000000000000000 : ℝ))) -
              6 * (217002424619864156391 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (1188524329359 / 1600000000000 : ℝ) := by
  have hL1 :
    (5555089124548337093933 / 10000000000000000000000 : ℝ) ≤
      Real.log (2788524329359 / 1600000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2788524329359 / 1600000000000 : ℚ))
        (L := (5555089124548337093933 / 10000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (1197524329359 / 1600000000000 : ℝ) ≤
      (-(2897472620967558860071 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1197524329359 / 1600000000000 : ℚ))
        (r' := (1197524329359 / 800000000000 : ℚ))
        (U := (-(2897472620967558860071 / 10000000000000000000000 : ℚ)))
        (U' := (4033999182032441139929 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1056 :
    Real.arctan (8618745302243101 / 23201619998505391 : ℝ) ≤
      (355673786674076914369 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8618745302243101 / 23201619998505391 : ℚ))
        (U := (355673786674076914369 / 1000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1055 :
    Real.arctan (8618745302243101 / 10000000000000000 : ℝ) ≤
      (2 * (355673786674076914369 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13201619998505391 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8618745302243101 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8618745302243101 / 10000000000000000 : ℝ) /
                (1 + (13201619998505391 / 10000000000000000 : ℝ)) =
              (8618745302243101 / 23201619998505391 : ℝ)
            by
        norm_num];
        exact hau1056)
  have hat1 :
    (Real.pi / 2 - (2 * (355673786674076914369 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8618745302243101 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8618745302243101 : ℝ) =
              (8618745302243101 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1055)
  have hat2 :
    Real.arctan (375000000000000 / 4309372651121549 : ℝ) ≤
      (217002424619864156391 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 4309372651121549 : ℚ))
        (U := (217002424619864156391 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1188524329359 / 1600000000000 : ℚ))
      (lo := (4309372651121549 / 5000000000000000 : ℚ))
      (hi := (8618745302243101 / 10000000000000000 : ℚ))
      (s := (4309372651121549 / 5000000000000000 : ℚ))
      (r₁ := (2788524329359 / 1600000000000 : ℚ))
      (r₂ := (1197524329359 / 1600000000000 : ℚ))
      (z₁ := (10000000000000000 / 8618745302243101 : ℚ))
      (z₂ := (375000000000000 / 4309372651121549 : ℚ))
      (L := (5555089124548337093933 / 10000000000000000000000 : ℚ))
      (U := (-(2897472620967558860071 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_643 :
    ((222422091992879484073 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2884755825322004909539 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2156067170950793 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3558322037419228638997 / 10000000000000000000000 : ℝ))) -
              6 * (216864142568515565517 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (23800963305737 / 32000000000000 : ℝ) := by
  have hL1 :
    (222422091992879484073 / 400000000000000000000 : ℝ) ≤
      Real.log (55800963305737 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (55800963305737 / 32000000000000 : ℚ))
        (L := (222422091992879484073 / 400000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (23980963305737 / 32000000000000 : ℝ) ≤
      (-(2884755825322004909539 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23980963305737 / 32000000000000 : ℚ))
        (r' := (23980963305737 / 16000000000000 : ℚ))
        (U := (-(2884755825322004909539 / 10000000000000000000000 : ℚ)))
        (U' := (4046715977677995090461 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1058 :
    Real.arctan (8624268683803175 / 23205226629271764 : ℝ) ≤
      (3558322037419228638997 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8624268683803175 / 23205226629271764 : ℚ))
        (U := (3558322037419228638997 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1057 :
    Real.arctan (344970747352127 / 400000000000000 : ℝ) ≤
      (2 * (3558322037419228638997 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3301306657317941 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (344970747352127 / 400000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (344970747352127 / 400000000000000 : ℝ) /
                (1 + (3301306657317941 / 2500000000000000 : ℝ)) =
              (8624268683803175 / 23205226629271764 : ℝ)
            by
        norm_num];
        exact hau1058)
  have hat1 :
    (Real.pi / 2 - (2 * (3558322037419228638997 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (400000000000000 / 344970747352127 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (400000000000000 / 344970747352127 : ℝ) =
              (344970747352127 / 400000000000000 : ℝ)
            by
        norm_num];
        exact hau1057)
  have hat2 :
    Real.arctan (187500000000000 / 2156067170950793 : ℝ) ≤
      (216864142568515565517 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 2156067170950793 : ℚ))
        (U := (216864142568515565517 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (23800963305737 / 32000000000000 : ℚ))
      (lo := (2156067170950793 / 2500000000000000 : ℚ))
      (hi := (344970747352127 / 400000000000000 : ℚ))
      (s := (2156067170950793 / 2500000000000000 : ℚ))
      (r₁ := (55800963305737 / 32000000000000 : ℚ))
      (r₂ := (23980963305737 / 32000000000000 : ℚ))
      (z₁ := (400000000000000 / 344970747352127 : ℚ))
      (z₂ := (187500000000000 / 2156067170950793 : ℚ))
      (L := (222422091992879484073 / 400000000000000000000 : ℚ))
      (U := (-(2884755825322004909539 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_644 :
    ((69575156151210255373 / 125000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(718013795207170907293 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((539361783137309 / 625000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (889976082434089063109 / 2500000000000000000000 : ℝ))) -
              6 * (866904498149987081409 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (11915720012147 / 16000000000000 : ℝ) := by
  have hL1 :
    (69575156151210255373 / 125000000000000000000 : ℝ) ≤
      Real.log (27915720012147 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (27915720012147 / 16000000000000 : ℚ))
        (L := (69575156151210255373 / 125000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (12005720012147 / 16000000000000 : ℝ) ≤
      (-(718013795207170907293 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12005720012147 / 16000000000000 : ℚ))
        (r' := (12005720012147 / 8000000000000 : ℚ))
        (U := (-(718013795207170907293 / 2500000000000000000000 : ℚ)))
        (U' := (1014854155542829092707 / 2500000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1060 :
    Real.arctan (8629788530196947 / 23208832275258807 : ℝ) ≤
      (889976082434089063109 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8629788530196947 / 23208832275258807 : ℚ))
        (U := (889976082434089063109 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1059 :
    Real.arctan (8629788530196947 / 10000000000000000 : ℝ) ≤
      (2 * (889976082434089063109 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13208832275258807 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8629788530196947 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8629788530196947 / 10000000000000000 : ℝ) /
                (1 + (13208832275258807 / 10000000000000000 : ℝ)) =
              (8629788530196947 / 23208832275258807 : ℝ)
            by
        norm_num];
        exact hau1060)
  have hat1 :
    (Real.pi / 2 - (2 * (889976082434089063109 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8629788530196947 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8629788530196947 : ℝ) =
              (8629788530196947 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1059)
  have hat2 :
    Real.arctan (46875000000000 / 539361783137309 : ℝ) ≤
      (866904498149987081409 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (46875000000000 / 539361783137309 : ℚ))
        (U := (866904498149987081409 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (11915720012147 / 16000000000000 : ℚ))
      (lo := (539361783137309 / 625000000000000 : ℚ))
      (hi := (8629788530196947 / 10000000000000000 : ℚ))
      (s := (539361783137309 / 625000000000000 : ℚ))
      (r₁ := (27915720012147 / 16000000000000 : ℚ))
      (r₂ := (12005720012147 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 8629788530196947 : ℚ))
      (z₂ := (46875000000000 / 539361783137309 : ℚ))
      (L := (69575156151210255373 / 125000000000000000000 : ℚ))
      (U := (-(718013795207170907293 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_645 :
    ((5576923940667797187807 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2846702181558542557229 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8640817644580863 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3563063295243344731693 / 10000000000000000000000 : ℝ))) -
              6 * (865803508735303275437 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (746637295669 / 1000000000000 : ℝ) := by
  have hL1 :
    (5576923940667797187807 / 10000000000000000000000 : ℝ) ≤
      Real.log (1746637295669 / 1000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1746637295669 / 1000000000000 : ℚ))
        (L := (5576923940667797187807 / 10000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (752262295669 / 1000000000000 : ℝ) ≤
      (-(2846702181558542557229 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (752262295669 / 1000000000000 : ℚ))
        (r' := (752262295669 / 500000000000 : ℚ))
        (U := (-(2846702181558542557229 / 10000000000000000000000 : ℚ)))
        (U' := (4084769621441457442771 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1062 :
    Real.arctan (4320408822290433 / 11608020308059366 : ℝ) ≤
      (3563063295243344731693 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4320408822290433 / 11608020308059366 : ℚ))
        (U := (3563063295243344731693 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1061 :
    Real.arctan (4320408822290433 / 5000000000000000 : ℝ) ≤
      (2 * (3563063295243344731693 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3304010154029683 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (4320408822290433 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4320408822290433 / 5000000000000000 : ℝ) /
                (1 + (3304010154029683 / 2500000000000000 : ℝ)) =
              (4320408822290433 / 11608020308059366 : ℝ)
            by
        norm_num];
        exact hau1062)
  have hat1 :
    (Real.pi / 2 - (2 * (3563063295243344731693 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4320408822290433 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4320408822290433 : ℝ) =
              (4320408822290433 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1061)
  have hat2 :
    Real.arctan (250000000000000 / 2880272548193621 : ℝ) ≤
      (865803508735303275437 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2880272548193621 : ℚ))
        (U := (865803508735303275437 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (746637295669 / 1000000000000 : ℚ))
      (lo := (8640817644580863 / 10000000000000000 : ℚ))
      (hi := (4320408822290433 / 5000000000000000 : ℚ))
      (s := (8640817644580863 / 10000000000000000 : ℚ))
      (r₁ := (1746637295669 / 1000000000000 : ℚ))
      (r₂ := (752262295669 / 1000000000000 : ℚ))
      (z₁ := (5000000000000000 / 4320408822290433 : ℚ))
      (z₂ := (250000000000000 / 2880272548193621 : ℚ))
      (L := (5576923940667797187807 / 10000000000000000000000 : ℚ))
      (U := (-(2846702181558542557229 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_646 :
    ((1395982290881571788087 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(283044465619030769971 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8647897332212889 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (356508924778024978169 / 1000000000000000000000 : ℝ))) -
              6 * (865098242589412292353 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (765809953469387 / 1024000000000000 : ℝ) := by
  have hL1 :
    (1395982290881571788087 / 2500000000000000000000 : ℝ) ≤
      Real.log (1789809953469387 / 1024000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1789809953469387 / 1024000000000000 : ℚ))
        (L := (1395982290881571788087 / 2500000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (771569953469387 / 1024000000000000 : ℝ) ≤
      (-(283044465619030769971 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (771569953469387 / 1024000000000000 : ℚ))
        (r' := (771569953469387 / 512000000000000 : ℚ))
        (U := (-(283044465619030769971 / 1000000000000000000000 : ℚ)))
        (U' := (410102714680969230029 / 1000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1064 :
    Real.arctan (665222871708684 / 1786205422491955 : ℝ) ≤
      (356508924778024978169 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (665222871708684 / 1786205422491955 : ℚ))
        (U := (356508924778024978169 / 1000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1063 :
    Real.arctan (2161974333053223 / 2500000000000000 : ℝ) ≤
      (2 * (356508924778024978169 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2644134098479083 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2161974333053223 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2161974333053223 / 2500000000000000 : ℝ) /
                (1 + (2644134098479083 / 2000000000000000 : ℝ)) =
              (665222871708684 / 1786205422491955 : ℝ)
            by
        norm_num];
        exact hau1064)
  have hat1 :
    (Real.pi / 2 - (2 * (356508924778024978169 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2161974333053223 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2161974333053223 : ℝ) =
              (2161974333053223 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau1063)
  have hat2 :
    Real.arctan (250000000000000 / 2882632444070963 : ℝ) ≤
      (865098242589412292353 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2882632444070963 : ℚ))
        (U := (865098242589412292353 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (765809953469387 / 1024000000000000 : ℚ))
      (lo := (8647897332212889 / 10000000000000000 : ℚ))
      (hi := (2161974333053223 / 2500000000000000 : ℚ))
      (s := (8647897332212889 / 10000000000000000 : ℚ))
      (r₁ := (1789809953469387 / 1024000000000000 : ℚ))
      (r₂ := (771569953469387 / 1024000000000000 : ℚ))
      (z₁ := (2500000000000000 / 2161974333053223 : ℚ))
      (z₂ := (250000000000000 / 2882632444070963 : ℚ))
      (L := (1395982290881571788087 / 2500000000000000000000 : ℚ))
      (U := (-(283044465619030769971 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_647 :
    ((2795464741252561992059 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1407106759320460963231 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4327485614363427 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (356711212603540415007 / 1000000000000000000000 : ℝ))) -
              6 * (432197348567961835751 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (383531658086859 / 512000000000000 : ℝ) := by
  have hL1 :
    (2795464741252561992059 / 5000000000000000000000 : ℝ) ≤
      Real.log (895531658086859 / 512000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (895531658086859 / 512000000000000 : ℚ))
        (L := (2795464741252561992059 / 5000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (386411658086859 / 512000000000000 : ℝ) ≤
      (-(1407106759320460963231 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (386411658086859 / 512000000000000 : ℚ))
        (r' := (386411658086859 / 256000000000000 : ℚ))
        (U := (-(1407106759320460963231 / 5000000000000000000000 : ℚ)))
        (U' := (2058629142179539036769 / 5000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1066 :
    Real.arctan (8654971228726857 / 23225298747857821 : ℝ) ≤
      (356711212603540415007 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8654971228726857 / 23225298747857821 : ℚ))
        (U := (356711212603540415007 / 1000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1065 :
    Real.arctan (8654971228726857 / 10000000000000000 : ℝ) ≤
      (2 * (356711212603540415007 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13225298747857821 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8654971228726857 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8654971228726857 / 10000000000000000 : ℝ) /
                (1 + (13225298747857821 / 10000000000000000 : ℝ)) =
              (8654971228726857 / 23225298747857821 : ℝ)
            by
        norm_num];
        exact hau1066)
  have hat1 :
    (Real.pi / 2 - (2 * (356711212603540415007 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8654971228726857 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8654971228726857 : ℝ) =
              (8654971228726857 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1065)
  have hat2 :
    Real.arctan (125000000000000 / 1442495204787809 : ℝ) ≤
      (432197348567961835751 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (125000000000000 / 1442495204787809 : ℚ))
        (U := (432197348567961835751 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (383531658086859 / 512000000000000 : ℚ))
      (lo := (4327485614363427 / 5000000000000000 : ℚ))
      (hi := (8654971228726857 / 10000000000000000 : ℚ))
      (s := (4327485614363427 / 5000000000000000 : ℚ))
      (r₁ := (895531658086859 / 512000000000000 : ℚ))
      (r₂ := (386411658086859 / 512000000000000 : ℚ))
      (z₁ := (10000000000000000 / 8654971228726857 : ℚ))
      (z₂ := (125000000000000 / 1442495204787809 : ℚ))
      (L := (2795464741252561992059 / 5000000000000000000000 : ℚ))
      (U := (-(1407106759320460963231 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_648 :
    ((5597924904465249726207 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1399004341694148145729 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1082754918538849 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1784565969182207295463 / 5000000000000000000000 : ℝ))) -
              6 * (431846432694659931273 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (768316678878049 / 1024000000000000 : ℝ) := by
  have hL1 :
    (5597924904465249726207 / 10000000000000000000000 : ℝ) ≤
      Real.log (1792316678878049 / 1024000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1792316678878049 / 1024000000000000 : ℚ))
        (L := (5597924904465249726207 / 10000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (774076678878049 / 1024000000000000 : ℝ) ≤
      (-(1399004341694148145729 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (774076678878049 / 1024000000000000 : ℚ))
        (r' := (774076678878049 / 512000000000000 : ℚ))
        (U := (-(1399004341694148145729 / 5000000000000000000000 : ℚ)))
        (U' := (2066731559805851854271 / 5000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1068 :
    Real.arctan (1732407869662159 / 4645985076841398 : ℝ) ≤
      (1784565969182207295463 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1732407869662159 / 4645985076841398 : ℚ))
        (U := (1784565969182207295463 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1067 :
    Real.arctan (1732407869662159 / 2000000000000000 : ℝ) ≤
      (2 * (1784565969182207295463 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1322992538420699 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1732407869662159 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1732407869662159 / 2000000000000000 : ℝ) /
                (1 + (1322992538420699 / 1000000000000000 : ℝ)) =
              (1732407869662159 / 4645985076841398 : ℝ)
            by
        norm_num];
        exact hau1068)
  have hat1 :
    (Real.pi / 2 - (2 * (1784565969182207295463 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1732407869662159 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1732407869662159 : ℝ) =
              (1732407869662159 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau1067)
  have hat2 :
    Real.arctan (93750000000000 / 1082754918538849 : ℝ) ≤
      (431846432694659931273 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (93750000000000 / 1082754918538849 : ℚ))
        (U := (431846432694659931273 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (768316678878049 / 1024000000000000 : ℚ))
      (lo := (1082754918538849 / 1250000000000000 : ℚ))
      (hi := (1732407869662159 / 2000000000000000 : ℚ))
      (s := (1082754918538849 / 1250000000000000 : ℚ))
      (r₁ := (1792316678878049 / 1024000000000000 : ℚ))
      (r₂ := (774076678878049 / 1024000000000000 : ℚ))
      (z₁ := (2000000000000000 / 1732407869662159 : ℚ))
      (z₂ := (93750000000000 / 1082754918538849 : ℚ))
      (L := (5597924904465249726207 / 10000000000000000000000 : ℚ))
      (U := (-(1399004341694148145729 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
