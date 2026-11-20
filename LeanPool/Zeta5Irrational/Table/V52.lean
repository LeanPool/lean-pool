/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries
import LeanPool.Zeta5Irrational.Table.LowerCertificate

public import LeanPool.Zeta5Irrational.Energy
import LeanPool.Zeta5Irrational.Certificates
import LeanPool.Zeta5Irrational.PotentialV
import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # V52: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma V_625 :
    ((2730877782592370590811 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3116169747917816613287 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1704860051870497 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3529515644499602674989 / 10000000000000000000000 : ℝ))) -
              6 * (877577784756869561493 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (23252382371711 / 32000000000000 : ℝ) := by
  have hL1 :
    (2730877782592370590811 / 5000000000000000000000 : ℝ) ≤
      Real.log (55252382371711 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (55252382371711 / 32000000000000 : ℚ))
        (L := (2730877782592370590811 / 5000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (23432382371711 / 32000000000000 : ℝ) ≤
      (-(3116169747917816613287 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23432382371711 / 32000000000000 : ℚ))
        (r' := (23432382371711 / 16000000000000 : ℚ))
        (U := (-(3116169747917816613287 / 10000000000000000000000 : ℚ)))
        (U' := (3815302055082183386713 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1022 :
    Real.arctan (4262150129676244 / 11570077908815025 : ℝ) ≤
      (3529515644499602674989 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4262150129676244 / 11570077908815025 : ℚ))
        (U := (3529515644499602674989 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1021 :
    Real.arctan (1065537532419061 / 1250000000000000 : ℝ) ≤
      (2 * (3529515644499602674989 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (262803116352601 / 200000000000000 : ℝ) ≤
          Real.sqrt (1 + (1065537532419061 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1065537532419061 / 1250000000000000 : ℝ) /
                (1 + (262803116352601 / 200000000000000 : ℝ)) =
              (4262150129676244 / 11570077908815025 : ℝ)
            by
        norm_num];
        exact hau1022)
  have hat1 :
    (Real.pi / 2 - (2 * (3529515644499602674989 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 1065537532419061 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 1065537532419061 : ℝ) =
              (1065537532419061 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau1021)
  have hat2 :
    Real.arctan (150000000000000 / 1704860051870497 : ℝ) ≤
      (877577784756869561493 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 1704860051870497 : ℚ))
        (U := (877577784756869561493 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (23252382371711 / 32000000000000 : ℚ))
      (lo := (1704860051870497 / 2000000000000000 : ℚ))
      (hi := (1065537532419061 / 1250000000000000 : ℚ))
      (s := (1704860051870497 / 2000000000000000 : ℚ))
      (r₁ := (55252382371711 / 32000000000000 : ℚ))
      (r₂ := (23432382371711 / 32000000000000 : ℚ))
      (z₁ := (1250000000000000 / 1065537532419061 : ℚ))
      (z₂ := (150000000000000 / 1704860051870497 : ℚ))
      (L := (2730877782592370590811 / 5000000000000000000000 : ℚ))
      (U := (-(3116169747917816613287 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_626 :
    ((546726995479048066533 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(77579298971171939033 / 250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8529884797410073 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1765566185380807726961 / 5000000000000000000000 : ℝ))) -
              6 * (219251543692524048579 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (5820714772567 / 8000000000000 : ℝ) := by
  have hL1 :
    (546726995479048066533 / 1000000000000000000000 : ℝ) ≤
      Real.log (13820714772567 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (13820714772567 / 8000000000000 : ℚ))
        (L := (546726995479048066533 / 1000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (5865714772567 / 8000000000000 : ℝ) ≤
      (-(77579298971171939033 / 250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5865714772567 / 8000000000000 : ℚ))
        (r' := (5865714772567 / 4000000000000 : ℚ))
        (U := (-(77579298971171939033 / 250000000000000000000 : ℚ)))
        (U' := (95707496103828060967 / 250000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1024 :
    Real.arctan (8529884797410076 / 23143779314074301 : ℝ) ≤
      (1765566185380807726961 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8529884797410076 / 23143779314074301 : ℚ))
        (U := (1765566185380807726961 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1023 :
    Real.arctan (2132471199352519 / 2500000000000000 : ℝ) ≤
      (2 * (1765566185380807726961 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13143779314074301 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2132471199352519 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2132471199352519 / 2500000000000000 : ℝ) /
                (1 + (13143779314074301 / 10000000000000000 : ℝ)) =
              (8529884797410076 / 23143779314074301 : ℝ)
            by
        norm_num];
        exact hau1024)
  have hat1 :
    (Real.pi / 2 - (2 * (1765566185380807726961 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2132471199352519 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2132471199352519 : ℝ) =
              (2132471199352519 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau1023)
  have hat2 :
    Real.arctan (750000000000000 / 8529884797410073 : ℝ) ≤
      (219251543692524048579 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 8529884797410073 : ℚ))
        (U := (219251543692524048579 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (5820714772567 / 8000000000000 : ℚ))
      (lo := (8529884797410073 / 10000000000000000 : ℚ))
      (hi := (2132471199352519 / 2500000000000000 : ℚ))
      (s := (8529884797410073 / 10000000000000000 : ℚ))
      (r₁ := (13820714772567 / 8000000000000 : ℚ))
      (r₂ := (5865714772567 / 8000000000000 : ℚ))
      (z₁ := (2500000000000000 / 2132471199352519 : ℚ))
      (z₂ := (750000000000000 / 8529884797410073 : ℚ))
      (L := (546726995479048066533 / 1000000000000000000000 : ℚ))
      (U := (-(77579298971171939033 / 250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_627 :
    ((5472781305222789424267 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3090191042100093015749 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8535465681647259 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3532747148789359859367 / 10000000000000000000000 : ℝ))) -
              6 * (175287136058003471421 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (932533432353 / 1280000000000 : ℝ) := by
  have hL1 :
    (5472781305222789424267 / 10000000000000000000000 : ℝ) ≤
      Real.log (2212533432353 / 1280000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2212533432353 / 1280000000000 : ℚ))
        (L := (5472781305222789424267 / 10000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (939733432353 / 1280000000000 : ℝ) ≤
      (-(3090191042100093015749 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (939733432353 / 1280000000000 : ℚ))
        (r' := (939733432353 / 640000000000 : ℚ))
        (U := (-(3090191042100093015749 / 10000000000000000000000 : ℚ)))
        (U' := (3841280760899906984251 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1026 :
    Real.arctan (251043108283743 / 680805935643029 : ℝ) ≤
      (3532747148789359859367 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (251043108283743 / 680805935643029 : ℚ))
        (U := (3532747148789359859367 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1025 :
    Real.arctan (4267732840823631 / 5000000000000000 : ℝ) ≤
      (2 * (3532747148789359859367 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6573700905931493 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4267732840823631 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4267732840823631 / 5000000000000000 : ℝ) /
                (1 + (6573700905931493 / 5000000000000000 : ℝ)) =
              (251043108283743 / 680805935643029 : ℝ)
            by
        norm_num];
        exact hau1026)
  have hat1 :
    (Real.pi / 2 - (2 * (3532747148789359859367 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4267732840823631 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4267732840823631 : ℝ) =
              (4267732840823631 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1025)
  have hat2 :
    Real.arctan (250000000000000 / 2845155227215753 : ℝ) ≤
      (175287136058003471421 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2845155227215753 : ℚ))
        (U := (175287136058003471421 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (932533432353 / 1280000000000 : ℚ))
      (lo := (8535465681647259 / 10000000000000000 : ℚ))
      (hi := (4267732840823631 / 5000000000000000 : ℚ))
      (s := (8535465681647259 / 10000000000000000 : ℚ))
      (r₁ := (2212533432353 / 1280000000000 : ℚ))
      (r₂ := (939733432353 / 1280000000000 : ℚ))
      (z₁ := (5000000000000000 / 4267732840823631 : ℚ))
      (z₂ := (250000000000000 / 2845155227215753 : ℚ))
      (L := (5472781305222789424267 / 10000000000000000000000 : ℚ))
      (U := (-(3090191042100093015749 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_628 :
    ((5478289619829812308189 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(769306738482647776489 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2135260729806619 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (441794997850047114757 / 1250000000000000000000 : ℝ))) -
              6 * (218966574423277628579 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (11671906263691 / 16000000000000 : ℝ) := by
  have hL1 :
    (5478289619829812308189 / 10000000000000000000000 : ℝ) ≤
      Real.log (27671906263691 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (27671906263691 / 16000000000000 : ℚ))
        (L := (5478289619829812308189 / 10000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (11761906263691 / 16000000000000 : ℝ) ≤
      (-(769306738482647776489 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11761906263691 / 16000000000000 : ℚ))
        (r' := (11761906263691 / 8000000000000 : ℚ))
        (U := (-(769306738482647776489 / 2500000000000000000000 : ℚ)))
        (U' := (963561212267352223511 / 2500000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1028 :
    Real.arctan (8541042919226479 / 23151023311821356 : ℝ) ≤
      (441794997850047114757 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8541042919226479 / 23151023311821356 : ℚ))
        (U := (441794997850047114757 / 1250000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1027 :
    Real.arctan (8541042919226479 / 10000000000000000 : ℝ) ≤
      (2 * (441794997850047114757 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3287755827955339 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8541042919226479 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8541042919226479 / 10000000000000000 : ℝ) /
                (1 + (3287755827955339 / 2500000000000000 : ℝ)) =
              (8541042919226479 / 23151023311821356 : ℝ)
            by
        norm_num];
        exact hau1028)
  have hat1 :
    (Real.pi / 2 - (2 * (441794997850047114757 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8541042919226479 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8541042919226479 : ℝ) =
              (8541042919226479 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1027)
  have hat2 :
    Real.arctan (187500000000000 / 2135260729806619 : ℝ) ≤
      (218966574423277628579 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 2135260729806619 : ℚ))
        (U := (218966574423277628579 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (11671906263691 / 16000000000000 : ℚ))
      (lo := (2135260729806619 / 2500000000000000 : ℚ))
      (hi := (8541042919226479 / 10000000000000000 : ℚ))
      (s := (2135260729806619 / 2500000000000000 : ℚ))
      (r₁ := (27671906263691 / 16000000000000 : ℚ))
      (r₂ := (11761906263691 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 8541042919226479 : ℚ))
      (z₂ := (187500000000000 / 2135260729806619 : ℚ))
      (L := (5478289619829812308189 / 10000000000000000000000 : ℚ))
      (U := (-(769306738482647776489 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_629 :
    ((5483794901954164421831 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(38303495634517765457 / 125000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2136654129321697 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3535970876998488086731 / 10000000000000000000000 : ℝ))) -
              6 * (875298023372310254261 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (23374289245939 / 32000000000000 : ℝ) := by
  have hL1 :
    (5483794901954164421831 / 10000000000000000000000 : ℝ) ≤
      Real.log (55374289245939 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (55374289245939 / 32000000000000 : ℚ))
        (L := (5483794901954164421831 / 10000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (23554289245939 / 32000000000000 : ℝ) ≤
      (-(38303495634517765457 / 125000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23554289245939 / 32000000000000 : ℚ))
        (r' := (23554289245939 / 16000000000000 : ℚ))
        (U := (-(38303495634517765457 / 125000000000000000000 : ℚ)))
        (U' := (48339901902982234543 / 125000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1030 :
    Real.arctan (8546616517286791 / 23154643814773525 : ℝ) ≤
      (3535970876998488086731 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8546616517286791 / 23154643814773525 : ℚ))
        (U := (3535970876998488086731 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1029 :
    Real.arctan (8546616517286791 / 10000000000000000 : ℝ) ≤
      (2 * (3535970876998488086731 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (526185752590941 / 400000000000000 : ℝ) ≤
          Real.sqrt (1 + (8546616517286791 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8546616517286791 / 10000000000000000 : ℝ) /
                (1 + (526185752590941 / 400000000000000 : ℝ)) =
              (8546616517286791 / 23154643814773525 : ℝ)
            by
        norm_num];
        exact hau1030)
  have hat1 :
    (Real.pi / 2 - (2 * (3535970876998488086731 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8546616517286791 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8546616517286791 : ℝ) =
              (8546616517286791 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1029)
  have hat2 :
    Real.arctan (187500000000000 / 2136654129321697 : ℝ) ≤
      (875298023372310254261 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 2136654129321697 : ℚ))
        (U := (875298023372310254261 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (23374289245939 / 32000000000000 : ℚ))
      (lo := (2136654129321697 / 2500000000000000 : ℚ))
      (hi := (8546616517286791 / 10000000000000000 : ℚ))
      (s := (2136654129321697 / 2500000000000000 : ℚ))
      (r₁ := (55374289245939 / 32000000000000 : ℚ))
      (r₂ := (23554289245939 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 8546616517286791 : ℚ))
      (z₂ := (187500000000000 / 2136654129321697 : ℚ))
      (L := (5483794901954164421831 / 10000000000000000000000 : ℚ))
      (U := (-(38303495634517765457 / 125000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_630 :
    ((5489297154932943295337 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(122053963567387008637 / 400000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1710437296588799 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (884394958893463844413 / 2500000000000000000000 : ℝ))) -
              6 * (174946170747382495469 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (1462797872781 / 2000000000000 : ℝ) := by
  have hL1 :
    (5489297154932943295337 / 10000000000000000000000 : ℝ) ≤
      Real.log (3462797872781 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (3462797872781 / 2000000000000 : ℚ))
        (L := (5489297154932943295337 / 10000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (1474047872781 / 2000000000000 : ℝ) ≤
      (-(122053963567387008637 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1474047872781 / 2000000000000 : ℚ))
        (r' := (1474047872781 / 1000000000000 : ℚ))
        (U := (-(122053963567387008637 / 400000000000000000000 : ℚ)))
        (U' := (155204908552612991363 / 400000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1032 :
    Real.arctan (4276093241471999 / 11579131660771237 : ℝ) ≤
      (884394958893463844413 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4276093241471999 / 11579131660771237 : ℚ))
        (U := (884394958893463844413 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1031 :
    Real.arctan (4276093241471999 / 5000000000000000 : ℝ) ≤
      (2 * (884394958893463844413 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6579131660771237 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4276093241471999 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4276093241471999 / 5000000000000000 : ℝ) /
                (1 + (6579131660771237 / 5000000000000000 : ℝ)) =
              (4276093241471999 / 11579131660771237 : ℝ)
            by
        norm_num];
        exact hau1032)
  have hat1 :
    (Real.pi / 2 - (2 * (884394958893463844413 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4276093241471999 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4276093241471999 : ℝ) =
              (4276093241471999 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1031)
  have hat2 :
    Real.arctan (150000000000000 / 1710437296588799 : ℝ) ≤
      (174946170747382495469 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 1710437296588799 : ℚ))
        (U := (174946170747382495469 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1462797872781 / 2000000000000 : ℚ))
      (lo := (1710437296588799 / 2000000000000000 : ℚ))
      (hi := (4276093241471999 / 5000000000000000 : ℚ))
      (s := (1710437296588799 / 2000000000000000 : ℚ))
      (r₁ := (3462797872781 / 2000000000000 : ℚ))
      (r₂ := (1474047872781 / 2000000000000 : ℚ))
      (z₁ := (5000000000000000 / 4276093241471999 : ℚ))
      (z₂ := (150000000000000 / 1710437296588799 : ℚ))
      (L := (5489297154932943295337 / 10000000000000000000000 : ℚ))
      (U := (-(122053963567387008637 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_631 :
    ((1098959276419548204243 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3038435225960614059479 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4278876411645369 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (884796715675760448579 / 2500000000000000000000 : ℝ))) -
              6 * (437082392606239601383 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (23435242683053 / 32000000000000 : ℝ) := by
  have hL1 :
    (1098959276419548204243 / 2000000000000000000000 : ℝ) ≤
      Real.log (55435242683053 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (55435242683053 / 32000000000000 : ℚ))
        (L := (1098959276419548204243 / 2000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (23615242683053 / 32000000000000 : ℝ) ≤
      (-(3038435225960614059479 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23615242683053 / 32000000000000 : ℚ))
        (r' := (23615242683053 / 16000000000000 : ℚ))
        (U := (-(3038435225960614059479 / 10000000000000000000000 : ℚ)))
        (U' := (3893036577039385940521 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1034 :
    Real.arctan (8557752823290741 / 23161881832950052 : ℝ) ≤
      (884796715675760448579 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8557752823290741 / 23161881832950052 : ℚ))
        (U := (884796715675760448579 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1033 :
    Real.arctan (8557752823290741 / 10000000000000000 : ℝ) ≤
      (2 * (884796715675760448579 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3290470458237513 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8557752823290741 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8557752823290741 / 10000000000000000 : ℝ) /
                (1 + (3290470458237513 / 2500000000000000 : ℝ)) =
              (8557752823290741 / 23161881832950052 : ℝ)
            by
        norm_num];
        exact hau1034)
  have hat1 :
    (Real.pi / 2 - (2 * (884796715675760448579 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8557752823290741 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8557752823290741 : ℝ) =
              (8557752823290741 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1033)
  have hat2 :
    Real.arctan (125000000000000 / 1426292137215123 : ℝ) ≤
      (437082392606239601383 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (125000000000000 / 1426292137215123 : ℚ))
        (U := (437082392606239601383 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (23435242683053 / 32000000000000 : ℚ))
      (lo := (4278876411645369 / 5000000000000000 : ℚ))
      (hi := (8557752823290741 / 10000000000000000 : ℚ))
      (s := (4278876411645369 / 5000000000000000 : ℚ))
      (r₁ := (55435242683053 / 32000000000000 : ℚ))
      (r₂ := (23615242683053 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 8557752823290741 : ℚ))
      (z₂ := (125000000000000 / 1426292137215123 : ℚ))
      (L := (1098959276419548204243 / 2000000000000000000000 : ℚ))
      (U := (-(3038435225960614059479 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_632 :
    ((5500292586774656357943 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(184664185669970729 / 610351562500000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8563315545396609 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (708158392509814711217 / 2000000000000000000000 : ℝ))) -
              6 * (436799907120371740757 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (2346571940161 / 3200000000000 : ℝ) := by
  have hL1 :
    (5500292586774656357943 / 10000000000000000000000 : ℝ) ≤
      Real.log (5546571940161 / 3200000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (5546571940161 / 3200000000000 : ℚ))
        (L := (5500292586774656357943 / 10000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (2364571940161 / 3200000000000 : ℝ) ≤
      (-(184664185669970729 / 610351562500000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2364571940161 / 3200000000000 : ℚ))
        (r' := (2364571940161 / 1600000000000 : ℚ))
        (U := (-(184664185669970729 / 610351562500000000 : ℚ)))
        (U' := (953597115474413959 / 2441406250000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1036 :
    Real.arctan (2854438515132204 / 7721833116605659 : ℝ) ≤
      (708158392509814711217 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2854438515132204 / 7721833116605659 : ℚ))
        (U := (708158392509814711217 / 2000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1035 :
    Real.arctan (2140828886349153 / 2500000000000000 : ℝ) ≤
      (2 * (708158392509814711217 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13165499349816977 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2140828886349153 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2140828886349153 / 2500000000000000 : ℝ) /
                (1 + (13165499349816977 / 10000000000000000 : ℝ)) =
              (2854438515132204 / 7721833116605659 : ℝ)
            by
        norm_num];
        exact hau1036)
  have hat1 :
    (Real.pi / 2 - (2 * (708158392509814711217 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2140828886349153 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2140828886349153 : ℝ) =
              (2140828886349153 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau1035)
  have hat2 :
    Real.arctan (250000000000000 / 2854438515132203 : ℝ) ≤
      (436799907120371740757 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2854438515132203 : ℚ))
        (U := (436799907120371740757 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2346571940161 / 3200000000000 : ℚ))
      (lo := (8563315545396609 / 10000000000000000 : ℚ))
      (hi := (2140828886349153 / 2500000000000000 : ℚ))
      (s := (8563315545396609 / 10000000000000000 : ℚ))
      (r₁ := (5546571940161 / 3200000000000 : ℚ))
      (r₂ := (2364571940161 / 3200000000000 : ℚ))
      (z₁ := (2500000000000000 / 2140828886349153 : ℚ))
      (z₂ := (250000000000000 / 2854438515132203 : ℚ))
      (L := (5500292586774656357943 / 10000000000000000000000 : ℚ))
      (U := (-(184664185669970729 / 610351562500000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_633 :
    ((5505785772284306800337 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3012657422447236628907 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8568874656308251 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3542395139261497851501 / 10000000000000000000000 : ℝ))) -
              6 * (109129492159939492009 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (23496196120167 / 32000000000000 : ℝ) := by
  have hL1 :
    (5505785772284306800337 / 10000000000000000000000 : ℝ) ≤
      Real.log (55496196120167 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (55496196120167 / 32000000000000 : ℚ))
        (L := (5505785772284306800337 / 10000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (23676196120167 / 32000000000000 : ℝ) ≤
      (-(3012657422447236628907 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23676196120167 / 32000000000000 : ℚ))
        (r' := (23676196120167 / 16000000000000 : ℚ))
        (U := (-(3012657422447236628907 / 10000000000000000000000 : ℚ)))
        (U' := (3918814380552763371093 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1038 :
    Real.arctan (8568874656308254 / 23169115872962841 : ℝ) ≤
      (3542395139261497851501 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8568874656308254 / 23169115872962841 : ℚ))
        (U := (3542395139261497851501 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1037 :
    Real.arctan (4284437328154127 / 5000000000000000 : ℝ) ≤
      (2 * (3542395139261497851501 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13169115872962841 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4284437328154127 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4284437328154127 / 5000000000000000 : ℝ) /
                (1 + (13169115872962841 / 10000000000000000 : ℝ)) =
              (8568874656308254 / 23169115872962841 : ℝ)
            by
        norm_num];
        exact hau1038)
  have hat1 :
    (Real.pi / 2 - (2 * (3542395139261497851501 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4284437328154127 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4284437328154127 : ℝ) =
              (4284437328154127 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1037)
  have hat2 :
    Real.arctan (750000000000000 / 8568874656308251 : ℝ) ≤
      (109129492159939492009 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 8568874656308251 : ℚ))
        (U := (109129492159939492009 / 1250000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (23496196120167 / 32000000000000 : ℚ))
      (lo := (8568874656308251 / 10000000000000000 : ℚ))
      (hi := (4284437328154127 / 5000000000000000 : ℚ))
      (s := (8568874656308251 / 10000000000000000 : ℚ))
      (r₁ := (55496196120167 / 32000000000000 : ℚ))
      (r₂ := (23676196120167 / 32000000000000 : ℚ))
      (z₁ := (5000000000000000 / 4284437328154127 : ℚ))
      (z₂ := (750000000000000 / 8568874656308251 : ℚ))
      (L := (5505785772284306800337 / 10000000000000000000000 : ℚ))
      (U := (-(3012657422447236628907 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_634 :
    ((5511275941941840616771 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2999793396511508222773 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1714886032609893 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (885999099244110855617 / 2500000000000000000000 : ℝ))) -
              6 * (872473150802591192013 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (5881668209681 / 8000000000000 : ℝ) := by
  have hL1 :
    (5511275941941840616771 / 10000000000000000000000 : ℝ) ≤
      Real.log (13881668209681 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (13881668209681 / 8000000000000 : ℚ))
        (L := (5511275941941840616771 / 10000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (5926668209681 / 8000000000000 : ℝ) ≤
      (-(2999793396511508222773 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5926668209681 / 8000000000000 : ℚ))
        (r' := (5926668209681 / 4000000000000 : ℚ))
        (U := (-(2999793396511508222773 / 10000000000000000000000 : ℚ)))
        (U' := (3931678406488491777227 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1040 :
    Real.arctan (8574430163049468 / 23172731403206113 : ℝ) ≤
      (885999099244110855617 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8574430163049468 / 23172731403206113 : ℚ))
        (U := (885999099244110855617 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1039 :
    Real.arctan (2143607540762367 / 2500000000000000 : ℝ) ≤
      (2 * (885999099244110855617 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13172731403206113 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2143607540762367 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2143607540762367 / 2500000000000000 : ℝ) /
                (1 + (13172731403206113 / 10000000000000000 : ℝ)) =
              (8574430163049468 / 23172731403206113 : ℝ)
            by
        norm_num];
        exact hau1040)
  have hat1 :
    (Real.pi / 2 - (2 * (885999099244110855617 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 2143607540762367 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 2143607540762367 : ℝ) =
              (2143607540762367 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau1039)
  have hat2 :
    Real.arctan (50000000000000 / 571628677536631 : ℝ) ≤
      (872473150802591192013 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (50000000000000 / 571628677536631 : ℚ))
        (U := (872473150802591192013 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (5881668209681 / 8000000000000 : ℚ))
      (lo := (1714886032609893 / 2000000000000000 : ℚ))
      (hi := (2143607540762367 / 2500000000000000 : ℚ))
      (s := (1714886032609893 / 2000000000000000 : ℚ))
      (r₁ := (13881668209681 / 8000000000000 : ℚ))
      (r₂ := (5926668209681 / 8000000000000 : ℚ))
      (z₁ := (2500000000000000 / 2143607540762367 : ℚ))
      (z₂ := (50000000000000 / 571628677536631 : ℚ))
      (L := (5511275941941840616771 / 10000000000000000000000 : ℚ))
      (U := (-(2999793396511508222773 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_635 :
    ((1379190774764237213347 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2986945897633933050071 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((33515554971177 / 39062500000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1772797869908340061831 / 5000000000000000000000 : ℝ))) -
              6 * (174382290259931083323 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (23557149557281 / 32000000000000 : ℝ) := by
  have hL1 :
    (1379190774764237213347 / 2500000000000000000000 : ℝ) ≤
      Real.log (55557149557281 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (55557149557281 / 32000000000000 : ℚ))
        (L := (1379190774764237213347 / 2500000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (23737149557281 / 32000000000000 : ℝ) ≤
      (-(2986945897633933050071 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23737149557281 / 32000000000000 : ℚ))
        (r' := (23737149557281 / 16000000000000 : ℚ))
        (U := (-(2986945897633933050071 / 10000000000000000000000 : ℚ)))
        (U' := (3944525905366066949929 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1042 :
    Real.arctan (1715996414524263 / 4635269188272827 : ℝ) ≤
      (1772797869908340061831 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1715996414524263 / 4635269188272827 : ℚ))
        (U := (1772797869908340061831 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1041 :
    Real.arctan (1715996414524263 / 2000000000000000 : ℝ) ≤
      (2 * (1772797869908340061831 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2635269188272827 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1715996414524263 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1715996414524263 / 2000000000000000 : ℝ) /
                (1 + (2635269188272827 / 2000000000000000 : ℝ)) =
              (1715996414524263 / 4635269188272827 : ℝ)
            by
        norm_num];
        exact hau1042)
  have hat1 :
    (Real.pi / 2 - (2 * (1772797869908340061831 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1715996414524263 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1715996414524263 : ℝ) =
              (1715996414524263 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau1041)
  have hat2 :
    Real.arctan (976562500000 / 11171851657059 : ℝ) ≤
      (174382290259931083323 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (976562500000 / 11171851657059 : ℚ))
        (U := (174382290259931083323 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (23557149557281 / 32000000000000 : ℚ))
      (lo := (33515554971177 / 39062500000000 : ℚ))
      (hi := (1715996414524263 / 2000000000000000 : ℚ))
      (s := (33515554971177 / 39062500000000 : ℚ))
      (r₁ := (55557149557281 / 32000000000000 : ℚ))
      (r₂ := (23737149557281 / 32000000000000 : ℚ))
      (z₁ := (2000000000000000 / 1715996414524263 : ℚ))
      (z₂ := (976562500000 / 11171851657059 : ℚ))
      (L := (1379190774764237213347 / 2500000000000000000000 : ℚ))
      (U := (-(2986945897633933050071 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_636 :
    ((5522247246933877305379 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2974114883402715778061 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1073191299000277 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3547193171891676928569 / 10000000000000000000000 : ℝ))) -
              6 * (435675417638097174757 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (11793813137919 / 16000000000000 : ℝ) := by
  have hL1 :
    (5522247246933877305379 / 10000000000000000000000 : ℝ) ≤
      Real.log (27793813137919 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (27793813137919 / 16000000000000 : ℚ))
        (L := (5522247246933877305379 / 10000000000000000000000 : ℚ))
        12 (by decide +kernel))
  have hU2 :
    Real.log (11883813137919 / 16000000000000 : ℝ) ≤
      (-(2974114883402715778061 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11883813137919 / 16000000000000 : ℚ))
        (r' := (11883813137919 / 8000000000000 : ℚ))
        (U := (-(2974114883402715778061 / 10000000000000000000000 : ℚ)))
        (U' := (3957356919597284221939 / 10000000000000000000000 : ℚ))
        1 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau1044 :
    Real.arctan (8585530392002219 / 23179959488253131 : ℝ) ≤
      (3547193171891676928569 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8585530392002219 / 23179959488253131 : ℚ))
        (U := (3547193171891676928569 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1043 :
    Real.arctan (8585530392002219 / 10000000000000000 : ℝ) ≤
      (2 * (3547193171891676928569 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13179959488253131 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8585530392002219 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8585530392002219 / 10000000000000000 : ℝ) /
                (1 + (13179959488253131 / 10000000000000000 : ℝ)) =
              (8585530392002219 / 23179959488253131 : ℝ)
            by
        norm_num];
        exact hau1044)
  have hat1 :
    (Real.pi / 2 - (2 * (3547193171891676928569 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8585530392002219 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8585530392002219 : ℝ) =
              (8585530392002219 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1043)
  have hat2 :
    Real.arctan (93750000000000 / 1073191299000277 : ℝ) ≤
      (435675417638097174757 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (93750000000000 / 1073191299000277 : ℚ))
        (U := (435675417638097174757 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (11793813137919 / 16000000000000 : ℚ))
      (lo := (1073191299000277 / 1250000000000000 : ℚ))
      (hi := (8585530392002219 / 10000000000000000 : ℚ))
      (s := (1073191299000277 / 1250000000000000 : ℚ))
      (r₁ := (27793813137919 / 16000000000000 : ℚ))
      (r₂ := (11883813137919 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 8585530392002219 : ℚ))
      (z₂ := (93750000000000 / 1073191299000277 : ℚ))
      (L := (5522247246933877305379 / 10000000000000000000000 : ℚ))
      (U := (-(2974114883402715778061 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
