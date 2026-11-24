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

/-! # V14: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped ArctangentCertificates LogarithmCertificates

lemma V_169 :
    ((1071890317176583928039 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21305693393452711451859 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3363698176688539 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1622404481577912283161 / 5000000000000000000000 : ℝ)) -
              6 * (548450874824163752413 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (7241257871269 / 64000000000000 : ℝ) := by
  have hL1 :
    (1071890317176583928039 / 10000000000000000000000 : ℝ) ≤
      Real.log (71241257871269 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (71241257871269 / 64000000000000 : ℚ))
        (L := (1071890317176583928039 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (7601257871269 / 64000000000000 : ℝ) ≤
      (-(21305693393452711451859 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7601257871269 / 64000000000000 : ℚ))
        (r' := (7601257871269 / 4000000000000 : ℚ))
        (U := (-(21305693393452711451859 / 10000000000000000000000 : ℚ)))
        (U' := (6420193818547288548141 / 10000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau231 :
    Real.arctan (1681849088344271 / 5000000000000000 : ℝ) ≤
      (1622404481577912283161 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1681849088344271 / 5000000000000000 : ℚ))
        (U := (1622404481577912283161 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1622404481577912283161 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1681849088344271 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1681849088344271 : ℝ) =
              (1681849088344271 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau231)
  have hat2 :
    Real.arctan (750000000000000 / 3363698176688539 : ℝ) ≤
      (548450874824163752413 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 3363698176688539 : ℚ))
        (U := (548450874824163752413 / 2500000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (7241257871269 / 64000000000000 : ℚ))
      (lo := (3363698176688539 / 10000000000000000 : ℚ))
      (hi := (1681849088344271 / 5000000000000000 : ℚ))
      (s := (3363698176688539 / 10000000000000000 : ℚ))
      (r₁ := (71241257871269 / 64000000000000 : ℚ))
      (r₂ := (7601257871269 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 1681849088344271 : ℚ))
      (z₂ := (750000000000000 / 3363698176688539 : ℚ))
      (L := (1071890317176583928039 / 10000000000000000000000 : ℚ))
      (U := (-(21305693393452711451859 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_170 :
    ((1075037203912298076033 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10638119306132417311027 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1684450974174337 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (812370766620299188099 / 2500000000000000000000 : ℝ)) -
              6 * (273815285801581864431 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (907960027007 / 8000000000000 : ℝ) := by
  have hL1 :
    (1075037203912298076033 / 10000000000000000000000 : ℝ) ≤
      Real.log (8907960027007 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (8907960027007 / 8000000000000 : ℚ))
        (L := (1075037203912298076033 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (952960027007 / 8000000000000 : ℝ) ≤
      (-(10638119306132417311027 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (952960027007 / 8000000000000 : ℚ))
        (r' := (952960027007 / 500000000000 : ℚ))
        (U := (-(10638119306132417311027 / 5000000000000000000000 : ℚ)))
        (U' := (3224824299867582688973 / 5000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau232 :
    Real.arctan (3368901948348677 / 10000000000000000 : ℝ) ≤
      (812370766620299188099 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3368901948348677 / 10000000000000000 : ℚ))
        (U := (812370766620299188099 / 2500000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (812370766620299188099 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3368901948348677 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3368901948348677 : ℝ) =
              (3368901948348677 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau232)
  have hat2 :
    Real.arctan (375000000000000 / 1684450974174337 : ℝ) ≤
      (273815285801581864431 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 1684450974174337 : ℚ))
        (U := (273815285801581864431 / 1250000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (907960027007 / 8000000000000 : ℚ))
      (lo := (1684450974174337 / 5000000000000000 : ℚ))
      (hi := (3368901948348677 / 10000000000000000 : ℚ))
      (s := (1684450974174337 / 5000000000000000 : ℚ))
      (r₁ := (8907960027007 / 8000000000000 : ℚ))
      (r₂ := (952960027007 / 8000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3368901948348677 : ℚ))
      (z₂ := (375000000000000 / 1684450974174337 : ℚ))
      (L := (1075037203912298076033 / 10000000000000000000000 : ℚ))
      (U := (-(10638119306132417311027 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_171 :
    ((539091550334963103107 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5311717583689524422171 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((105440552949823 / 312500000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (406768561615688575177 / 1250000000000000000000 : ℝ)) -
              6 * (1093627877775185649047 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (7286102560843 / 64000000000000 : ℝ) := by
  have hL1 :
    (539091550334963103107 / 5000000000000000000000 : ℝ) ≤
      Real.log (71286102560843 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (71286102560843 / 64000000000000 : ℚ))
        (L := (539091550334963103107 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (7646102560843 / 64000000000000 : ℝ) ≤
      (-(5311717583689524422171 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7646102560843 / 64000000000000 : ℚ))
        (r' := (7646102560843 / 4000000000000 : ℚ))
        (U := (-(5311717583689524422171 / 2500000000000000000000 : ℚ)))
        (U' := (1619754219310475577829 / 2500000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau233 :
    Real.arctan (3374097694394339 / 10000000000000000 : ℝ) ≤
      (406768561615688575177 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3374097694394339 / 10000000000000000 : ℚ))
        (U := (406768561615688575177 / 1250000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (406768561615688575177 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3374097694394339 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3374097694394339 : ℝ) =
              (3374097694394339 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau233)
  have hat2 :
    Real.arctan (23437500000000 / 105440552949823 : ℝ) ≤
      (1093627877775185649047 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (23437500000000 / 105440552949823 : ℚ))
        (U := (1093627877775185649047 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (7286102560843 / 64000000000000 : ℚ))
      (lo := (105440552949823 / 312500000000000 : ℚ))
      (hi := (3374097694394339 / 10000000000000000 : ℚ))
      (s := (105440552949823 / 312500000000000 : ℚ))
      (r₁ := (71286102560843 / 64000000000000 : ℚ))
      (r₂ := (7646102560843 / 64000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3374097694394339 : ℚ))
      (z₂ := (23437500000000 / 105440552949823 : ℚ))
      (L := (539091550334963103107 / 5000000000000000000000 : ℚ))
      (U := (-(5311717583689524422171 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_172 :
    ((1081328008072146210999 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(21217588054326763577179 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3379285451844349 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1629402640588147556519 / 5000000000000000000000 : ℝ)) -
              6 * (2184003797519659522247 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (730852490563 / 6400000000000 : ℝ) := by
  have hL1 :
    (1081328008072146210999 / 10000000000000000000000 : ℝ) ≤
      Real.log (7130852490563 / 6400000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (7130852490563 / 6400000000000 : ℚ))
        (L := (1081328008072146210999 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (766852490563 / 6400000000000 : ℝ) ≤
      (-(21217588054326763577179 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (766852490563 / 6400000000000 : ℚ))
        (r' := (766852490563 / 400000000000 : ℚ))
        (U := (-(21217588054326763577179 / 10000000000000000000000 : ℚ)))
        (U' := (6508299157673236422821 / 10000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau234 :
    Real.arctan (13200333796267 / 39062500000000 : ℝ) ≤
      (1629402640588147556519 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (13200333796267 / 39062500000000 : ℚ))
        (U := (1629402640588147556519 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1629402640588147556519 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (39062500000000 / 13200333796267 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (39062500000000 / 13200333796267 : ℝ) =
              (13200333796267 / 39062500000000 : ℝ)
            by
        norm_num];
        exact hau234)
  have hat2 :
    Real.arctan (750000000000000 / 3379285451844349 : ℝ) ≤
      (2184003797519659522247 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 3379285451844349 : ℚ))
        (U := (2184003797519659522247 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (730852490563 / 6400000000000 : ℚ))
      (lo := (3379285451844349 / 10000000000000000 : ℚ))
      (hi := (13200333796267 / 39062500000000 : ℚ))
      (s := (3379285451844349 / 10000000000000000 : ℚ))
      (r₁ := (7130852490563 / 6400000000000 : ℚ))
      (r₂ := (766852490563 / 6400000000000 : ℚ))
      (z₁ := (39062500000000 / 13200333796267 : ℚ))
      (z₂ := (750000000000000 / 3379285451844349 : ℚ))
      (L := (1081328008072146210999 / 10000000000000000000000 : ℚ))
      (U := (-(21217588054326763577179 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_173 :
    ((271117981685262172049 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1059419563440124122021 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3384465257433817 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3263453469630001012291 / 10000000000000000000000 : ℝ)) -
              6 * (2180766304264109440283 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (7330947250417 / 64000000000000 : ℝ) := by
  have hL1 :
    (271117981685262172049 / 2500000000000000000000 : ℝ) ≤
      Real.log (71330947250417 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (71330947250417 / 64000000000000 : ℚ))
        (L := (271117981685262172049 / 2500000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (7690947250417 / 64000000000000 : ℝ) ≤
      (-(1059419563440124122021 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7690947250417 / 64000000000000 : ℚ))
        (r' := (7690947250417 / 4000000000000 : ℚ))
        (U := (-(1059419563440124122021 / 500000000000000000000 : ℚ)))
        (U' := (326874797159875877979 / 500000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau235 :
    Real.arctan (169223262871691 / 500000000000000 : ℝ) ≤
      (3263453469630001012291 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (169223262871691 / 500000000000000 : ℚ))
        (U := (3263453469630001012291 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3263453469630001012291 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (500000000000000 / 169223262871691 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 169223262871691 : ℝ) =
              (169223262871691 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau235)
  have hat2 :
    Real.arctan (750000000000000 / 3384465257433817 : ℝ) ≤
      (2180766304264109440283 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 3384465257433817 : ℚ))
        (U := (2180766304264109440283 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (7330947250417 / 64000000000000 : ℚ))
      (lo := (3384465257433817 / 10000000000000000 : ℚ))
      (hi := (169223262871691 / 500000000000000 : ℚ))
      (s := (3384465257433817 / 10000000000000000 : ℚ))
      (r₁ := (71330947250417 / 64000000000000 : ℚ))
      (r₂ := (7690947250417 / 64000000000000 : ℚ))
      (z₁ := (500000000000000 / 169223262871691 : ℚ))
      (z₂ := (750000000000000 / 3384465257433817 : ℚ))
      (L := (271117981685262172049 / 2500000000000000000000 : ℚ))
      (U := (-(1059419563440124122021 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_174 :
    ((217522971459627535867 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5289819870100654850123 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1694818573808583 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3268093096395075635043 / 10000000000000000000000 : ℝ)) -
              6 * (2177543168845947543807 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1838342398801 / 16000000000000 : ℝ) := by
  have hL1 :
    (217522971459627535867 / 2000000000000000000000 : ℝ) ≤
      Real.log (17838342398801 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (17838342398801 / 16000000000000 : ℚ))
        (L := (217522971459627535867 / 2000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (1928342398801 / 16000000000000 : ℝ) ≤
      (-(5289819870100654850123 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1928342398801 / 16000000000000 : ℚ))
        (r' := (1928342398801 / 1000000000000 : ℚ))
        (U := (-(5289819870100654850123 / 2500000000000000000000 : ℚ)))
        (U' := (1641651932899345149877 / 2500000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau236 :
    Real.arctan (3389637147617169 / 10000000000000000 : ℝ) ≤
      (3268093096395075635043 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3389637147617169 / 10000000000000000 : ℚ))
        (U := (3268093096395075635043 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3268093096395075635043 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3389637147617169 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3389637147617169 : ℝ) =
              (3389637147617169 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau236)
  have hat2 :
    Real.arctan (125000000000000 / 564939524602861 : ℝ) ≤
      (2177543168845947543807 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (125000000000000 / 564939524602861 : ℚ))
        (U := (2177543168845947543807 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1838342398801 / 16000000000000 : ℚ))
      (lo := (1694818573808583 / 5000000000000000 : ℚ))
      (hi := (3389637147617169 / 10000000000000000 : ℚ))
      (s := (1694818573808583 / 5000000000000000 : ℚ))
      (r₁ := (17838342398801 / 16000000000000 : ℚ))
      (r₂ := (1928342398801 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3389637147617169 : ℚ))
      (z₂ := (125000000000000 / 564939524602861 : ℚ))
      (L := (217522971459627535867 / 2000000000000000000000 : ℚ))
      (U := (-(5289819870100654850123 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_175 :
    ((1093897756559963010019 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2637663615683673257443 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((339995732619773 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1638673407935689605673 / 5000000000000000000000 : ℝ)) -
              6 * (2171139549275033092439 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (3699107142389 / 32000000000000 : ℝ) := by
  have hL1 :
    (1093897756559963010019 / 10000000000000000000000 : ℝ) ≤
      Real.log (35699107142389 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (35699107142389 / 32000000000000 : ℚ))
        (L := (1093897756559963010019 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (3879107142389 / 32000000000000 : ℝ) ≤
      (-(2637663615683673257443 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3879107142389 / 32000000000000 : ℚ))
        (r' := (3879107142389 / 2000000000000 : ℚ))
        (U := (-(2637663615683673257443 / 1250000000000000000000 : ℚ)))
        (U' := (828072285816326742557 / 1250000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau237 :
    Real.arctan (3399957326197733 / 10000000000000000 : ℝ) ≤
      (1638673407935689605673 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3399957326197733 / 10000000000000000 : ℚ))
        (U := (1638673407935689605673 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1638673407935689605673 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3399957326197733 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3399957326197733 : ℝ) =
              (3399957326197733 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau237)
  have hat2 :
    Real.arctan (75000000000000 / 339995732619773 : ℝ) ≤
      (2171139549275033092439 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (75000000000000 / 339995732619773 : ℚ))
        (U := (2171139549275033092439 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (3699107142389 / 32000000000000 : ℚ))
      (lo := (339995732619773 / 1000000000000000 : ℚ))
      (hi := (3399957326197733 / 10000000000000000 : ℚ))
      (s := (339995732619773 / 1000000000000000 : ℚ))
      (r₁ := (35699107142389 / 32000000000000 : ℚ))
      (r₂ := (3879107142389 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3399957326197733 : ℚ))
      (z₂ := (75000000000000 / 339995732619773 : ℚ))
      (L := (1093897756559963010019 / 10000000000000000000000 : ℚ))
      (U := (-(2637663615683673257443 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_176 :
    ((4400706843271805573 / 40000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10521836246531778932779 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((852561568430141 / 2500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1643283369413787703769 / 5000000000000000000000 : ℝ)) -
              6 * (135299506569951335849 / 625000000000000000000 : ℝ)))) ≤
      Vfield (465191185897 / 4000000000000 : ℝ) := by
  have hL1 :
    (4400706843271805573 / 40000000000000000000 : ℝ) ≤
      Real.log (4465191185897 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (4465191185897 / 4000000000000 : ℚ))
        (L := (4400706843271805573 / 40000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (487691185897 / 4000000000000 : ℝ) ≤
      (-(10521836246531778932779 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (487691185897 / 4000000000000 : ℚ))
        (r' := (487691185897 / 250000000000 : ℚ))
        (U := (-(10521836246531778932779 / 5000000000000000000000 : ℚ)))
        (U' := (3341107359468221067221 / 5000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau238 :
    Real.arctan (3410246273720567 / 10000000000000000 : ℝ) ≤
      (1643283369413787703769 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3410246273720567 / 10000000000000000 : ℚ))
        (U := (1643283369413787703769 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1643283369413787703769 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3410246273720567 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3410246273720567 : ℝ) =
              (3410246273720567 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau238)
  have hat2 :
    Real.arctan (187500000000000 / 852561568430141 : ℝ) ≤
      (135299506569951335849 / 625000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 852561568430141 : ℚ))
        (U := (135299506569951335849 / 625000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (465191185897 / 4000000000000 : ℚ))
      (lo := (852561568430141 / 2500000000000000 : ℚ))
      (hi := (3410246273720567 / 10000000000000000 : ℚ))
      (s := (852561568430141 / 2500000000000000 : ℚ))
      (r₁ := (4465191185897 / 4000000000000 : ℚ))
      (r₂ := (487691185897 / 4000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3410246273720567 : ℚ))
      (z₂ := (187500000000000 / 852561568430141 : ℚ))
      (L := (4400706843271805573 / 40000000000000000000 : ℚ))
      (U := (-(10521836246531778932779 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_177 :
    ((1106451725023094177469 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10493183176854784838949 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3420504272016681 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3295753160068787053413 / 10000000000000000000000 : ℝ)) -
              6 * (431700003932662026033 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (3743951831963 / 32000000000000 : ℝ) := by
  have hL1 :
    (1106451725023094177469 / 10000000000000000000000 : ℝ) ≤
      Real.log (35743951831963 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (35743951831963 / 32000000000000 : ℚ))
        (L := (1106451725023094177469 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (3923951831963 / 32000000000000 : ℝ) ≤
      (-(10493183176854784838949 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3923951831963 / 32000000000000 : ℚ))
        (r' := (3923951831963 / 2000000000000 : ℚ))
        (U := (-(10493183176854784838949 / 5000000000000000000000 : ℚ)))
        (U' := (3369760429145215161051 / 5000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau239 :
    Real.arctan (855126068004171 / 2500000000000000 : ℝ) ≤
      (3295753160068787053413 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (855126068004171 / 2500000000000000 : ℚ))
        (U := (3295753160068787053413 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3295753160068787053413 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 855126068004171 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 855126068004171 : ℝ) =
              (855126068004171 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau239)
  have hat2 :
    Real.arctan (250000000000000 / 1140168090672227 : ℝ) ≤
      (431700003932662026033 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1140168090672227 : ℚ))
        (U := (431700003932662026033 / 2000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (3743951831963 / 32000000000000 : ℚ))
      (lo := (3420504272016681 / 10000000000000000 : ℚ))
      (hi := (855126068004171 / 2500000000000000 : ℚ))
      (s := (3420504272016681 / 10000000000000000 : ℚ))
      (r₁ := (35743951831963 / 32000000000000 : ℚ))
      (r₂ := (3923951831963 / 32000000000000 : ℚ))
      (z₁ := (2500000000000000 / 855126068004171 : ℚ))
      (z₂ := (250000000000000 / 1140168090672227 : ℚ))
      (L := (1106451725023094177469 / 10000000000000000000000 : ℚ))
      (U := (-(10493183176854784838949 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_178 :
    ((222544560823413658539 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2092938674339300144207 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((686146319740731 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (66098127401491722431 / 200000000000000000000 : ℝ)) -
              6 * (1076131246361408251279 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (15065496707 / 128000000000 : ℝ) := by
  have hL1 :
    (222544560823413658539 / 2000000000000000000000 : ℝ) ≤
      Real.log (143065496707 / 128000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (143065496707 / 128000000000 : ℚ))
        (L := (222544560823413658539 / 2000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (15785496707 / 128000000000 : ℝ) ≤
      (-(2092938674339300144207 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (15785496707 / 128000000000 : ℚ))
        (r' := (15785496707 / 8000000000 : ℚ))
        (U := (-(2092938674339300144207 / 1000000000000000000000 : ℚ)))
        (U' := (679650046860699855793 / 1000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau240 :
    Real.arctan (1715365799351829 / 5000000000000000 : ℝ) ≤
      (66098127401491722431 / 200000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1715365799351829 / 5000000000000000 : ℚ))
        (U := (66098127401491722431 / 200000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (66098127401491722431 / 200000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1715365799351829 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1715365799351829 : ℝ) =
              (1715365799351829 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau240)
  have hat2 :
    Real.arctan (50000000000000 / 228715439913577 : ℝ) ≤
      (1076131246361408251279 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (50000000000000 / 228715439913577 : ℚ))
        (U := (1076131246361408251279 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (15065496707 / 128000000000 : ℚ))
      (lo := (686146319740731 / 2000000000000000 : ℚ))
      (hi := (1715365799351829 / 5000000000000000 : ℚ))
      (s := (686146319740731 / 2000000000000000 : ℚ))
      (r₁ := (143065496707 / 128000000000 : ℚ))
      (r₂ := (15785496707 / 128000000000 : ℚ))
      (z₁ := (5000000000000000 / 1715365799351829 : ℚ))
      (z₂ := (50000000000000 / 228715439913577 : ℚ))
      (L := (222544560823413658539 / 2000000000000000000000 : ℚ))
      (U := (-(2092938674339300144207 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_179 :
    ((1118989953032259600469 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(20872729962077034974551 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3440928527273287 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3314026655088241252493 / 10000000000000000000000 : ℝ)) -
              6 * (429215748043235457857 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (3788796521537 / 32000000000000 : ℝ) := by
  have hL1 :
    (1118989953032259600469 / 10000000000000000000000 : ℝ) ≤
      Real.log (35788796521537 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (35788796521537 / 32000000000000 : ℚ))
        (L := (1118989953032259600469 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (3968796521537 / 32000000000000 : ℝ) ≤
      (-(20872729962077034974551 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3968796521537 / 32000000000000 : ℚ))
        (r' := (3968796521537 / 2000000000000 : ℚ))
        (U := (-(20872729962077034974551 / 10000000000000000000000 : ℚ)))
        (U' := (6853157249922965025449 / 10000000000000000000000 : ℚ))
        4 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau241 :
    Real.arctan (344092852727329 / 1000000000000000 : ℝ) ≤
      (3314026655088241252493 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (344092852727329 / 1000000000000000 : ℚ))
        (U := (3314026655088241252493 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3314026655088241252493 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 344092852727329 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 344092852727329 : ℝ) =
              (344092852727329 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau241)
  have hat2 :
    Real.arctan (750000000000000 / 3440928527273287 : ℝ) ≤
      (429215748043235457857 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 3440928527273287 : ℚ))
        (U := (429215748043235457857 / 2000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (3788796521537 / 32000000000000 : ℚ))
      (lo := (3440928527273287 / 10000000000000000 : ℚ))
      (hi := (344092852727329 / 1000000000000000 : ℚ))
      (s := (3440928527273287 / 10000000000000000 : ℚ))
      (r₁ := (35788796521537 / 32000000000000 : ℚ))
      (r₂ := (3968796521537 / 32000000000000 : ℚ))
      (z₁ := (1000000000000000 / 344092852727329 : ℚ))
      (z₂ := (750000000000000 / 3440928527273287 : ℚ))
      (L := (1118989953032259600469 / 10000000000000000000000 : ℚ))
      (U := (-(20872729962077034974551 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_180 :
    ((45010127067671446827 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(20816392372260701008297 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3451095327176937 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (332311429720360928943 / 1000000000000000000000 : ℝ)) -
              6 * (2139947993750407451587 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (952804716581 / 8000000000000 : ℝ) := by
  have hL1 :
    (45010127067671446827 / 400000000000000000000 : ℝ) ≤
      Real.log (8952804716581 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (8952804716581 / 8000000000000 : ℚ))
        (L := (45010127067671446827 / 400000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (997804716581 / 8000000000000 : ℝ) ≤
      (-(20816392372260701008297 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (997804716581 / 8000000000000 : ℚ))
        (r' := (997804716581 / 500000000000 : ℚ))
        (U := (-(20816392372260701008297 / 10000000000000000000000 : ℚ)))
        (U' := (6909494839739298991703 / 10000000000000000000000 : ℚ))
        4 15 (by decide +kernel) (by constructor <;> norm_num)
  have hau242 :
    Real.arctan (172554766358847 / 500000000000000 : ℝ) ≤
      (332311429720360928943 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (172554766358847 / 500000000000000 : ℚ))
        (U := (332311429720360928943 / 1000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (332311429720360928943 / 1000000000000000000000 : ℝ)) ≤
      Real.arctan (500000000000000 / 172554766358847 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 172554766358847 : ℝ) =
              (172554766358847 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau242)
  have hat2 :
    Real.arctan (250000000000000 / 1150365109058979 : ℝ) ≤
      (2139947993750407451587 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1150365109058979 : ℚ))
        (U := (2139947993750407451587 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (952804716581 / 8000000000000 : ℚ))
      (lo := (3451095327176937 / 10000000000000000 : ℚ))
      (hi := (172554766358847 / 500000000000000 : ℚ))
      (s := (3451095327176937 / 10000000000000000 : ℚ))
      (r₁ := (8952804716581 / 8000000000000 : ℚ))
      (r₂ := (997804716581 / 8000000000000 : ℚ))
      (z₁ := (500000000000000 / 172554766358847 : ℚ))
      (z₂ := (250000000000000 / 1150365109058979 : ℚ))
      (L := (45010127067671446827 / 400000000000000000000 : ℚ))
      (U := (-(20816392372260701008297 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
