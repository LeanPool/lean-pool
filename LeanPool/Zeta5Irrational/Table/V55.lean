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

/-! # V55: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped ArctangentCertificates LogarithmCertificates

lemma V_661 :
    ((1145983301800406914357 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(499000694584906999959 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1759050891838961 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3606936715486809115069 / 10000000000000000000000 : ℝ))) -
              6 * (170134931662895184751 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (396065285130169 / 512000000000000 : ℝ) := by
  have hL1 :
    (1145983301800406914357 / 2000000000000000000000 : ℝ) ≤
      Real.log (908065285130169 / 512000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (908065285130169 / 512000000000000 : ℚ))
        (L := (1145983301800406914357 / 2000000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (398945285130169 / 512000000000000 : ℝ) ≤
      (-(499000694584906999959 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (398945285130169 / 512000000000000 : ℚ))
        (r' := (398945285130169 / 256000000000000 : ℚ))
        (U := (-(499000694584906999959 / 2000000000000000000000 : ℚ)))
        (U' := (887293666015093000041 / 2000000000000000000000 : ℚ))
        1 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau1094 :
    Real.arctan (2198813614798702 / 5829381521037223 : ℝ) ≤
      (3606936715486809115069 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2198813614798702 / 5829381521037223 : ℚ))
        (U := (3606936715486809115069 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1093 :
    Real.arctan (1099406807399351 / 1250000000000000 : ℝ) ≤
      (2 * (3606936715486809115069 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3329381521037223 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1099406807399351 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1099406807399351 / 1250000000000000 : ℝ) /
                (1 + (3329381521037223 / 2500000000000000 : ℝ)) =
              (2198813614798702 / 5829381521037223 : ℝ)
            by
        norm_num];
        exact hau1094)
  have hat1 :
    (Real.pi / 2 - (2 * (3606936715486809115069 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 1099406807399351 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 1099406807399351 : ℝ) =
              (1099406807399351 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau1093)
  have hat2 :
    Real.arctan (150000000000000 / 1759050891838961 : ℝ) ≤
      (170134931662895184751 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 1759050891838961 : ℚ))
        (U := (170134931662895184751 / 2000000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (396065285130169 / 512000000000000 : ℚ))
      (lo := (1759050891838961 / 2000000000000000 : ℚ))
      (hi := (1099406807399351 / 1250000000000000 : ℚ))
      (s := (1759050891838961 / 2000000000000000 : ℚ))
      (r₁ := (908065285130169 / 512000000000000 : ℚ))
      (r₂ := (398945285130169 / 512000000000000 : ℚ))
      (z₁ := (1250000000000000 / 1099406807399351 : ℚ))
      (z₂ := (150000000000000 / 1759050891838961 : ℚ))
      (L := (1145983301800406914357 / 2000000000000000000000 : ℚ))
      (U := (-(499000694584906999959 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_662 :
    ((1148741910766415787971 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2463635813600251484823 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8809159914837269 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3610854212269592993969 / 10000000000000000000000 : ℝ))) -
              6 * (169867660582945952537 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (794637295669 / 1024000000000 : ℝ) := by
  have hL1 :
    (1148741910766415787971 / 2000000000000000000000 : ℝ) ≤
      Real.log (1818637295669 / 1024000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1818637295669 / 1024000000000 : ℚ))
        (L := (1148741910766415787971 / 2000000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (800397295669 / 1024000000000 : ℝ) ≤
      (-(2463635813600251484823 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (800397295669 / 1024000000000 : ℚ))
        (r' := (800397295669 / 512000000000 : ℚ))
        (U := (-(2463635813600251484823 / 10000000000000000000000 : ℚ)))
        (U' := (4467835989399748515177 / 10000000000000000000000 : ℚ))
        1 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau1096 :
    Real.arctan (2202289978709318 / 5831678428408643 : ℝ) ≤
      (3610854212269592993969 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2202289978709318 / 5831678428408643 : ℚ))
        (U := (3610854212269592993969 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1095 :
    Real.arctan (1101144989354659 / 1250000000000000 : ℝ) ≤
      (2 * (3610854212269592993969 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3331678428408643 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1101144989354659 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1101144989354659 / 1250000000000000 : ℝ) /
                (1 + (3331678428408643 / 2500000000000000 : ℝ)) =
              (2202289978709318 / 5831678428408643 : ℝ)
            by
        norm_num];
        exact hau1096)
  have hat1 :
    (Real.pi / 2 - (2 * (3610854212269592993969 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 1101144989354659 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 1101144989354659 : ℝ) =
              (1101144989354659 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau1095)
  have hat2 :
    Real.arctan (750000000000000 / 8809159914837269 : ℝ) ≤
      (169867660582945952537 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 8809159914837269 : ℚ))
        (U := (169867660582945952537 / 2000000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (794637295669 / 1024000000000 : ℚ))
      (lo := (8809159914837269 / 10000000000000000 : ℚ))
      (hi := (1101144989354659 / 1250000000000000 : ℚ))
      (s := (8809159914837269 / 10000000000000000 : ℚ))
      (r₁ := (1818637295669 / 1024000000000 : ℚ))
      (r₂ := (800397295669 / 1024000000000 : ℚ))
      (z₁ := (1250000000000000 / 1101144989354659 : ℚ))
      (z₂ := (750000000000000 / 8809159914837269 : ℚ))
      (L := (1148741910766415787971 / 2000000000000000000000 : ℚ))
      (U := (-(2463635813600251484823 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_663 :
    ((5757483600055410461667 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1216183119845151522901 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2205760863743583 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3614760147456547547451 / 10000000000000000000000 : ℝ))) -
              6 * (42400411290363432093 / 500000000000000000000 : ℝ)))) ≤
      Vfield (398572010538831 / 512000000000000 : ℝ) := by
  have hL1 :
    (5757483600055410461667 / 10000000000000000000000 : ℝ) ≤
      Real.log (910572010538831 / 512000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (910572010538831 / 512000000000000 : ℚ))
        (L := (5757483600055410461667 / 10000000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (401452010538831 / 512000000000000 : ℝ) ≤
      (-(1216183119845151522901 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (401452010538831 / 512000000000000 : ℚ))
        (r' := (401452010538831 / 256000000000000 : ℚ))
        (U := (-(1216183119845151522901 / 5000000000000000000000 : ℚ)))
        (U' := (2249552781654848477099 / 5000000000000000000000 : ℚ))
        1 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau1098 :
    Real.arctan (8823043454974335 / 23335895013397691 : ℝ) ≤
      (3614760147456547547451 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8823043454974335 / 23335895013397691 : ℚ))
        (U := (3614760147456547547451 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1097 :
    Real.arctan (1764608690994867 / 2000000000000000 : ℝ) ≤
      (2 * (3614760147456547547451 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13335895013397691 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1764608690994867 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1764608690994867 / 2000000000000000 : ℝ) /
                (1 + (13335895013397691 / 10000000000000000 : ℝ)) =
              (8823043454974335 / 23335895013397691 : ℝ)
            by
        norm_num];
        exact hau1098)
  have hat1 :
    (Real.pi / 2 - (2 * (3614760147456547547451 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1764608690994867 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1764608690994867 : ℝ) =
              (1764608690994867 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau1097)
  have hat2 :
    Real.arctan (62500000000000 / 735253621247861 : ℝ) ≤
      (42400411290363432093 / 500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (62500000000000 / 735253621247861 : ℚ))
        (U := (42400411290363432093 / 500000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (398572010538831 / 512000000000000 : ℚ))
      (lo := (2205760863743583 / 2500000000000000 : ℚ))
      (hi := (1764608690994867 / 2000000000000000 : ℚ))
      (s := (2205760863743583 / 2500000000000000 : ℚ))
      (r₁ := (910572010538831 / 512000000000000 : ℚ))
      (r₂ := (401452010538831 / 512000000000000 : ℚ))
      (z₁ := (2000000000000000 / 1764608690994867 : ℚ))
      (z₂ := (62500000000000 / 735253621247861 : ℚ))
      (L := (5757483600055410461667 / 10000000000000000000000 : ℚ))
      (U := (-(1216183119845151522901 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_664 :
    ((5771238699937592243929 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(120059706984401290531 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2209226295724861 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1809327290937027190591 / 5000000000000000000000 : ℝ))) -
              6 * (846684377985567652479 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (199912686621581 / 256000000000000 : ℝ) := by
  have hL1 :
    (5771238699937592243929 / 10000000000000000000000 : ℝ) ≤
      Real.log (455912686621581 / 256000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (455912686621581 / 256000000000000 : ℚ))
        (L := (5771238699937592243929 / 10000000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (201352686621581 / 256000000000000 : ℝ) ≤
      (-(120059706984401290531 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (201352686621581 / 256000000000000 : ℚ))
        (r' := (201352686621581 / 128000000000000 : ℚ))
        (U := (-(120059706984401290531 / 500000000000000000000 : ℚ)))
        (U' := (226513883165598709469 / 500000000000000000000 : ℚ))
        1 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau1100 :
    Real.arctan (8836905182899447 / 23345069996502644 : ℝ) ≤
      (1809327290937027190591 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8836905182899447 / 23345069996502644 : ℚ))
        (U := (1809327290937027190591 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1099 :
    Real.arctan (8836905182899447 / 10000000000000000 : ℝ) ≤
      (2 * (1809327290937027190591 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3336267499125661 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8836905182899447 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8836905182899447 / 10000000000000000 : ℝ) /
                (1 + (3336267499125661 / 2500000000000000 : ℝ)) =
              (8836905182899447 / 23345069996502644 : ℝ)
            by
        norm_num];
        exact hau1100)
  have hat1 :
    (Real.pi / 2 - (2 * (1809327290937027190591 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8836905182899447 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8836905182899447 : ℝ) =
              (8836905182899447 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1099)
  have hat2 :
    Real.arctan (187500000000000 / 2209226295724861 : ℝ) ≤
      (846684377985567652479 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 2209226295724861 : ℚ))
        (U := (846684377985567652479 / 10000000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (199912686621581 / 256000000000000 : ℚ))
      (lo := (2209226295724861 / 2500000000000000 : ℚ))
      (hi := (8836905182899447 / 10000000000000000 : ℚ))
      (s := (2209226295724861 / 2500000000000000 : ℚ))
      (r₁ := (455912686621581 / 256000000000000 : ℚ))
      (r₂ := (201352686621581 / 256000000000000 : ℚ))
      (z₁ := (10000000000000000 / 8836905182899447 : ℚ))
      (z₂ := (187500000000000 / 2209226295724861 : ℚ))
      (L := (5771238699937592243929 / 10000000000000000000000 : ℚ))
      (U := (-(120059706984401290531 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_665 :
    ((5798692268665044501883 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(46782798876266465479 / 200000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((886456361125207 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3626409189323357591577 / 10000000000000000000000 : ℝ))) -
              6 * (844055176835286775381 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (25145756165739 / 32000000000000 : ℝ) := by
  have hL1 :
    (5798692268665044501883 / 10000000000000000000000 : ℝ) ≤
      Real.log (57145756165739 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (57145756165739 / 32000000000000 : ℚ))
        (L := (5798692268665044501883 / 10000000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (25325756165739 / 32000000000000 : ℝ) ≤
      (-(46782798876266465479 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (25325756165739 / 32000000000000 : ℚ))
        (r' := (25325756165739 / 16000000000000 : ℚ))
        (U := (-(46782798876266465479 / 200000000000000000000 : ℚ)))
        (U' := (91846637183733534521 / 200000000000000000000 : ℚ))
        1 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau1102 :
    Real.arctan (8864563611252073 / 23363401064771436 : ℝ) ≤
      (3626409189323357591577 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8864563611252073 / 23363401064771436 : ℚ))
        (U := (3626409189323357591577 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1101 :
    Real.arctan (8864563611252073 / 10000000000000000 : ℝ) ≤
      (2 * (3626409189323357591577 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3340850266192859 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (8864563611252073 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8864563611252073 / 10000000000000000 : ℝ) /
                (1 + (3340850266192859 / 2500000000000000 : ℝ)) =
              (8864563611252073 / 23363401064771436 : ℝ)
            by
        norm_num];
        exact hau1102)
  have hat1 :
    (Real.pi / 2 - (2 * (3626409189323357591577 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8864563611252073 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8864563611252073 : ℝ) =
              (8864563611252073 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1101)
  have hat2 :
    Real.arctan (75000000000000 / 886456361125207 : ℝ) ≤
      (844055176835286775381 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (75000000000000 / 886456361125207 : ℚ))
        (U := (844055176835286775381 / 10000000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (25145756165739 / 32000000000000 : ℚ))
      (lo := (886456361125207 / 1000000000000000 : ℚ))
      (hi := (8864563611252073 / 10000000000000000 : ℚ))
      (s := (886456361125207 / 1000000000000000 : ℚ))
      (r₁ := (57145756165739 / 32000000000000 : ℚ))
      (r₂ := (25325756165739 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 8864563611252073 : ℚ))
      (z₂ := (75000000000000 / 886456361125207 : ℚ))
      (L := (5798692268665044501883 / 10000000000000000000000 : ℚ))
      (U := (-(46782798876266465479 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_666 :
    ((728258834231571345467 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2277468446675428642341 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2223034002555877 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (363411851176786735763 / 1000000000000000000000 : ℝ))) -
              6 * (420725158977982490263 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (202419412030243 / 256000000000000 : ℝ) := by
  have hL1 :
    (728258834231571345467 / 1250000000000000000000 : ℝ) ≤
      Real.log (458419412030243 / 256000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (458419412030243 / 256000000000000 : ℚ))
        (L := (728258834231571345467 / 1250000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (203859412030243 / 256000000000000 : ℝ) ≤
      (-(2277468446675428642341 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (203859412030243 / 256000000000000 : ℚ))
        (r' := (203859412030243 / 128000000000000 : ℚ))
        (U := (-(2277468446675428642341 / 10000000000000000000000 : ℚ)))
        (U' := (4654003356324571357659 / 10000000000000000000000 : ℚ))
        1 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau1104 :
    Real.arctan (8892136010223511 / 23381707022062382 : ℝ) ≤
      (363411851176786735763 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8892136010223511 / 23381707022062382 : ℚ))
        (U := (363411851176786735763 / 1000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1103 :
    Real.arctan (8892136010223511 / 10000000000000000 : ℝ) ≤
      (2 * (363411851176786735763 / 1000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6690853511031191 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8892136010223511 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8892136010223511 / 10000000000000000 : ℝ) /
                (1 + (6690853511031191 / 5000000000000000 : ℝ)) =
              (8892136010223511 / 23381707022062382 : ℝ)
            by
        norm_num];
        exact hau1104)
  have hat1 :
    (Real.pi / 2 - (2 * (363411851176786735763 / 1000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8892136010223511 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8892136010223511 : ℝ) =
              (8892136010223511 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1103)
  have hat2 :
    Real.arctan (187500000000000 / 2223034002555877 : ℝ) ≤
      (420725158977982490263 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 2223034002555877 : ℚ))
        (U := (420725158977982490263 / 5000000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (202419412030243 / 256000000000000 : ℚ))
      (lo := (2223034002555877 / 2500000000000000 : ℚ))
      (hi := (8892136010223511 / 10000000000000000 : ℚ))
      (s := (2223034002555877 / 2500000000000000 : ℚ))
      (r₁ := (458419412030243 / 256000000000000 : ℚ))
      (r₂ := (203859412030243 / 256000000000000 : ℚ))
      (z₁ := (10000000000000000 / 8892136010223511 : ℚ))
      (z₂ := (187500000000000 / 2223034002555877 : ℚ))
      (L := (728258834231571345467 / 1250000000000000000000 : ℚ))
      (U := (-(2277468446675428642341 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_667 :
    ((5853374325948511987951 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(44323499137129365541 / 200000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1114952897202199 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1820891509478601631143 / 5000000000000000000000 : ℝ))) -
              6 * (167773885606187475007 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (101836387367287 / 128000000000000 : ℝ) := by
  have hL1 :
    (5853374325948511987951 / 10000000000000000000000 : ℝ) ≤
      Real.log (229836387367287 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (229836387367287 / 128000000000000 : ℚ))
        (L := (5853374325948511987951 / 10000000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (102556387367287 / 128000000000000 : ℝ) ≤
      (-(44323499137129365541 / 200000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (102556387367287 / 128000000000000 : ℚ))
        (r' := (102556387367287 / 64000000000000 : ℚ))
        (U := (-(44323499137129365541 / 200000000000000000000 : ℚ)))
        (U' := (94305936922870634459 / 200000000000000000000 : ℚ))
        1 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau1106 :
    Real.arctan (1783924635523519 / 4679997594257823 : ℝ) ≤
      (1820891509478601631143 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1783924635523519 / 4679997594257823 : ℚ))
        (U := (1820891509478601631143 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1105 :
    Real.arctan (1783924635523519 / 2000000000000000 : ℝ) ≤
      (2 * (1820891509478601631143 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2679997594257823 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1783924635523519 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1783924635523519 / 2000000000000000 : ℝ) /
                (1 + (2679997594257823 / 2000000000000000 : ℝ)) =
              (1783924635523519 / 4679997594257823 : ℝ)
            by
        norm_num];
        exact hau1106)
  have hat1 :
    (Real.pi / 2 - (2 * (1820891509478601631143 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1783924635523519 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1783924635523519 : ℝ) =
              (1783924635523519 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau1105)
  have hat2 :
    Real.arctan (93750000000000 / 1114952897202199 : ℝ) ≤
      (167773885606187475007 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (93750000000000 / 1114952897202199 : ℚ))
        (U := (167773885606187475007 / 2000000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (101836387367287 / 128000000000000 : ℚ))
      (lo := (1114952897202199 / 1250000000000000 : ℚ))
      (hi := (1783924635523519 / 2000000000000000 : ℚ))
      (s := (1114952897202199 / 1250000000000000 : ℚ))
      (r₁ := (229836387367287 / 128000000000000 : ℚ))
      (r₂ := (102556387367287 / 128000000000000 : ℚ))
      (z₁ := (2000000000000000 / 1783924635523519 : ℚ))
      (z₂ := (93750000000000 / 1114952897202199 : ℚ))
      (L := (5853374325948511987951 / 10000000000000000000000 : ℚ))
      (U := (-(44323499137129365541 / 200000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_668 :
    ((2940301816024167914831 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(86210194747194041833 / 400000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4473512949491491 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (729880634679149746393 / 2000000000000000000000 : ℝ))) -
              6 * (418156070855025838797 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (40985227487781 / 51200000000000 : ℝ) := by
  have hL1 :
    (2940301816024167914831 / 5000000000000000000000 : ℝ) ≤
      Real.log (92185227487781 / 51200000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (92185227487781 / 51200000000000 : ℚ))
        (L := (2940301816024167914831 / 5000000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (41273227487781 / 51200000000000 : ℝ) ≤
      (-(86210194747194041833 / 400000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (41273227487781 / 51200000000000 : ℚ))
        (r' := (41273227487781 / 25600000000000 : ℚ))
        (U := (-(86210194747194041833 / 400000000000000000000 : ℚ)))
        (U' := (191048677372805958167 / 400000000000000000000 : ℚ))
        1 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau1108 :
    Real.arctan (8947025898982985 / 23418244014664223 : ℝ) ≤
      (729880634679149746393 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8947025898982985 / 23418244014664223 : ℚ))
        (U := (729880634679149746393 / 2000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1107 :
    Real.arctan (1789405179796597 / 2000000000000000 : ℝ) ≤
      (2 * (729880634679149746393 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13418244014664223 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1789405179796597 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1789405179796597 / 2000000000000000 : ℝ) /
                (1 + (13418244014664223 / 10000000000000000 : ℝ)) =
              (8947025898982985 / 23418244014664223 : ℝ)
            by
        norm_num];
        exact hau1108)
  have hat1 :
    (Real.pi / 2 - (2 * (729880634679149746393 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1789405179796597 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1789405179796597 : ℝ) =
              (1789405179796597 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau1107)
  have hat2 :
    Real.arctan (375000000000000 / 4473512949491491 : ℝ) ≤
      (418156070855025838797 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 4473512949491491 : ℚ))
        (U := (418156070855025838797 / 5000000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (40985227487781 / 51200000000000 : ℚ))
      (lo := (4473512949491491 / 5000000000000000 : ℚ))
      (hi := (1789405179796597 / 2000000000000000 : ℚ))
      (s := (4473512949491491 / 5000000000000000 : ℚ))
      (r₁ := (92185227487781 / 51200000000000 : ℚ))
      (r₂ := (41273227487781 / 51200000000000 : ℚ))
      (z₁ := (2000000000000000 / 1789405179796597 : ℚ))
      (z₂ := (375000000000000 / 4473512949491491 : ℚ))
      (L := (2940301816024167914831 / 5000000000000000000000 : ℚ))
      (U := (-(86210194747194041833 / 400000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_669 :
    ((1476939748982764032159 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2094703660133547240031 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8974344947875111 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3656979430493994796031 / 10000000000000000000000 : ℝ))) -
              6 * (833778101392414941191 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (51544875035809 / 64000000000000 : ℝ) := by
  have hL1 :
    (1476939748982764032159 / 2500000000000000000000 : ℝ) ≤
      Real.log (115544875035809 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (115544875035809 / 64000000000000 : ℚ))
        (L := (1476939748982764032159 / 2500000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (51904875035809 / 64000000000000 : ℝ) ≤
      (-(2094703660133547240031 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (51904875035809 / 64000000000000 : ℚ))
        (r' := (51904875035809 / 32000000000000 : ℚ))
        (U := (-(2094703660133547240031 / 10000000000000000000000 : ℚ)))
        (U' := (4836768142866452759969 / 10000000000000000000000 : ℚ))
        1 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau1110 :
    Real.arctan (8974344947875114 / 23436475253705919 : ℝ) ≤
      (3656979430493994796031 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8974344947875114 / 23436475253705919 : ℚ))
        (U := (3656979430493994796031 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1109 :
    Real.arctan (4487172473937557 / 5000000000000000 : ℝ) ≤
      (2 * (3656979430493994796031 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13436475253705919 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4487172473937557 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4487172473937557 / 5000000000000000 : ℝ) /
                (1 + (13436475253705919 / 10000000000000000 : ℝ)) =
              (8974344947875114 / 23436475253705919 : ℝ)
            by
        norm_num];
        exact hau1110)
  have hat1 :
    (Real.pi / 2 - (2 * (3656979430493994796031 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4487172473937557 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4487172473937557 : ℝ) =
              (4487172473937557 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau1109)
  have hat2 :
    Real.arctan (750000000000000 / 8974344947875111 : ℝ) ≤
      (833778101392414941191 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 8974344947875111 : ℚ))
        (U := (833778101392414941191 / 10000000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (51544875035809 / 64000000000000 : ℚ))
      (lo := (8974344947875111 / 10000000000000000 : ℚ))
      (hi := (4487172473937557 / 5000000000000000 : ℚ))
      (s := (8974344947875111 / 10000000000000000 : ℚ))
      (r₁ := (115544875035809 / 64000000000000 : ℚ))
      (r₂ := (51904875035809 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 4487172473937557 : ℚ))
      (z₂ := (750000000000000 / 8974344947875111 : ℚ))
      (L := (1476939748982764032159 / 2500000000000000000000 : ℚ))
      (U := (-(2094703660133547240031 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_670 :
    ((5961849495794045218043 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1974690200181473962903 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2257183766004251 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3672002039722087261413 / 10000000000000000000000 : ℝ))) -
              6 * (828778365856198504881 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (104343112775949 / 128000000000000 : ℝ) := by
  have hL1 :
    (5961849495794045218043 / 10000000000000000000000 : ℝ) ≤
      Real.log (232343112775949 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (232343112775949 / 128000000000000 : ℚ))
        (L := (5961849495794045218043 / 10000000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (105063112775949 / 128000000000000 : ℝ) ≤
      (-(1974690200181473962903 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (105063112775949 / 128000000000000 : ℚ))
        (r' := (105063112775949 / 64000000000000 : ℚ))
        (U := (-(1974690200181473962903 / 10000000000000000000000 : ℚ)))
        (U' := (4956781602818526037097 / 10000000000000000000000 : ℚ))
        1 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau1112 :
    Real.arctan (9028735064017007 / 23472863721429463 : ℝ) ≤
      (3672002039722087261413 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (9028735064017007 / 23472863721429463 : ℚ))
        (U := (3672002039722087261413 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1111 :
    Real.arctan (9028735064017007 / 10000000000000000 : ℝ) ≤
      (2 * (3672002039722087261413 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (13472863721429463 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (9028735064017007 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (9028735064017007 / 10000000000000000 : ℝ) /
                (1 + (13472863721429463 / 10000000000000000 : ℝ)) =
              (9028735064017007 / 23472863721429463 : ℝ)
            by
        norm_num];
        exact hau1112)
  have hat1 :
    (Real.pi / 2 - (2 * (3672002039722087261413 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 9028735064017007 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 9028735064017007 : ℝ) =
              (9028735064017007 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau1111)
  have hat2 :
    Real.arctan (187500000000000 / 2257183766004251 : ℝ) ≤
      (828778365856198504881 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 2257183766004251 : ℚ))
        (U := (828778365856198504881 / 10000000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (104343112775949 / 128000000000000 : ℚ))
      (lo := (2257183766004251 / 2500000000000000 : ℚ))
      (hi := (9028735064017007 / 10000000000000000 : ℚ))
      (s := (2257183766004251 / 2500000000000000 : ℚ))
      (r₁ := (232343112775949 / 128000000000000 : ℚ))
      (r₂ := (105063112775949 / 128000000000000 : ℚ))
      (z₁ := (10000000000000000 / 9028735064017007 : ℚ))
      (z₂ := (187500000000000 / 2257183766004251 : ℚ))
      (L := (5961849495794045218043 / 10000000000000000000000 : ℚ))
      (U := (-(1974690200181473962903 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_671 :
    ((3007824495396823922311 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1856099999143922723371 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1135349935516639 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (737370870709823805733 / 2000000000000000000000 : ℝ))) -
              6 * (82386750778903374503 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (2639911887007 / 3200000000000 : ℝ) := by
  have hL1 :
    (3007824495396823922311 / 5000000000000000000000 : ℝ) ≤
      Real.log (5839911887007 / 3200000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (5839911887007 / 3200000000000 : ℚ))
        (L := (3007824495396823922311 / 5000000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (2657911887007 / 3200000000000 : ℝ) ≤
      (-(1856099999143922723371 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2657911887007 / 3200000000000 : ℚ))
        (r' := (2657911887007 / 1600000000000 : ℚ))
        (U := (-(1856099999143922723371 / 10000000000000000000000 : ℚ)))
        (U' := (5075371803856077276629 / 10000000000000000000000 : ℚ))
        1 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau1114 :
    Real.arctan (139735376678971 / 361679294968710 : ℝ) ≤
      (737370870709823805733 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (139735376678971 / 361679294968710 : ℚ))
        (U := (737370870709823805733 / 2000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1113 :
    Real.arctan (1816559896826623 / 2000000000000000 : ℝ) ≤
      (2 * (737370870709823805733 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (270183083459323 / 200000000000000 : ℝ) ≤
          Real.sqrt (1 + (1816559896826623 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1816559896826623 / 2000000000000000 : ℝ) /
                (1 + (270183083459323 / 200000000000000 : ℝ)) =
              (139735376678971 / 361679294968710 : ℝ)
            by
        norm_num];
        exact hau1114)
  have hat1 :
    (Real.pi / 2 - (2 * (737370870709823805733 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1816559896826623 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1816559896826623 : ℝ) =
              (1816559896826623 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau1113)
  have hat2 :
    Real.arctan (93750000000000 / 1135349935516639 : ℝ) ≤
      (82386750778903374503 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (93750000000000 / 1135349935516639 : ℚ))
        (U := (82386750778903374503 / 1000000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2639911887007 / 3200000000000 : ℚ))
      (lo := (1135349935516639 / 1250000000000000 : ℚ))
      (hi := (1816559896826623 / 2000000000000000 : ℚ))
      (s := (1135349935516639 / 1250000000000000 : ℚ))
      (r₁ := (5839911887007 / 3200000000000 : ℚ))
      (r₂ := (2657911887007 / 3200000000000 : ℚ))
      (z₁ := (2000000000000000 / 1816559896826623 : ℚ))
      (z₂ := (93750000000000 / 1135349935516639 : ℚ))
      (L := (3007824495396823922311 / 5000000000000000000000 : ℚ))
      (U := (-(1856099999143922723371 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_672 :
    ((1517290148843070986257 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(434724923741976688371 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((9136543990028577 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (925384943603547055683 / 2500000000000000000000 : ℝ))) -
              6 * (409521462399309001603 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (106849838184611 / 128000000000000 : ℝ) := by
  have hL1 :
    (1517290148843070986257 / 2500000000000000000000 : ℝ) ≤
      Real.log (234849838184611 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (234849838184611 / 128000000000000 : ℚ))
        (L := (1517290148843070986257 / 2500000000000000000000 : ℚ))
        13 (by decide +kernel))
  have hU2 :
    Real.log (107569838184611 / 128000000000000 : ℝ) ≤
      (-(434724923741976688371 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (107569838184611 / 128000000000000 : ℚ))
        (r' := (107569838184611 / 64000000000000 : ℚ))
        (U := (-(434724923741976688371 / 2500000000000000000000 : ℚ)))
        (U' := (1298143027008023311629 / 2500000000000000000000 : ℚ))
        1 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau1116 :
    Real.arctan (761378665835715 / 1962112283010469 : ℝ) ≤
      (925384943603547055683 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (761378665835715 / 1962112283010469 : ℚ))
        (U := (925384943603547055683 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau1115 :
    Real.arctan (456827199501429 / 500000000000000 : ℝ) ≤
      (2 * (925384943603547055683 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3386336849031407 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (456827199501429 / 500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (456827199501429 / 500000000000000 : ℝ) /
                (1 + (3386336849031407 / 2500000000000000 : ℝ)) =
              (761378665835715 / 1962112283010469 : ℝ)
            by
        norm_num];
        exact hau1116)
  have hat1 :
    (Real.pi / 2 - (2 * (925384943603547055683 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (500000000000000 / 456827199501429 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 456827199501429 : ℝ) =
              (456827199501429 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau1115)
  have hat2 :
    Real.arctan (250000000000000 / 3045514663342859 : ℝ) ≤
      (409521462399309001603 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 3045514663342859 : ℚ))
        (U := (409521462399309001603 / 5000000000000000000000 : ℚ))
        3 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (106849838184611 / 128000000000000 : ℚ))
      (lo := (9136543990028577 / 10000000000000000 : ℚ))
      (hi := (456827199501429 / 500000000000000 : ℚ))
      (s := (9136543990028577 / 10000000000000000 : ℚ))
      (r₁ := (234849838184611 / 128000000000000 : ℚ))
      (r₂ := (107569838184611 / 128000000000000 : ℚ))
      (z₁ := (500000000000000 / 456827199501429 : ℚ))
      (z₂ := (250000000000000 / 3045514663342859 : ℚ))
      (L := (1517290148843070986257 / 2500000000000000000000 : ℚ))
      (U := (-(434724923741976688371 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
