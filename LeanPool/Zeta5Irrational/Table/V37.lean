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

/-! # V37: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma V_445 :
    ((765842864606636857627 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(234493277614459757331 / 312500000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6830540250086371 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2996310293174500557039 / 10000000000000000000000 : ℝ))) -
              6 * (546814399689969324883 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (933125602161 / 2000000000000 : ℝ) := by
  have hL1 :
    (765842864606636857627 / 2000000000000000000000 : ℝ) ≤
      Real.log (2933125602161 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2933125602161 / 2000000000000 : ℚ))
        (L := (765842864606636857627 / 2000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (944375602161 / 2000000000000 : ℝ) ≤
      (-(234493277614459757331 / 312500000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (944375602161 / 2000000000000 : ℚ))
        (r' := (944375602161 / 500000000000 : ℚ))
        (U := (-(234493277614459757331 / 312500000000000000000 : ℚ)))
        (U' := (198723710073040242669 / 312500000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau662 :
    Real.arctan (3415270125043187 / 11055086293936074 : ℝ) ≤
      (2996310293174500557039 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3415270125043187 / 11055086293936074 : ℚ))
        (U := (2996310293174500557039 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau661 :
    Real.arctan (3415270125043187 / 5000000000000000 : ℝ) ≤
      (2 * (2996310293174500557039 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3027543146968037 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (3415270125043187 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3415270125043187 / 5000000000000000 : ℝ) /
                (1 + (3027543146968037 / 2500000000000000 : ℝ)) =
              (3415270125043187 / 11055086293936074 : ℝ)
            by
        norm_num];
        exact hau662)
  have hat1 :
    (Real.pi / 2 - (2 * (2996310293174500557039 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3415270125043187 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3415270125043187 : ℝ) =
              (3415270125043187 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau661)
  have hat2 :
    Real.arctan (750000000000000 / 6830540250086371 : ℝ) ≤
      (546814399689969324883 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 6830540250086371 : ℚ))
        (U := (546814399689969324883 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (933125602161 / 2000000000000 : ℚ))
      (lo := (6830540250086371 / 10000000000000000 : ℚ))
      (hi := (3415270125043187 / 5000000000000000 : ℚ))
      (s := (6830540250086371 / 10000000000000000 : ℚ))
      (r₁ := (2933125602161 / 2000000000000 : ℚ))
      (r₂ := (944375602161 / 2000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3415270125043187 : ℚ))
      (z₂ := (750000000000000 / 6830540250086371 : ℚ))
      (L := (765842864606636857627 / 2000000000000000000000 : ℚ))
      (U := (-(234493277614459757331 / 312500000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_446 :
    ((3838240205298106251957 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(747577809759293719037 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1710056835599697 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (599922291000491826411 / 2000000000000000000000 : ℝ))) -
              6 * (218418460430541568817 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (467887100957 / 1000000000000 : ℝ) := by
  have hL1 :
    (3838240205298106251957 / 10000000000000000000000 : ℝ) ≤
      Real.log (1467887100957 / 1000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1467887100957 / 1000000000000 : ℚ))
        (L := (3838240205298106251957 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (473512100957 / 1000000000000 : ℝ) ≤
      (-(747577809759293719037 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (473512100957 / 1000000000000 : ℚ))
        (r' := (473512100957 / 250000000000 : ℚ))
        (U := (-(747577809759293719037 / 1000000000000000000000 : ℚ)))
        (U' := (638716550840706280963 / 1000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau664 :
    Real.arctan (207279616436327 / 670170880935590 : ℝ) ≤
      (599922291000491826411 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (207279616436327 / 670170880935590 : ℚ))
        (U := (599922291000491826411 / 2000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau663 :
    Real.arctan (6840227342398791 / 10000000000000000 : ℝ) ≤
      (2 * (599922291000491826411 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1211563907087447 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6840227342398791 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6840227342398791 / 10000000000000000 : ℝ) /
                (1 + (1211563907087447 / 1000000000000000 : ℝ)) =
              (207279616436327 / 670170880935590 : ℝ)
            by
        norm_num];
        exact hau664)
  have hat1 :
    (Real.pi / 2 - (2 * (599922291000491826411 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6840227342398791 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6840227342398791 : ℝ) =
              (6840227342398791 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau663)
  have hat2 :
    Real.arctan (62500000000000 / 570018945199899 : ℝ) ≤
      (218418460430541568817 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (62500000000000 / 570018945199899 : ℚ))
        (U := (218418460430541568817 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (467887100957 / 1000000000000 : ℚ))
      (lo := (1710056835599697 / 2500000000000000 : ℚ))
      (hi := (6840227342398791 / 10000000000000000 : ℚ))
      (s := (1710056835599697 / 2500000000000000 : ℚ))
      (r₁ := (1467887100957 / 1000000000000 : ℚ))
      (r₂ := (473512100957 / 1000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6840227342398791 : ℚ))
      (z₂ := (62500000000000 / 570018945199899 : ℚ))
      (L := (3838240205298106251957 / 10000000000000000000000 : ℚ))
      (U := (-(747577809759293719037 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_447 :
    ((240453621765865922073 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7447849530514487331947 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1369980147058343 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (750726243913883062749 / 2500000000000000000000 : ℝ))) -
              6 * (218112452596585238241 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (938422801667 / 2000000000000 : ℝ) := by
  have hL1 :
    (240453621765865922073 / 625000000000000000000 : ℝ) ≤
      Real.log (2938422801667 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2938422801667 / 2000000000000 : ℚ))
        (L := (240453621765865922073 / 625000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (949672801667 / 2000000000000 : ℝ) ≤
      (-(7447849530514487331947 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (949672801667 / 2000000000000 : ℚ))
        (r' := (949672801667 / 500000000000 : ℚ))
        (U := (-(7447849530514487331947 / 10000000000000000000000 : ℚ)))
        (U' := (6415094075485512668053 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau666 :
    Real.arctan (3424950367645859 / 11060551544276931 : ℝ) ≤
      (750726243913883062749 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3424950367645859 / 11060551544276931 : ℚ))
        (U := (750726243913883062749 / 2500000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau665 :
    Real.arctan (3424950367645859 / 5000000000000000 : ℝ) ≤
      (2 * (750726243913883062749 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6060551544276931 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3424950367645859 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3424950367645859 / 5000000000000000 : ℝ) /
                (1 + (6060551544276931 / 5000000000000000 : ℝ)) =
              (3424950367645859 / 11060551544276931 : ℝ)
            by
        norm_num];
        exact hau666)
  have hat1 :
    (Real.pi / 2 - (2 * (750726243913883062749 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3424950367645859 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3424950367645859 : ℝ) =
              (3424950367645859 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau665)
  have hat2 :
    Real.arctan (150000000000000 / 1369980147058343 : ℝ) ≤
      (218112452596585238241 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 1369980147058343 : ℚ))
        (U := (218112452596585238241 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (938422801667 / 2000000000000 : ℚ))
      (lo := (1369980147058343 / 2000000000000000 : ℚ))
      (hi := (3424950367645859 / 5000000000000000 : ℚ))
      (s := (1369980147058343 / 2000000000000000 : ℚ))
      (r₁ := (2938422801667 / 2000000000000 : ℚ))
      (r₂ := (949672801667 / 2000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3424950367645859 : ℚ))
      (z₂ := (150000000000000 / 1369980147058343 : ℚ))
      (L := (240453621765865922073 / 625000000000000000000 : ℚ))
      (U := (-(7447849530514487331947 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_448 :
    ((3856267566566845575453 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1854999686683688517279 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3429780243361081 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1503095444308757277833 / 5000000000000000000000 : ℝ))) -
              6 * (217807727351321952453 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (47053570071 / 100000000000 : ℝ) := by
  have hL1 :
    (3856267566566845575453 / 10000000000000000000000 : ℝ) ≤
      Real.log (147053570071 / 100000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (147053570071 / 100000000000 : ℚ))
        (L := (3856267566566845575453 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (47616070071 / 100000000000 : ℝ) ≤
      (-(1854999686683688517279 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47616070071 / 100000000000 : ℚ))
        (r' := (47616070071 / 25000000000 : ℚ))
        (U := (-(1854999686683688517279 / 2500000000000000000000 : ℚ)))
        (U' := (1610736214816311482721 / 2500000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau668 :
    Real.arctan (1371912097344433 / 4425312928848564 : ℝ) ≤
      (1503095444308757277833 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1371912097344433 / 4425312928848564 : ℚ))
        (U := (1503095444308757277833 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau667 :
    Real.arctan (1371912097344433 / 2000000000000000 : ℝ) ≤
      (2 * (1503095444308757277833 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (606328232212141 / 500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1371912097344433 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1371912097344433 / 2000000000000000 : ℝ) /
                (1 + (606328232212141 / 500000000000000 : ℝ)) =
              (1371912097344433 / 4425312928848564 : ℝ)
            by
        norm_num];
        exact hau668)
  have hat1 :
    (Real.pi / 2 - (2 * (1503095444308757277833 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1371912097344433 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1371912097344433 : ℝ) =
              (1371912097344433 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau667)
  have hat2 :
    Real.arctan (375000000000000 / 3429780243361081 : ℝ) ≤
      (217807727351321952453 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 3429780243361081 : ℚ))
        (U := (217807727351321952453 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (47053570071 / 100000000000 : ℚ))
      (lo := (3429780243361081 / 5000000000000000 : ℚ))
      (hi := (1371912097344433 / 2000000000000000 : ℚ))
      (s := (3429780243361081 / 5000000000000000 : ℚ))
      (r₁ := (147053570071 / 100000000000 : ℚ))
      (r₂ := (47616070071 / 100000000000 : ℚ))
      (z₁ := (2000000000000000 / 1371912097344433 : ℚ))
      (z₂ := (375000000000000 / 3429780243361081 : ℚ))
      (L := (3856267566566845575453 / 10000000000000000000000 : ℚ))
      (U := (-(1854999686683688517279 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_449 :
    ((3865269074863888535449 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7392225314191339633631 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1717301663559907 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3009469227143283066133 / 10000000000000000000000 : ℝ))) -
              6 * (1087521378799764588307 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (943720001173 / 2000000000000 : ℝ) := by
  have hL1 :
    (3865269074863888535449 / 10000000000000000000000 : ℝ) ≤
      Real.log (2943720001173 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2943720001173 / 2000000000000 : ℚ))
        (L := (3865269074863888535449 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (954970001173 / 2000000000000 : ℝ) ≤
      (-(7392225314191339633631 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (954970001173 / 2000000000000 : ℚ))
        (r' := (954970001173 / 500000000000 : ℚ))
        (U := (-(7392225314191339633631 / 10000000000000000000000 : ℚ)))
        (U' := (6470718291808660366369 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau670 :
    Real.arctan (528400511864587 / 1702463364712795 : ℝ) ≤
      (3009469227143283066133 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (528400511864587 / 1702463364712795 : ℚ))
        (U := (3009469227143283066133 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau669 :
    Real.arctan (6869206654239631 / 10000000000000000 : ℝ) ≤
      (2 * (3009469227143283066133 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2426404748253267 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6869206654239631 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6869206654239631 / 10000000000000000 : ℝ) /
                (1 + (2426404748253267 / 2000000000000000 : ℝ)) =
              (528400511864587 / 1702463364712795 : ℝ)
            by
        norm_num];
        exact hau670)
  have hat1 :
    (Real.pi / 2 - (2 * (3009469227143283066133 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6869206654239631 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6869206654239631 : ℝ) =
              (6869206654239631 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau669)
  have hat2 :
    Real.arctan (187500000000000 / 1717301663559907 : ℝ) ≤
      (1087521378799764588307 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 1717301663559907 : ℚ))
        (U := (1087521378799764588307 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (943720001173 / 2000000000000 : ℚ))
      (lo := (1717301663559907 / 2500000000000000 : ℚ))
      (hi := (6869206654239631 / 10000000000000000 : ℚ))
      (s := (1717301663559907 / 2500000000000000 : ℚ))
      (r₁ := (2943720001173 / 2000000000000 : ℚ))
      (r₂ := (954970001173 / 2000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6869206654239631 : ℚ))
      (z₂ := (187500000000000 / 1717301663559907 : ℚ))
      (L := (3865269074863888535449 / 10000000000000000000000 : ℚ))
      (U := (-(7392225314191339633631 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_450 :
    ((3874262487732329959907 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7364528804411839307839 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3439419647495053 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (753185006065245064909 / 2500000000000000000000 : ℝ))) -
              6 * (1086010444872883962773 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (473184300463 / 1000000000000 : ℝ) := by
  have hL1 :
    (3874262487732329959907 / 10000000000000000000000 : ℝ) ≤
      Real.log (1473184300463 / 1000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1473184300463 / 1000000000000 : ℚ))
        (L := (3874262487732329959907 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (478809300463 / 1000000000000 : ℝ) ≤
      (-(7364528804411839307839 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (478809300463 / 1000000000000 : ℚ))
        (r' := (478809300463 / 250000000000 : ℚ))
        (U := (-(7364528804411839307839 / 10000000000000000000000 : ℚ)))
        (U' := (6498414801588160692161 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau672 :
    Real.arctan (6878839294990109 / 22137480382941922 : ℝ) ≤
      (753185006065245064909 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6878839294990109 / 22137480382941922 : ℚ))
        (U := (753185006065245064909 / 2500000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau671 :
    Real.arctan (6878839294990109 / 10000000000000000 : ℝ) ≤
      (2 * (753185006065245064909 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6068740191470961 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6878839294990109 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6878839294990109 / 10000000000000000 : ℝ) /
                (1 + (6068740191470961 / 5000000000000000 : ℝ)) =
              (6878839294990109 / 22137480382941922 : ℝ)
            by
        norm_num];
        exact hau672)
  have hat1 :
    (Real.pi / 2 - (2 * (753185006065245064909 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6878839294990109 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6878839294990109 : ℝ) =
              (6878839294990109 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau671)
  have hat2 :
    Real.arctan (375000000000000 / 3439419647495053 : ℝ) ≤
      (1086010444872883962773 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 3439419647495053 : ℚ))
        (U := (1086010444872883962773 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (473184300463 / 1000000000000 : ℚ))
      (lo := (3439419647495053 / 5000000000000000 : ℚ))
      (hi := (6878839294990109 / 10000000000000000 : ℚ))
      (s := (3439419647495053 / 5000000000000000 : ℚ))
      (r₁ := (1473184300463 / 1000000000000 : ℚ))
      (r₂ := (478809300463 / 1000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6878839294990109 : ℚ))
      (z₂ := (375000000000000 / 3439419647495053 : ℚ))
      (L := (3874262487732329959907 / 10000000000000000000000 : ℚ))
      (U := (-(7364528804411839307839 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_451 :
    ((776649563944038904551 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3668454396237089531377 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((215264327053751 / 312500000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (754000828193542139837 / 2500000000000000000000 : ℝ))) -
              6 * (54225289558276524857 / 500000000000000000000 : ℝ)))) ≤
      Vfield (949017200679 / 2000000000000 : ℝ) := by
  have hL1 :
    (776649563944038904551 / 2000000000000000000000 : ℝ) ≤
      Real.log (2949017200679 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2949017200679 / 2000000000000 : ℚ))
        (L := (776649563944038904551 / 2000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (960267200679 / 2000000000000 : ℝ) ≤
      (-(3668454396237089531377 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (960267200679 / 2000000000000 : ℚ))
        (r' := (960267200679 / 500000000000 : ℚ))
        (U := (-(3668454396237089531377 / 5000000000000000000000 : ℚ)))
        (U' := (3263017406762910468623 / 5000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau674 :
    Real.arctan (6888458465720035 / 22142934572579644 : ℝ) ≤
      (754000828193542139837 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6888458465720035 / 22142934572579644 : ℚ))
        (U := (754000828193542139837 / 2500000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau673 :
    Real.arctan (1377691693144007 / 2000000000000000 : ℝ) ≤
      (2 * (754000828193542139837 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3035733643144911 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1377691693144007 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1377691693144007 / 2000000000000000 : ℝ) /
                (1 + (3035733643144911 / 2500000000000000 : ℝ)) =
              (6888458465720035 / 22142934572579644 : ℝ)
            by
        norm_num];
        exact hau674)
  have hat1 :
    (Real.pi / 2 - (2 * (754000828193542139837 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1377691693144007 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1377691693144007 : ℝ) =
              (1377691693144007 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau673)
  have hat2 :
    Real.arctan (23437500000000 / 215264327053751 : ℝ) ≤
      (54225289558276524857 / 500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (23437500000000 / 215264327053751 : ℚ))
        (U := (54225289558276524857 / 500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (949017200679 / 2000000000000 : ℚ))
      (lo := (215264327053751 / 312500000000000 : ℚ))
      (hi := (1377691693144007 / 2000000000000000 : ℚ))
      (s := (215264327053751 / 312500000000000 : ℚ))
      (r₁ := (2949017200679 / 2000000000000 : ℚ))
      (r₂ := (960267200679 / 2000000000000 : ℚ))
      (z₁ := (2000000000000000 / 1377691693144007 : ℚ))
      (z₂ := (23437500000000 / 215264327053751 : ℚ))
      (L := (776649563944038904551 / 2000000000000000000000 : ℚ))
      (U := (-(3668454396237089531377 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_452 :
    ((7784450170672652891 / 20000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7309364856967499426647 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((862258027847523 / 1250000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3019259125263958673499 / 10000000000000000000000 : ℝ))) -
              6 * (270751843572750147929 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (59479112527 / 125000000000 : ℝ) := by
  have hL1 :
    (7784450170672652891 / 20000000000000000000 : ℝ) ≤
      Real.log (184479112527 / 125000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (184479112527 / 125000000000 : ℚ))
        (L := (7784450170672652891 / 20000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (60182237527 / 125000000000 : ℝ) ≤
      (-(7309364856967499426647 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (60182237527 / 125000000000 : ℚ))
        (r' := (60182237527 / 31250000000 : ℚ))
        (U := (-(7309364856967499426647 / 10000000000000000000000 : ℚ)))
        (U' := (6553578749032500573353 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau676 :
    Real.arctan (6898064222780187 / 22148386313482132 : ℝ) ≤
      (3019259125263958673499 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6898064222780187 / 22148386313482132 : ℚ))
        (U := (3019259125263958673499 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau675 :
    Real.arctan (6898064222780187 / 10000000000000000 : ℝ) ≤
      (2 * (3019259125263958673499 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3037096578370533 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (6898064222780187 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6898064222780187 / 10000000000000000 : ℝ) /
                (1 + (3037096578370533 / 2500000000000000 : ℝ)) =
              (6898064222780187 / 22148386313482132 : ℝ)
            by
        norm_num];
        exact hau676)
  have hat1 :
    (Real.pi / 2 - (2 * (3019259125263958673499 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6898064222780187 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6898064222780187 : ℝ) =
              (6898064222780187 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau675)
  have hat2 :
    Real.arctan (31250000000000 / 287419342615841 : ℝ) ≤
      (270751843572750147929 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (31250000000000 / 287419342615841 : ℚ))
        (U := (270751843572750147929 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (59479112527 / 125000000000 : ℚ))
      (lo := (862258027847523 / 1250000000000000 : ℚ))
      (hi := (6898064222780187 / 10000000000000000 : ℚ))
      (s := (862258027847523 / 1250000000000000 : ℚ))
      (r₁ := (184479112527 / 125000000000 : ℚ))
      (r₂ := (60182237527 / 125000000000 : ℚ))
      (z₁ := (10000000000000000 / 6898064222780187 : ℚ))
      (z₂ := (31250000000000 / 287419342615841 : ℚ))
      (L := (7784450170672652891 / 20000000000000000000 : ℚ))
      (U := (-(7309364856967499426647 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_453 :
    ((780238859810106012883 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7281896579953576581699 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1726914155532383 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (604501498818222252083 / 2000000000000000000000 : ℝ))) -
              6 * (216303030256213961533 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (190862880037 / 400000000000 : ℝ) := by
  have hL1 :
    (780238859810106012883 / 2000000000000000000000 : ℝ) ≤
      Real.log (590862880037 / 400000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (590862880037 / 400000000000 : ℚ))
        (L := (780238859810106012883 / 2000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (193112880037 / 400000000000 : ℝ) ≤
      (-(7281896579953576581699 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (193112880037 / 400000000000 : ℚ))
        (r' := (193112880037 / 100000000000 : ℚ))
        (U := (-(7281896579953576581699 / 10000000000000000000000 : ℚ)))
        (U' := (6581047026046423418301 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau678 :
    Real.arctan (6907656622129535 / 22153835608944609 : ℝ) ≤
      (604501498818222252083 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6907656622129535 / 22153835608944609 : ℚ))
        (U := (604501498818222252083 / 2000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau677 :
    Real.arctan (1381531324425907 / 2000000000000000 : ℝ) ≤
      (2 * (604501498818222252083 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12153835608944609 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1381531324425907 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1381531324425907 / 2000000000000000 : ℝ) /
                (1 + (12153835608944609 / 10000000000000000 : ℝ)) =
              (6907656622129535 / 22153835608944609 : ℝ)
            by
        norm_num];
        exact hau678)
  have hat1 :
    (Real.pi / 2 - (2 * (604501498818222252083 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1381531324425907 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1381531324425907 : ℝ) =
              (1381531324425907 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau677)
  have hat2 :
    Real.arctan (187500000000000 / 1726914155532383 : ℝ) ≤
      (216303030256213961533 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 1726914155532383 : ℚ))
        (U := (216303030256213961533 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (190862880037 / 400000000000 : ℚ))
      (lo := (1726914155532383 / 2500000000000000 : ℚ))
      (hi := (1381531324425907 / 2000000000000000 : ℚ))
      (s := (1726914155532383 / 2500000000000000 : ℚ))
      (r₁ := (590862880037 / 400000000000 : ℚ))
      (r₂ := (193112880037 / 400000000000 : ℚ))
      (z₁ := (2000000000000000 / 1381531324425907 : ℚ))
      (z₂ := (187500000000000 / 1726914155532383 : ℚ))
      (L := (780238859810106012883 / 2000000000000000000000 : ℚ))
      (U := (-(7281896579953576581699 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_454 :
    ((782031095058741953577 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1813625886732192964727 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6917235719339047 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3025748451398115421169 / 10000000000000000000000 : ℝ))) -
              6 * (33750908736900517841 / 312500000000000000000 : ℝ)))) ≤
      Vfield (478481499969 / 1000000000000 : ℝ) := by
  have hL1 :
    (782031095058741953577 / 2000000000000000000000 : ℝ) ≤
      Real.log (1478481499969 / 1000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1478481499969 / 1000000000000 : ℚ))
        (L := (782031095058741953577 / 2000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (484106499969 / 1000000000000 : ℝ) ≤
      (-(1813625886732192964727 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (484106499969 / 1000000000000 : ℚ))
        (r' := (484106499969 / 250000000000 : ℚ))
        (U := (-(1813625886732192964727 / 2500000000000000000000 : ℚ)))
        (U' := (1652110014767807035273 / 2500000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau680 :
    Real.arctan (988176531334150 / 3165611780322131 : ℝ) ≤
      (3025748451398115421169 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (988176531334150 / 3165611780322131 : ℚ))
        (U := (3025748451398115421169 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau679 :
    Real.arctan (138344714386781 / 200000000000000 : ℝ) ≤
      (2 * (3025748451398115421169 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12159282462254917 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (138344714386781 / 200000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (138344714386781 / 200000000000000 : ℝ) /
                (1 + (12159282462254917 / 10000000000000000 : ℝ)) =
              (988176531334150 / 3165611780322131 : ℝ)
            by
        norm_num];
        exact hau680)
  have hat1 :
    (Real.pi / 2 - (2 * (3025748451398115421169 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (200000000000000 / 138344714386781 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (200000000000000 / 138344714386781 : ℝ) =
              (138344714386781 / 200000000000000 : ℝ)
            by
        norm_num];
        exact hau679)
  have hat2 :
    Real.arctan (750000000000000 / 6917235719339047 : ℝ) ≤
      (33750908736900517841 / 312500000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 6917235719339047 : ℚ))
        (U := (33750908736900517841 / 312500000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (478481499969 / 1000000000000 : ℚ))
      (lo := (6917235719339047 / 10000000000000000 : ℚ))
      (hi := (138344714386781 / 200000000000000 : ℚ))
      (s := (6917235719339047 / 10000000000000000 : ℚ))
      (r₁ := (1478481499969 / 1000000000000 : ℚ))
      (r₂ := (484106499969 / 1000000000000 : ℚ))
      (z₁ := (200000000000000 / 138344714386781 : ℚ))
      (z₂ := (750000000000000 / 6917235719339047 : ℚ))
      (L := (782031095058741953577 / 2000000000000000000000 : ℚ))
      (U := (-(1813625886732192964727 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_455 :
    ((3919108628458009307323 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(451699084174156310643 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6926801569595449 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (757245507277809449937 / 2500000000000000000000 : ℝ))) -
              6 * (269637279260881504219 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (959611599691 / 2000000000000 : ℝ) := by
  have hL1 :
    (3919108628458009307323 / 10000000000000000000000 : ℝ) ≤
      Real.log (2959611599691 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2959611599691 / 2000000000000 : ℚ))
        (L := (3919108628458009307323 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (970861599691 / 2000000000000 : ℝ) ≤
      (-(451699084174156310643 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (970861599691 / 2000000000000 : ℚ))
        (r' := (970861599691 / 500000000000 : ℚ))
        (U := (-(451699084174156310643 / 625000000000000000000 : ℚ)))
        (U' := (414734891200843689357 / 625000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau682 :
    Real.arctan (1731700392398863 / 5541181719173383 : ℝ) ≤
      (757245507277809449937 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1731700392398863 / 5541181719173383 : ℚ))
        (U := (757245507277809449937 / 2500000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau681 :
    Real.arctan (1731700392398863 / 2500000000000000 : ℝ) ≤
      (2 * (757245507277809449937 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3041181719173383 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1731700392398863 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1731700392398863 / 2500000000000000 : ℝ) /
                (1 + (3041181719173383 / 2500000000000000 : ℝ)) =
              (1731700392398863 / 5541181719173383 : ℝ)
            by
        norm_num];
        exact hau682)
  have hat1 :
    (Real.pi / 2 - (2 * (757245507277809449937 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1731700392398863 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1731700392398863 : ℝ) =
              (1731700392398863 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau681)
  have hat2 :
    Real.arctan (750000000000000 / 6926801569595449 : ℝ) ≤
      (269637279260881504219 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 6926801569595449 : ℚ))
        (U := (269637279260881504219 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (959611599691 / 2000000000000 : ℚ))
      (lo := (6926801569595449 / 10000000000000000 : ℚ))
      (hi := (1731700392398863 / 2500000000000000 : ℚ))
      (s := (6926801569595449 / 10000000000000000 : ℚ))
      (r₁ := (2959611599691 / 2000000000000 : ℚ))
      (r₂ := (970861599691 / 2000000000000 : ℚ))
      (z₁ := (2500000000000000 / 1731700392398863 : ℚ))
      (z₂ := (750000000000000 / 6926801569595449 : ℚ))
      (L := (3919108628458009307323 / 10000000000000000000000 : ℚ))
      (U := (-(451699084174156310643 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_456 :
    ((245503360806059405313 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(7199941571780214482551 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1734088556926231 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (606441651788510147911 / 2000000000000000000000 : ℝ))) -
              6 * (538537610962834018837 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (240565049861 / 500000000000 : ℝ) := by
  have hL1 :
    (245503360806059405313 / 625000000000000000000 : ℝ) ≤
      Real.log (740565049861 / 500000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (740565049861 / 500000000000 : ℚ))
        (L := (245503360806059405313 / 625000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hU2 :
    Real.log (243377549861 / 500000000000 : ℝ) ≤
      (-(7199941571780214482551 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (243377549861 / 500000000000 : ℚ))
        (r' := (243377549861 / 125000000000 : ℚ))
        (U := (-(7199941571780214482551 / 10000000000000000000000 : ℚ)))
        (U' := (6663002034219785517449 / 10000000000000000000000 : ℚ))
        2 14 (by decide +kernel) (by constructor <;> norm_num)
  have hau684 :
    Real.arctan (6936354227704927 / 22170168855533598 : ℝ) ≤
      (606441651788510147911 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6936354227704927 / 22170168855533598 : ℚ))
        (U := (606441651788510147911 / 2000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hau683 :
    Real.arctan (6936354227704927 / 10000000000000000 : ℝ) ≤
      (2 * (606441651788510147911 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6085084427766799 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6936354227704927 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6936354227704927 / 10000000000000000 : ℝ) /
                (1 + (6085084427766799 / 5000000000000000 : ℝ)) =
              (6936354227704927 / 22170168855533598 : ℝ)
            by
        norm_num];
        exact hau684)
  have hat1 :
    (Real.pi / 2 - (2 * (606441651788510147911 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6936354227704927 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6936354227704927 : ℝ) =
              (6936354227704927 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau683)
  have hat2 :
    Real.arctan (187500000000000 / 1734088556926231 : ℝ) ≤
      (538537610962834018837 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 1734088556926231 : ℚ))
        (U := (538537610962834018837 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (240565049861 / 500000000000 : ℚ))
      (lo := (1734088556926231 / 2500000000000000 : ℚ))
      (hi := (6936354227704927 / 10000000000000000 : ℚ))
      (s := (1734088556926231 / 2500000000000000 : ℚ))
      (r₁ := (740565049861 / 500000000000 : ℚ))
      (r₂ := (243377549861 / 500000000000 : ℚ))
      (z₁ := (10000000000000000 / 6936354227704927 : ℚ))
      (z₂ := (187500000000000 / 1734088556926231 : ℚ))
      (L := (245503360806059405313 / 625000000000000000000 : ℚ))
      (U := (-(7199941571780214482551 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
