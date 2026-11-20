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

/-! # V27: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma V_325 :
    ((2602736867247839204543 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5971596284766294893433 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2726192802200519 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2495901233890856705717 / 10000000000000000000000 : ℝ))) -
              6 * (683483096073199743303 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (19026245618611 / 64000000000000 : ℝ) := by
  have hL1 :
    (2602736867247839204543 / 10000000000000000000000 : ℝ) ≤
      Real.log (83026245618611 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (83026245618611 / 64000000000000 : ℚ))
        (L := (2602736867247839204543 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (19386245618611 / 64000000000000 : ℝ) ≤
      (-(5971596284766294893433 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19386245618611 / 64000000000000 : ℚ))
        (r' := (19386245618611 / 16000000000000 : ℚ))
        (U := (-(5971596284766294893433 / 5000000000000000000000 : ℚ)))
        (U' := (959875518233705106567 / 5000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau422 :
    Real.arctan (5452385604401041 / 21389842350931802 : ℝ) ≤
      (2495901233890856705717 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5452385604401041 / 21389842350931802 : ℚ))
        (U := (2495901233890856705717 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau421 :
    Real.arctan (5452385604401041 / 10000000000000000 : ℝ) ≤
      (2 * (2495901233890856705717 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5694921175465901 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5452385604401041 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5452385604401041 / 10000000000000000 : ℝ) /
                (1 + (5694921175465901 / 5000000000000000 : ℝ)) =
              (5452385604401041 / 21389842350931802 : ℝ)
            by
        norm_num];
        exact hau422)
  have hat1 :
    (Real.pi / 2 - (2 * (2495901233890856705717 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5452385604401041 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5452385604401041 : ℝ) =
              (5452385604401041 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau421)
  have hat2 :
    Real.arctan (375000000000000 / 2726192802200519 : ℝ) ≤
      (683483096073199743303 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 2726192802200519 : ℚ))
        (U := (683483096073199743303 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (19026245618611 / 64000000000000 : ℚ))
      (lo := (2726192802200519 / 5000000000000000 : ℚ))
      (hi := (5452385604401041 / 10000000000000000 : ℚ))
      (s := (2726192802200519 / 5000000000000000 : ℚ))
      (r₁ := (83026245618611 / 64000000000000 : ℚ))
      (r₂ := (19386245618611 / 64000000000000 : ℚ))
      (z₁ := (10000000000000000 / 5452385604401041 : ℚ))
      (z₂ := (375000000000000 / 2726192802200519 : ℚ))
      (L := (2602736867247839204543 / 10000000000000000000000 : ℚ))
      (U := (-(5971596284766294893433 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_326 :
    ((651854409488761182881 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11923161429885025563023 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1364488135098277 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2498046341966979991561 / 10000000000000000000000 : ℝ))) -
              6 * (1365589208491496565637 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1525209391779 / 5120000000000 : ℝ) := by
  have hL1 :
    (651854409488761182881 / 2500000000000000000000 : ℝ) ≤
      Real.log (6645209391779 / 5120000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (6645209391779 / 5120000000000 : ℚ))
        (L := (651854409488761182881 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (1554009391779 / 5120000000000 : ℝ) ≤
      (-(11923161429885025563023 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1554009391779 / 5120000000000 : ℚ))
        (r' := (1554009391779 / 1280000000000 : ℚ))
        (U := (-(11923161429885025563023 / 10000000000000000000000 : ℚ)))
        (U' := (1939782176114974436977 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau424 :
    Real.arctan (5457952540393111 / 21392508324911752 : ℝ) ≤
      (2498046341966979991561 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5457952540393111 / 21392508324911752 : ℚ))
        (U := (2498046341966979991561 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau423 :
    Real.arctan (5457952540393111 / 10000000000000000 : ℝ) ≤
      (2 * (2498046341966979991561 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1424063540613969 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (5457952540393111 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5457952540393111 / 10000000000000000 : ℝ) /
                (1 + (1424063540613969 / 1250000000000000 : ℝ)) =
              (5457952540393111 / 21392508324911752 : ℝ)
            by
        norm_num];
        exact hau424)
  have hat1 :
    (Real.pi / 2 - (2 * (2498046341966979991561 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5457952540393111 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5457952540393111 : ℝ) =
              (5457952540393111 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau423)
  have hat2 :
    Real.arctan (187500000000000 / 1364488135098277 : ℝ) ≤
      (1365589208491496565637 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 1364488135098277 : ℚ))
        (U := (1365589208491496565637 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1525209391779 / 5120000000000 : ℚ))
      (lo := (1364488135098277 / 2500000000000000 : ℚ))
      (hi := (5457952540393111 / 10000000000000000 : ℚ))
      (s := (1364488135098277 / 2500000000000000 : ℚ))
      (r₁ := (6645209391779 / 5120000000000 : ℚ))
      (r₂ := (1554009391779 / 5120000000000 : ℚ))
      (z₁ := (10000000000000000 / 5457952540393111 : ℚ))
      (z₂ := (187500000000000 / 1364488135098277 : ℚ))
      (L := (651854409488761182881 / 2500000000000000000000 : ℚ))
      (U := (-(11923161429885025563023 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_327 :
    ((2612096218725827974741 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5951585167346387345697 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((27317569020361 / 50000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2500188261746333242647 / 10000000000000000000000 : ℝ))) -
              6 * (341054094455857365227 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (2387998646983 / 8000000000000 : ℝ) := by
  have hL1 :
    (2612096218725827974741 / 10000000000000000000000 : ℝ) ≤
      Real.log (10387998646983 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (10387998646983 / 8000000000000 : ℚ))
        (L := (2612096218725827974741 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (2432998646983 / 8000000000000 : ℝ) ≤
      (-(5951585167346387345697 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2432998646983 / 8000000000000 : ℚ))
        (r' := (2432998646983 / 2000000000000 : ℚ))
        (U := (-(5951585167346387345697 / 5000000000000000000000 : ℚ)))
        (U' := (979886635653612654303 / 5000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau426 :
    Real.arctan (5463513804072203 / 21395173675170005 : ℝ) ≤
      (2500188261746333242647 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5463513804072203 / 21395173675170005 : ℚ))
        (U := (2500188261746333242647 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau425 :
    Real.arctan (5463513804072203 / 10000000000000000 : ℝ) ≤
      (2 * (2500188261746333242647 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2279034735034001 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5463513804072203 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5463513804072203 / 10000000000000000 : ℝ) /
                (1 + (2279034735034001 / 2000000000000000 : ℝ)) =
              (5463513804072203 / 21395173675170005 : ℝ)
            by
        norm_num];
        exact hau426)
  have hat1 :
    (Real.pi / 2 - (2 * (2500188261746333242647 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5463513804072203 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5463513804072203 : ℝ) =
              (5463513804072203 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau425)
  have hat2 :
    Real.arctan (3750000000000 / 27317569020361 : ℝ) ≤
      (341054094455857365227 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3750000000000 / 27317569020361 : ℚ))
        (U := (341054094455857365227 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2387998646983 / 8000000000000 : ℚ))
      (lo := (27317569020361 / 50000000000000 : ℚ))
      (hi := (5463513804072203 / 10000000000000000 : ℚ))
      (s := (27317569020361 / 50000000000000 : ℚ))
      (r₁ := (10387998646983 / 8000000000000 : ℚ))
      (r₂ := (2432998646983 / 8000000000000 : ℚ))
      (z₁ := (10000000000000000 / 5463513804072203 : ℚ))
      (z₂ := (3750000000000 / 27317569020361 : ℚ))
      (L := (2612096218725827974741 / 10000000000000000000000 : ℚ))
      (U := (-(5951585167346387345697 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_328 :
    ((2616772611608389628563 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11883219124168659191989 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1367267353185529 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2502327002872303514111 / 10000000000000000000000 : ℝ))) -
              6 * (681423839653867688303 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (38285721908981 / 128000000000000 : ℝ) := by
  have hL1 :
    (2616772611608389628563 / 10000000000000000000000 : ℝ) ≤
      Real.log (166285721908981 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (166285721908981 / 128000000000000 : ℚ))
        (L := (2616772611608389628563 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (39005721908981 / 128000000000000 : ℝ) ≤
      (-(11883219124168659191989 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (39005721908981 / 128000000000000 : ℚ))
        (r' := (39005721908981 / 32000000000000 : ℚ))
        (U := (-(11883219124168659191989 / 10000000000000000000000 : ℚ)))
        (U' := (1979724481831340808011 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau428 :
    Real.arctan (5469069412742119 / 21397838402144127 : ℝ) ≤
      (2502327002872303514111 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5469069412742119 / 21397838402144127 : ℚ))
        (U := (2502327002872303514111 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau427 :
    Real.arctan (5469069412742119 / 10000000000000000 : ℝ) ≤
      (2 * (2502327002872303514111 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11397838402144127 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5469069412742119 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5469069412742119 / 10000000000000000 : ℝ) /
                (1 + (11397838402144127 / 10000000000000000 : ℝ)) =
              (5469069412742119 / 21397838402144127 : ℝ)
            by
        norm_num];
        exact hau428)
  have hat1 :
    (Real.pi / 2 - (2 * (2502327002872303514111 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5469069412742119 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5469069412742119 : ℝ) =
              (5469069412742119 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau427)
  have hat2 :
    Real.arctan (187500000000000 / 1367267353185529 : ℝ) ≤
      (681423839653867688303 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 1367267353185529 : ℚ))
        (U := (681423839653867688303 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (38285721908981 / 128000000000000 : ℚ))
      (lo := (1367267353185529 / 2500000000000000 : ℚ))
      (hi := (5469069412742119 / 10000000000000000 : ℚ))
      (s := (1367267353185529 / 2500000000000000 : ℚ))
      (r₁ := (166285721908981 / 128000000000000 : ℚ))
      (r₂ := (39005721908981 / 128000000000000 : ℚ))
      (z₁ := (10000000000000000 / 5469069412742119 : ℚ))
      (z₂ := (187500000000000 / 1367267353185529 : ℚ))
      (L := (2616772611608389628563 / 10000000000000000000000 : ℚ))
      (U := (-(11883219124168659191989 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_329 :
    ((262144681864805827297 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11863307639479982018991 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1094923876723771 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1252231287470484669311 / 5000000000000000000000 : ℝ))) -
              6 * (340370773063998395589 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (19181732733117 / 64000000000000 : ℝ) := by
  have hL1 :
    (262144681864805827297 / 1000000000000000000000 : ℝ) ≤
      Real.log (83181732733117 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (83181732733117 / 64000000000000 : ℚ))
        (L := (262144681864805827297 / 1000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (19541732733117 / 64000000000000 : ℝ) ≤
      (-(11863307639479982018991 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19541732733117 / 64000000000000 : ℚ))
        (r' := (19541732733117 / 16000000000000 : ℚ))
        (U := (-(11863307639479982018991 / 10000000000000000000000 : ℚ)))
        (U' := (1999635966520017981009 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau430 :
    Real.arctan (5474619383618858 / 21400502506271173 : ℝ) ≤
      (1252231287470484669311 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5474619383618858 / 21400502506271173 : ℚ))
        (U := (1252231287470484669311 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau429 :
    Real.arctan (2737309691809429 / 5000000000000000 : ℝ) ≤
      (2 * (1252231287470484669311 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11400502506271173 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2737309691809429 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2737309691809429 / 5000000000000000 : ℝ) /
                (1 + (11400502506271173 / 10000000000000000 : ℝ)) =
              (5474619383618858 / 21400502506271173 : ℝ)
            by
        norm_num];
        exact hau430)
  have hat1 :
    (Real.pi / 2 - (2 * (1252231287470484669311 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2737309691809429 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2737309691809429 : ℝ) =
              (2737309691809429 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau429)
  have hat2 :
    Real.arctan (150000000000000 / 1094923876723771 : ℝ) ≤
      (340370773063998395589 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 1094923876723771 : ℚ))
        (U := (340370773063998395589 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (19181732733117 / 64000000000000 : ℚ))
      (lo := (1094923876723771 / 2000000000000000 : ℚ))
      (hi := (2737309691809429 / 5000000000000000 : ℚ))
      (s := (1094923876723771 / 2000000000000000 : ℚ))
      (r₁ := (83181732733117 / 64000000000000 : ℚ))
      (r₂ := (19541732733117 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 2737309691809429 : ℚ))
      (z₂ := (150000000000000 / 1094923876723771 : ℚ))
      (L := (262144681864805827297 / 1000000000000000000000 : ℚ))
      (U := (-(11863307639479982018991 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_330 :
    ((525223768377459148197 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11843435722740940104459 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1370040933457811 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1253297493750716190239 / 5000000000000000000000 : ℝ))) -
              6 * (272024519224901943929 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (38441209023487 / 128000000000000 : ℝ) := by
  have hL1 :
    (525223768377459148197 / 2000000000000000000000 : ℝ) ≤
      Real.log (166441209023487 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (166441209023487 / 128000000000000 : ℚ))
        (L := (525223768377459148197 / 2000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (39161209023487 / 128000000000000 : ℝ) ≤
      (-(11843435722740940104459 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (39161209023487 / 128000000000000 : ℚ))
        (r' := (39161209023487 / 32000000000000 : ℚ))
        (U := (-(11843435722740940104459 / 10000000000000000000000 : ℚ)))
        (U' := (2019507883259059895541 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau432 :
    Real.arctan (5480163733831247 / 21403165987987687 : ℝ) ≤
      (1253297493750716190239 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5480163733831247 / 21403165987987687 : ℚ))
        (U := (1253297493750716190239 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau431 :
    Real.arctan (5480163733831247 / 10000000000000000 : ℝ) ≤
      (2 * (1253297493750716190239 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11403165987987687 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5480163733831247 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5480163733831247 / 10000000000000000 : ℝ) /
                (1 + (11403165987987687 / 10000000000000000 : ℝ)) =
              (5480163733831247 / 21403165987987687 : ℝ)
            by
        norm_num];
        exact hau432)
  have hat1 :
    (Real.pi / 2 - (2 * (1253297493750716190239 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5480163733831247 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5480163733831247 : ℝ) =
              (5480163733831247 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau431)
  have hat2 :
    Real.arctan (187500000000000 / 1370040933457811 : ℝ) ≤
      (272024519224901943929 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 1370040933457811 : ℚ))
        (U := (272024519224901943929 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (38441209023487 / 128000000000000 : ℚ))
      (lo := (1370040933457811 / 2500000000000000 : ℚ))
      (hi := (5480163733831247 / 10000000000000000 : ℚ))
      (s := (1370040933457811 / 2500000000000000 : ℚ))
      (r₁ := (166441209023487 / 128000000000000 : ℚ))
      (r₂ := (39161209023487 / 128000000000000 : ℚ))
      (z₁ := (10000000000000000 / 5480163733831247 : ℚ))
      (z₂ := (187500000000000 / 1370040933457811 : ℚ))
      (L := (525223768377459148197 / 2000000000000000000000 : ℚ))
      (U := (-(11843435722740940104459 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_331 :
    ((2630788683365702473583 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(11823603217005112636329 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5485702480421547 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2508724250056138755739 / 10000000000000000000000 : ℝ))) -
              6 * (135876617051301854297 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (1925947629037 / 6400000000000 : ℝ) := by
  have hL1 :
    (2630788683365702473583 / 10000000000000000000000 : ℝ) ≤
      Real.log (8325947629037 / 6400000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (8325947629037 / 6400000000000 : ℚ))
        (L := (2630788683365702473583 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (1961947629037 / 6400000000000 : ℝ) ≤
      (-(11823603217005112636329 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1961947629037 / 6400000000000 : ℚ))
        (r' := (1961947629037 / 1600000000000 : ℚ))
        (U := (-(11823603217005112636329 / 10000000000000000000000 : ℚ)))
        (U' := (2039340388994887363671 / 10000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau434 :
    Real.arctan (914283746736925 / 3567638141288284 : ℝ) ≤
      (2508724250056138755739 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (914283746736925 / 3567638141288284 : ℚ))
        (U := (2508724250056138755739 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau433 :
    Real.arctan (109714049608431 / 200000000000000 : ℝ) ≤
      (2 * (2508724250056138755739 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1425728605966213 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (109714049608431 / 200000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (109714049608431 / 200000000000000 : ℝ) /
                (1 + (1425728605966213 / 1250000000000000 : ℝ)) =
              (914283746736925 / 3567638141288284 : ℝ)
            by
        norm_num];
        exact hau434)
  have hat1 :
    (Real.pi / 2 - (2 * (2508724250056138755739 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (200000000000000 / 109714049608431 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (200000000000000 / 109714049608431 : ℝ) =
              (109714049608431 / 200000000000000 : ℝ)
            by
        norm_num];
        exact hau433)
  have hat2 :
    Real.arctan (250000000000000 / 1828567493473849 : ℝ) ≤
      (135876617051301854297 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1828567493473849 : ℚ))
        (U := (135876617051301854297 / 1000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1925947629037 / 6400000000000 : ℚ))
      (lo := (5485702480421547 / 10000000000000000 : ℚ))
      (hi := (109714049608431 / 200000000000000 : ℚ))
      (s := (5485702480421547 / 10000000000000000 : ℚ))
      (r₁ := (8325947629037 / 6400000000000 : ℚ))
      (r₂ := (1961947629037 / 6400000000000 : ℚ))
      (z₁ := (200000000000000 / 109714049608431 : ℚ))
      (z₂ := (250000000000000 / 1828567493473849 : ℚ))
      (L := (2630788683365702473583 / 10000000000000000000000 : ℚ))
      (U := (-(11823603217005112636329 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_332 :
    ((66003045729603764453 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(736503488463111140191 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1099352646095163 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (314121670365840661703 / 1250000000000000000000 : ℝ))) -
              6 * (678032724979199444369 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (19337219847623 / 64000000000000 : ℝ) := by
  have hL1 :
    (66003045729603764453 / 250000000000000000000 : ℝ) ≤
      Real.log (83337219847623 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (83337219847623 / 64000000000000 : ℚ))
        (L := (66003045729603764453 / 250000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (19697219847623 / 64000000000000 : ℝ) ≤
      (-(736503488463111140191 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19697219847623 / 64000000000000 : ℚ))
        (r' := (19697219847623 / 16000000000000 : ℚ))
        (U := (-(736503488463111140191 / 625000000000000000000 : ℚ)))
        (U' := (129930486911888859809 / 625000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau436 :
    Real.arctan (916127205079303 / 3568525450505307 : ℝ) ≤
      (314121670365840661703 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (916127205079303 / 3568525450505307 : ℚ))
        (U := (314121670365840661703 / 1250000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau435 :
    Real.arctan (2748381615237909 / 5000000000000000 : ℝ) ≤
      (2 * (314121670365840661703 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5705576351515921 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2748381615237909 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2748381615237909 / 5000000000000000 : ℝ) /
                (1 + (5705576351515921 / 5000000000000000 : ℝ)) =
              (916127205079303 / 3568525450505307 : ℝ)
            by
        norm_num];
        exact hau436)
  have hat1 :
    (Real.pi / 2 - (2 * (314121670365840661703 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2748381615237909 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2748381615237909 : ℝ) =
              (2748381615237909 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau435)
  have hat2 :
    Real.arctan (50000000000000 / 366450882031721 : ℝ) ≤
      (678032724979199444369 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (50000000000000 / 366450882031721 : ℚ))
        (U := (678032724979199444369 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (19337219847623 / 64000000000000 : ℚ))
      (lo := (1099352646095163 / 2000000000000000 : ℚ))
      (hi := (2748381615237909 / 5000000000000000 : ℚ))
      (s := (1099352646095163 / 2000000000000000 : ℚ))
      (r₁ := (83337219847623 / 64000000000000 : ℚ))
      (r₂ := (19697219847623 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 2748381615237909 : ℚ))
      (z₂ := (50000000000000 / 366450882031721 : ℚ))
      (L := (66003045729603764453 / 250000000000000000000 : ℚ))
      (U := (-(736503488463111140191 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_333 :
    ((2649446272363180973399 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2348932839525893305633 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5507801768411671 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1258604994325691642003 / 5000000000000000000000 : ℝ))) -
              6 * (270676154042019708727 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (4853740851219 / 16000000000000 : ℝ) := by
  have hL1 :
    (2649446272363180973399 / 10000000000000000000000 : ℝ) ≤
      Real.log (20853740851219 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (20853740851219 / 16000000000000 : ℚ))
        (L := (2649446272363180973399 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (4943740851219 / 16000000000000 : ℝ) ≤
      (-(2348932839525893305633 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4943740851219 / 16000000000000 : ℚ))
        (r' := (4943740851219 / 4000000000000 : ℚ))
        (U := (-(2348932839525893305633 / 2000000000000000000000 : ℚ)))
        (U' := (423655881674106694367 / 2000000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau438 :
    Real.arctan (5507801768411674 / 21416474075655703 : ℝ) ≤
      (1258604994325691642003 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5507801768411674 / 21416474075655703 : ℚ))
        (U := (1258604994325691642003 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau437 :
    Real.arctan (2753900884205837 / 5000000000000000 : ℝ) ≤
      (2 * (1258604994325691642003 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11416474075655703 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2753900884205837 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2753900884205837 / 5000000000000000 : ℝ) /
                (1 + (11416474075655703 / 10000000000000000 : ℝ)) =
              (5507801768411674 / 21416474075655703 : ℝ)
            by
        norm_num];
        exact hau438)
  have hat1 :
    (Real.pi / 2 - (2 * (1258604994325691642003 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2753900884205837 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2753900884205837 : ℝ) =
              (2753900884205837 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau437)
  have hat2 :
    Real.arctan (750000000000000 / 5507801768411671 : ℝ) ≤
      (270676154042019708727 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 5507801768411671 : ℚ))
        (U := (270676154042019708727 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4853740851219 / 16000000000000 : ℚ))
      (lo := (5507801768411671 / 10000000000000000 : ℚ))
      (hi := (2753900884205837 / 5000000000000000 : ℚ))
      (s := (5507801768411671 / 10000000000000000 : ℚ))
      (r₁ := (20853740851219 / 16000000000000 : ℚ))
      (r₂ := (4943740851219 / 16000000000000 : ℚ))
      (z₁ := (5000000000000000 / 2753900884205837 : ℚ))
      (z₂ := (750000000000000 / 5507801768411671 : ℚ))
      (L := (2649446272363180973399 / 10000000000000000000000 : ℚ))
      (U := (-(2348932839525893305633 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_334 :
    ((166172626819820649641 / 625000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2926356785290338176897 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5518818227512711 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2521434201602609004749 / 10000000000000000000000 : ℝ))) -
              6 * (1350711973100143615783 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (19492706962129 / 64000000000000 : ℝ) := by
  have hL1 :
    (166172626819820649641 / 625000000000000000000 : ℝ) ≤
      Real.log (83492706962129 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (83492706962129 / 64000000000000 : ℚ))
        (L := (166172626819820649641 / 625000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (19852706962129 / 64000000000000 : ℝ) ≤
      (-(2926356785290338176897 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (19852706962129 / 64000000000000 : ℚ))
        (r' := (19852706962129 / 16000000000000 : ℚ))
        (U := (-(2926356785290338176897 / 2500000000000000000000 : ℚ)))
        (U' := (539379116209661823103 / 2500000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau440 :
    Real.arctan (2759409113756357 / 10710896484535649 : ℝ) ≤
      (2521434201602609004749 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2759409113756357 / 10710896484535649 : ℚ))
        (U := (2521434201602609004749 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau439 :
    Real.arctan (2759409113756357 / 5000000000000000 : ℝ) ≤
      (2 * (2521434201602609004749 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5710896484535649 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (2759409113756357 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (2759409113756357 / 5000000000000000 : ℝ) /
                (1 + (5710896484535649 / 5000000000000000 : ℝ)) =
              (2759409113756357 / 10710896484535649 : ℝ)
            by
        norm_num];
        exact hau440)
  have hat1 :
    (Real.pi / 2 - (2 * (2521434201602609004749 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 2759409113756357 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 2759409113756357 : ℝ) =
              (2759409113756357 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau439)
  have hat2 :
    Real.arctan (750000000000000 / 5518818227512711 : ℝ) ≤
      (1350711973100143615783 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 5518818227512711 : ℚ))
        (U := (1350711973100143615783 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (19492706962129 / 64000000000000 : ℚ))
      (lo := (5518818227512711 / 10000000000000000 : ℚ))
      (hi := (2759409113756357 / 5000000000000000 : ℚ))
      (s := (5518818227512711 / 10000000000000000 : ℚ))
      (r₁ := (83492706962129 / 64000000000000 : ℚ))
      (r₂ := (19852706962129 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 2759409113756357 : ℚ))
      (z₂ := (750000000000000 / 5518818227512711 : ℚ))
      (L := (166172626819820649641 / 625000000000000000000 : ℚ))
      (U := (-(2926356785290338176897 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_335 :
    ((533613823123012619069 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(729146464864790530219 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((345613296233431 / 625000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1262823037718319180193 / 5000000000000000000000 : ℝ))) -
              6 * (337014725658869163649 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (9785225259691 / 32000000000000 : ℝ) := by
  have hL1 :
    (533613823123012619069 / 2000000000000000000000 : ℝ) ≤
      Real.log (41785225259691 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (41785225259691 / 32000000000000 : ℚ))
        (L := (533613823123012619069 / 2000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (9965225259691 / 32000000000000 : ℝ) ≤
      (-(729146464864790530219 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9965225259691 / 32000000000000 : ℚ))
        (r' := (9965225259691 / 8000000000000 : ℚ))
        (U := (-(729146464864790530219 / 625000000000000000000 : ℚ)))
        (U' := (137287510510209469781 / 625000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau442 :
    Real.arctan (5529812739734899 / 21427109386740566 : ℝ) ≤
      (1262823037718319180193 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5529812739734899 / 21427109386740566 : ℚ))
        (U := (1262823037718319180193 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau441 :
    Real.arctan (5529812739734899 / 10000000000000000 : ℝ) ≤
      (2 * (1262823037718319180193 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5713554693370283 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5529812739734899 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5529812739734899 / 10000000000000000 : ℝ) /
                (1 + (5713554693370283 / 5000000000000000 : ℝ)) =
              (5529812739734899 / 21427109386740566 : ℝ)
            by
        norm_num];
        exact hau442)
  have hat1 :
    (Real.pi / 2 - (2 * (1262823037718319180193 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5529812739734899 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5529812739734899 : ℝ) =
              (5529812739734899 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau441)
  have hat2 :
    Real.arctan (46875000000000 / 345613296233431 : ℝ) ≤
      (337014725658869163649 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (46875000000000 / 345613296233431 : ℚ))
        (U := (337014725658869163649 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (9785225259691 / 32000000000000 : ℚ))
      (lo := (345613296233431 / 625000000000000 : ℚ))
      (hi := (5529812739734899 / 10000000000000000 : ℚ))
      (s := (345613296233431 / 625000000000000 : ℚ))
      (r₁ := (41785225259691 / 32000000000000 : ℚ))
      (r₂ := (9965225259691 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 5529812739734899 : ℚ))
      (z₂ := (46875000000000 / 345613296233431 : ℚ))
      (L := (533613823123012619069 / 2000000000000000000000 : ℚ))
      (U := (-(729146464864790530219 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_336 :
    ((1338683773990469618213 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2906852973399345608809 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((554078543572499 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1264922841551584207157 / 5000000000000000000000 : ℝ))) -
              6 * (672710702479827681713 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (3929638815327 / 12800000000000 : ℝ) := by
  have hL1 :
    (1338683773990469618213 / 5000000000000000000000 : ℝ) ≤
      Real.log (16729638815327 / 12800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (16729638815327 / 12800000000000 : ℚ))
        (L := (1338683773990469618213 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (4001638815327 / 12800000000000 : ℝ) ≤
      (-(2906852973399345608809 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4001638815327 / 12800000000000 : ℚ))
        (r' := (4001638815327 / 3200000000000 : ℚ))
        (U := (-(2906852973399345608809 / 2500000000000000000000 : ℚ)))
        (U' := (558882928100654391191 / 2500000000000000000000 : ℚ))
        2 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau444 :
    Real.arctan (5540785435724993 / 21432423332117393 : ℝ) ≤
      (1264922841551584207157 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5540785435724993 / 21432423332117393 : ℚ))
        (U := (1264922841551584207157 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau443 :
    Real.arctan (5540785435724993 / 10000000000000000 : ℝ) ≤
      (2 * (1264922841551584207157 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11432423332117393 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5540785435724993 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5540785435724993 / 10000000000000000 : ℝ) /
                (1 + (11432423332117393 / 10000000000000000 : ℝ)) =
              (5540785435724993 / 21432423332117393 : ℝ)
            by
        norm_num];
        exact hau444)
  have hat1 :
    (Real.pi / 2 - (2 * (1264922841551584207157 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5540785435724993 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5540785435724993 : ℝ) =
              (5540785435724993 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau443)
  have hat2 :
    Real.arctan (75000000000000 / 554078543572499 : ℝ) ≤
      (672710702479827681713 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (75000000000000 / 554078543572499 : ℚ))
        (U := (672710702479827681713 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (3929638815327 / 12800000000000 : ℚ))
      (lo := (554078543572499 / 1000000000000000 : ℚ))
      (hi := (5540785435724993 / 10000000000000000 : ℚ))
      (s := (554078543572499 / 1000000000000000 : ℚ))
      (r₁ := (16729638815327 / 12800000000000 : ℚ))
      (r₂ := (4001638815327 / 12800000000000 : ℚ))
      (z₁ := (10000000000000000 / 5540785435724993 : ℚ))
      (z₂ := (75000000000000 / 554078543572499 : ℚ))
      (L := (1338683773990469618213 / 5000000000000000000000 : ℚ))
      (U := (-(2906852973399345608809 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
