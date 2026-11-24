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

/-! # V07: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped ArctangentCertificates LogarithmCertificates

lemma V_85 :
    ((226771874510981741379 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14780287962918279265411 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((430806739120629 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1060808378329828977447 / 5000000000000000000000 : ℝ)) -
              6 * (41882007321997290791 / 125000000000000000000 : ℝ)))) ≤
      Vfield (742377785887 / 16000000000000 : ℝ) := by
  have hL1 :
    (226771874510981741379 / 5000000000000000000000 : ℝ) ≤
      Real.log (16742377785887 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (16742377785887 / 16000000000000 : ℚ))
        (L := (226771874510981741379 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (832377785887 / 16000000000000 : ℝ) ≤
      (-(14780287962918279265411 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (832377785887 / 16000000000000 : ℚ))
        (r' := (832377785887 / 500000000000 : ℚ))
        (U := (-(14780287962918279265411 / 5000000000000000000000 : ℚ)))
        (U' := (2548391544581720734589 / 5000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau147 :
    Real.arctan (538508423900787 / 2500000000000000 : ℝ) ≤
      (1060808378329828977447 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (538508423900787 / 2500000000000000 : ℚ))
        (U := (1060808378329828977447 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1060808378329828977447 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 538508423900787 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 538508423900787 : ℝ) =
              (538508423900787 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau147)
  have hat2 :
    Real.arctan (50000000000000 / 143602246373543 : ℝ) ≤
      (41882007321997290791 / 125000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (50000000000000 / 143602246373543 : ℚ))
        (U := (41882007321997290791 / 125000000000000000000 : ℚ))
        8 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (742377785887 / 16000000000000 : ℚ))
      (lo := (430806739120629 / 2000000000000000 : ℚ))
      (hi := (538508423900787 / 2500000000000000 : ℚ))
      (s := (430806739120629 / 2000000000000000 : ℚ))
      (r₁ := (16742377785887 / 16000000000000 : ℚ))
      (r₂ := (832377785887 / 16000000000000 : ℚ))
      (z₁ := (2500000000000000 / 538508423900787 : ℚ))
      (z₂ := (50000000000000 / 143602246373543 : ℚ))
      (L := (226771874510981741379 / 5000000000000000000000 : ℚ))
      (U := (-(14780287962918279265411 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_86 :
    ((457118096870510924543 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(29488926237277907956139 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2162699649333341 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2129896972254185019601 / 10000000000000000000000 : ℝ)) -
              6 * (834527990154732413477 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (598690530973 / 12800000000000 : ℝ) := by
  have hL1 :
    (457118096870510924543 / 10000000000000000000000 : ℝ) ≤
      Real.log (13398690530973 / 12800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (13398690530973 / 12800000000000 : ℚ))
        (L := (457118096870510924543 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (670690530973 / 12800000000000 : ℝ) ≤
      (-(29488926237277907956139 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (670690530973 / 12800000000000 : ℚ))
        (r' := (670690530973 / 400000000000 : ℚ))
        (U := (-(29488926237277907956139 / 10000000000000000000000 : ℚ)))
        (U' := (5168432777722092043861 / 10000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau148 :
    Real.arctan (67584364041667 / 312500000000000 : ℝ) ≤
      (2129896972254185019601 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (67584364041667 / 312500000000000 : ℚ))
        (U := (2129896972254185019601 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2129896972254185019601 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (312500000000000 / 67584364041667 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (312500000000000 / 67584364041667 : ℝ) =
              (67584364041667 / 312500000000000 : ℝ)
            by
        norm_num];
        exact hau148)
  have hat2 :
    Real.arctan (750000000000000 / 2162699649333341 : ℝ) ≤
      (834527990154732413477 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 2162699649333341 : ℚ))
        (U := (834527990154732413477 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (598690530973 / 12800000000000 : ℚ))
      (lo := (2162699649333341 / 10000000000000000 : ℚ))
      (hi := (67584364041667 / 312500000000000 : ℚ))
      (s := (2162699649333341 / 10000000000000000 : ℚ))
      (r₁ := (13398690530973 / 12800000000000 : ℚ))
      (r₂ := (670690530973 / 12800000000000 : ℚ))
      (z₁ := (312500000000000 / 67584364041667 : ℚ))
      (z₂ := (750000000000000 / 2162699649333341 : ℚ))
      (L := (457118096870510924543 / 10000000000000000000000 : ℚ))
      (U := (-(29488926237277907956139 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_87 :
    ((460691167579284695889 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(29417786266558953428469 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2171331016832617 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2138141194336938362321 / 10000000000000000000000 : ℝ)) -
              6 * (3325801225385149696601 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (1508697083091 / 32000000000000 : ℝ) := by
  have hL1 :
    (460691167579284695889 / 10000000000000000000000 : ℝ) ≤
      Real.log (33508697083091 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (33508697083091 / 32000000000000 : ℚ))
        (L := (460691167579284695889 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (1688697083091 / 32000000000000 : ℝ) ≤
      (-(29417786266558953428469 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1688697083091 / 32000000000000 : ℚ))
        (r' := (1688697083091 / 1000000000000 : ℚ))
        (U := (-(29417786266558953428469 / 10000000000000000000000 : ℚ)))
        (U' := (5239572748441046571531 / 10000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau149 :
    Real.arctan (108566550841631 / 500000000000000 : ℝ) ≤
      (2138141194336938362321 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (108566550841631 / 500000000000000 : ℚ))
        (U := (2138141194336938362321 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2138141194336938362321 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (500000000000000 / 108566550841631 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 108566550841631 : ℝ) =
              (108566550841631 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau149)
  have hat2 :
    Real.arctan (750000000000000 / 2171331016832617 : ℝ) ≤
      (3325801225385149696601 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 2171331016832617 : ℚ))
        (U := (3325801225385149696601 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1508697083091 / 32000000000000 : ℚ))
      (lo := (2171331016832617 / 10000000000000000 : ℚ))
      (hi := (108566550841631 / 500000000000000 : ℚ))
      (s := (2171331016832617 / 10000000000000000 : ℚ))
      (r₁ := (33508697083091 / 32000000000000 : ℚ))
      (r₂ := (1688697083091 / 32000000000000 : ℚ))
      (z₁ := (500000000000000 / 108566550841631 : ℚ))
      (z₂ := (750000000000000 / 2171331016832617 : ℚ))
      (L := (460691167579284695889 / 10000000000000000000000 : ℚ))
      (U := (-(29417786266558953428469 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_88 :
    ((464262962060620974379 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(29347148812585080077493 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((435985641786157 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (429269968176594904411 / 2000000000000000000000 : ℝ)) -
              6 * (1656812925087286155121 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (3041335677499 / 64000000000000 : ℝ) := by
  have hL1 :
    (464262962060620974379 / 10000000000000000000000 : ℝ) ≤
      Real.log (67041335677499 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (67041335677499 / 64000000000000 : ℚ))
        (L := (464262962060620974379 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (3401335677499 / 64000000000000 : ℝ) ≤
      (-(29347148812585080077493 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3401335677499 / 64000000000000 : ℚ))
        (r' := (3401335677499 / 2000000000000 : ℚ))
        (U := (-(29347148812585080077493 / 10000000000000000000000 : ℚ)))
        (U' := (5310210202414919922507 / 10000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau150 :
    Real.arctan (544982052232697 / 2500000000000000 : ℝ) ≤
      (429269968176594904411 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (544982052232697 / 2500000000000000 : ℚ))
        (U := (429269968176594904411 / 2000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (429269968176594904411 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 544982052232697 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 544982052232697 : ℝ) =
              (544982052232697 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau150)
  have hat2 :
    Real.arctan (150000000000000 / 435985641786157 : ℝ) ≤
      (1656812925087286155121 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 435985641786157 : ℚ))
        (U := (1656812925087286155121 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (3041335677499 / 64000000000000 : ℚ))
      (lo := (435985641786157 / 2000000000000000 : ℚ))
      (hi := (544982052232697 / 2500000000000000 : ℚ))
      (s := (435985641786157 / 2000000000000000 : ℚ))
      (r₁ := (67041335677499 / 64000000000000 : ℚ))
      (r₂ := (3401335677499 / 64000000000000 : ℚ))
      (z₁ := (2500000000000000 / 544982052232697 : ℚ))
      (z₂ := (150000000000000 / 435985641786157 : ℚ))
      (L := (464262962060620974379 / 10000000000000000000000 : ℚ))
      (U := (-(29347148812585080077493 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_89 :
    ((233916740612939341691 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(3659625853224161050433 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((437698325677629 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2154523321717564278481 / 10000000000000000000000 : ℝ)) -
              6 * (1320633347875011933 / 4000000000000000000 : ℝ)))) ≤
      Vfield (191579824301 / 4000000000000 : ℝ) := by
  have hL1 :
    (233916740612939341691 / 5000000000000000000000 : ℝ) ≤
      Real.log (4191579824301 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (4191579824301 / 4000000000000 : ℚ))
        (L := (233916740612939341691 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (214079824301 / 4000000000000 : ℝ) ≤
      (-(3659625853224161050433 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (214079824301 / 4000000000000 : ℚ))
        (r' := (214079824301 / 125000000000 : ℚ))
        (U := (-(3659625853224161050433 / 1250000000000000000000 : ℚ)))
        (U' := (672544023650838949567 / 1250000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau151 :
    Real.arctan (547122907097037 / 2500000000000000 : ℝ) ≤
      (2154523321717564278481 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (547122907097037 / 2500000000000000 : ℚ))
        (U := (2154523321717564278481 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2154523321717564278481 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 547122907097037 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 547122907097037 : ℝ) =
              (547122907097037 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau151)
  have hat2 :
    Real.arctan (50000000000000 / 145899441892543 : ℝ) ≤
      (1320633347875011933 / 4000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (50000000000000 / 145899441892543 : ℚ))
        (U := (1320633347875011933 / 4000000000000000000 : ℚ))
        8 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (191579824301 / 4000000000000 : ℚ))
      (lo := (437698325677629 / 2000000000000000 : ℚ))
      (hi := (547122907097037 / 2500000000000000 : ℚ))
      (s := (437698325677629 / 2000000000000000 : ℚ))
      (r₁ := (4191579824301 / 4000000000000 : ℚ))
      (r₂ := (214079824301 / 4000000000000 : ℚ))
      (z₁ := (2500000000000000 / 547122907097037 : ℚ))
      (z₂ := (50000000000000 / 145899441892543 : ℚ))
      (L := (233916740612939341691 / 5000000000000000000000 : ℚ))
      (U := (-(3659625853224161050433 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_90 :
    ((47140272598544088727 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(29207353403930246574293 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((109851083505783 / 500000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (432532407747580506091 / 2000000000000000000000 : ℝ)) -
              6 * (1644835690550822215319 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (3089218700133 / 64000000000000 : ℝ) := by
  have hL1 :
    (47140272598544088727 / 1000000000000000000000 : ℝ) ≤
      Real.log (67089218700133 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (67089218700133 / 64000000000000 : ℚ))
        (L := (47140272598544088727 / 1000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (3449218700133 / 64000000000000 : ℝ) ≤
      (-(29207353403930246574293 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3449218700133 / 64000000000000 : ℚ))
        (r' := (3449218700133 / 2000000000000 : ℚ))
        (U := (-(29207353403930246574293 / 10000000000000000000000 : ℚ)))
        (U' := (5450005611069753425707 / 10000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau152 :
    Real.arctan (2197021670115663 / 10000000000000000 : ℝ) ≤
      (432532407747580506091 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2197021670115663 / 10000000000000000 : ℚ))
        (U := (432532407747580506091 / 2000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (432532407747580506091 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2197021670115663 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2197021670115663 : ℝ) =
              (2197021670115663 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau152)
  have hat2 :
    Real.arctan (12500000000000 / 36617027835261 : ℝ) ≤
      (1644835690550822215319 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (12500000000000 / 36617027835261 : ℚ))
        (U := (1644835690550822215319 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (3089218700133 / 64000000000000 : ℚ))
      (lo := (109851083505783 / 500000000000000 : ℚ))
      (hi := (2197021670115663 / 10000000000000000 : ℚ))
      (s := (109851083505783 / 500000000000000 : ℚ))
      (r₁ := (67089218700133 / 64000000000000 : ℚ))
      (r₂ := (3449218700133 / 64000000000000 : ℚ))
      (z₁ := (10000000000000000 / 2197021670115663 : ℚ))
      (z₂ := (12500000000000 / 36617027835261 : ℚ))
      (L := (47140272598544088727 / 1000000000000000000000 : ℚ))
      (U := (-(29207353403930246574293 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_91 :
    ((118742674312179046039 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(29138181787976365168227 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((220551872138747 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2170766386127115701763 / 10000000000000000000000 : ℝ)) -
              6 * (655577508409682210587 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (62263204229 / 1280000000000 : ℝ) := by
  have hL1 :
    (118742674312179046039 / 2500000000000000000000 : ℝ) ≤
      Real.log (1342263204229 / 1280000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1342263204229 / 1280000000000 : ℚ))
        (L := (118742674312179046039 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (69463204229 / 1280000000000 : ℝ) ≤
      (-(29138181787976365168227 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (69463204229 / 1280000000000 : ℚ))
        (r' := (69463204229 / 40000000000 : ℚ))
        (U := (-(29138181787976365168227 / 10000000000000000000000 : ℚ)))
        (U' := (5519177227023634831773 / 10000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau153 :
    Real.arctan (2205518721387473 / 10000000000000000 : ℝ) ≤
      (2170766386127115701763 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2205518721387473 / 10000000000000000 : ℚ))
        (U := (2170766386127115701763 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2170766386127115701763 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2205518721387473 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2205518721387473 : ℝ) =
              (2205518721387473 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau153)
  have hat2 :
    Real.arctan (75000000000000 / 220551872138747 : ℝ) ≤
      (655577508409682210587 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (75000000000000 / 220551872138747 : ℚ))
        (U := (655577508409682210587 / 2000000000000000000000 : ℚ))
        7 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (62263204229 / 1280000000000 : ℚ))
      (lo := (220551872138747 / 1000000000000000 : ℚ))
      (hi := (2205518721387473 / 10000000000000000 : ℚ))
      (s := (220551872138747 / 1000000000000000 : ℚ))
      (r₁ := (1342263204229 / 1280000000000 : ℚ))
      (r₂ := (69463204229 / 1280000000000 : ℚ))
      (z₁ := (10000000000000000 / 2205518721387473 : ℚ))
      (z₂ := (75000000000000 / 220551872138747 : ℚ))
      (L := (118742674312179046039 / 2500000000000000000000 : ℚ))
      (U := (-(29138181787976365168227 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_92 :
    ((478537395924140096139 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1816842834888117217761 / 625000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2213983162046051 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (544709187640218728401 / 2500000000000000000000 : ℝ)) -
              6 * (25517418505229754007 / 78125000000000000000 : ℝ)))) ≤
      Vfield (3137101722767 / 64000000000000 : ℝ) := by
  have hL1 :
    (478537395924140096139 / 10000000000000000000000 : ℝ) ≤
      Real.log (67137101722767 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (67137101722767 / 64000000000000 : ℚ))
        (L := (478537395924140096139 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (3497101722767 / 64000000000000 : ℝ) ≤
      (-(1816842834888117217761 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3497101722767 / 64000000000000 : ℚ))
        (r' := (3497101722767 / 2000000000000 : ℚ))
        (U := (-(1816842834888117217761 / 625000000000000000000 : ℚ)))
        (U' := (349242103549382782239 / 625000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau154 :
    Real.arctan (1106991581023027 / 5000000000000000 : ℝ) ≤
      (544709187640218728401 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1106991581023027 / 5000000000000000 : ℚ))
        (U := (544709187640218728401 / 2500000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (544709187640218728401 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1106991581023027 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1106991581023027 : ℝ) =
              (1106991581023027 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau154)
  have hat2 :
    Real.arctan (750000000000000 / 2213983162046051 : ℝ) ≤
      (25517418505229754007 / 78125000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 2213983162046051 : ℚ))
        (U := (25517418505229754007 / 78125000000000000000 : ℚ))
        7 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (3137101722767 / 64000000000000 : ℚ))
      (lo := (2213983162046051 / 10000000000000000 : ℚ))
      (hi := (1106991581023027 / 5000000000000000 : ℚ))
      (s := (2213983162046051 / 10000000000000000 : ℚ))
      (r₁ := (67137101722767 / 64000000000000 : ℚ))
      (r₂ := (3497101722767 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 1106991581023027 : ℚ))
      (z₂ := (750000000000000 / 2213983162046051 : ℚ))
      (L := (478537395924140096139 / 10000000000000000000000 : ℚ))
      (U := (-(1816842834888117217761 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_93 :
    ((241051411459588228539 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14500628815202590003913 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1111207682350181 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2186873511406957655783 / 10000000000000000000000 : ℝ)) -
              6 * (3254695233748423021389 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (790260808521 / 16000000000000 : ℝ) := by
  have hL1 :
    (241051411459588228539 / 5000000000000000000000 : ℝ) ≤
      Real.log (16790260808521 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (16790260808521 / 16000000000000 : ℚ))
        (L := (241051411459588228539 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (880260808521 / 16000000000000 : ℝ) ≤
      (-(14500628815202590003913 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (880260808521 / 16000000000000 : ℚ))
        (r' := (880260808521 / 500000000000 : ℚ))
        (U := (-(14500628815202590003913 / 5000000000000000000000 : ℚ)))
        (U' := (2828050692297409996087 / 5000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau155 :
    Real.arctan (444483072940073 / 2000000000000000 : ℝ) ≤
      (2186873511406957655783 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (444483072940073 / 2000000000000000 : ℚ))
        (U := (2186873511406957655783 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2186873511406957655783 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 444483072940073 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 444483072940073 : ℝ) =
              (444483072940073 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau155)
  have hat2 :
    Real.arctan (375000000000000 / 1111207682350181 : ℝ) ≤
      (3254695233748423021389 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 1111207682350181 : ℚ))
        (U := (3254695233748423021389 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (790260808521 / 16000000000000 : ℚ))
      (lo := (1111207682350181 / 5000000000000000 : ℚ))
      (hi := (444483072940073 / 2000000000000000 : ℚ))
      (s := (1111207682350181 / 5000000000000000 : ℚ))
      (r₁ := (16790260808521 / 16000000000000 : ℚ))
      (r₂ := (880260808521 / 16000000000000 : ℚ))
      (z₁ := (2000000000000000 / 444483072940073 : ℚ))
      (z₂ := (375000000000000 / 1111207682350181 : ℚ))
      (L := (241051411459588228539 / 5000000000000000000000 : ℚ))
      (U := (-(14500628815202590003913 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_94 :
    ((7588546549067481217 / 156250000000000000000 : ℝ) -
              6 * (3 / 40) * (-(361668653152000194621 / 125000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2230815694917233 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2194877040918014085383 / 10000000000000000000000 : ℝ)) -
              6 * (1621641182458017941551 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (3184984745401 / 64000000000000 : ℝ) := by
  have hL1 :
    (7588546549067481217 / 156250000000000000000 : ℝ) ≤
      Real.log (67184984745401 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (67184984745401 / 64000000000000 : ℚ))
        (L := (7588546549067481217 / 156250000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (3544984745401 / 64000000000000 : ℝ) ≤
      (-(361668653152000194621 / 125000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3544984745401 / 64000000000000 : ℚ))
        (r' := (3544984745401 / 2000000000000 : ℚ))
        (U := (-(361668653152000194621 / 125000000000000000000 : ℚ)))
        (U' := (71548334535499805379 / 125000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau156 :
    Real.arctan (557703923729309 / 2500000000000000 : ℝ) ≤
      (2194877040918014085383 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (557703923729309 / 2500000000000000 : ℚ))
        (U := (2194877040918014085383 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2194877040918014085383 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 557703923729309 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 557703923729309 : ℝ) =
              (557703923729309 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau156)
  have hat2 :
    Real.arctan (750000000000000 / 2230815694917233 : ℝ) ≤
      (1621641182458017941551 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 2230815694917233 : ℚ))
        (U := (1621641182458017941551 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (3184984745401 / 64000000000000 : ℚ))
      (lo := (2230815694917233 / 10000000000000000 : ℚ))
      (hi := (557703923729309 / 2500000000000000 : ℚ))
      (s := (2230815694917233 / 10000000000000000 : ℚ))
      (r₁ := (67184984745401 / 64000000000000 : ℚ))
      (r₂ := (3544984745401 / 64000000000000 : ℚ))
      (z₁ := (2500000000000000 / 557703923729309 : ℚ))
      (z₂ := (750000000000000 / 2230815694917233 : ℚ))
      (L := (7588546549067481217 / 156250000000000000000 : ℚ))
      (U := (-(361668653152000194621 / 125000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_95 :
    ((489229865493091729373 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14433091499673113264557 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((22391845114063 / 100000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1101423852208921727903 / 5000000000000000000000 : ℝ)) -
              6 * (807997210730837352441 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (1604463128359 / 32000000000000 : ℝ) := by
  have hL1 :
    (489229865493091729373 / 10000000000000000000000 : ℝ) ≤
      Real.log (33604463128359 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (33604463128359 / 32000000000000 : ℚ))
        (L := (489229865493091729373 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (1784463128359 / 32000000000000 : ℝ) ≤
      (-(14433091499673113264557 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1784463128359 / 32000000000000 : ℚ))
        (r' := (1784463128359 / 1000000000000 : ℚ))
        (U := (-(14433091499673113264557 / 5000000000000000000000 : ℚ)))
        (U' := (2895588007826886735443 / 5000000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau157 :
    Real.arctan (2239184511406303 / 10000000000000000 : ℝ) ≤
      (1101423852208921727903 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2239184511406303 / 10000000000000000 : ℚ))
        (U := (1101423852208921727903 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1101423852208921727903 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 2239184511406303 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 2239184511406303 : ℝ) =
              (2239184511406303 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau157)
  have hat2 :
    Real.arctan (7500000000000 / 22391845114063 : ℝ) ≤
      (807997210730837352441 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7500000000000 / 22391845114063 : ℚ))
        (U := (807997210730837352441 / 2500000000000000000000 : ℚ))
        7 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1604463128359 / 32000000000000 : ℚ))
      (lo := (22391845114063 / 100000000000000 : ℚ))
      (hi := (2239184511406303 / 10000000000000000 : ℚ))
      (s := (22391845114063 / 100000000000000 : ℚ))
      (r₁ := (33604463128359 / 32000000000000 : ℚ))
      (r₂ := (1784463128359 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 2239184511406303 : ℚ))
      (z₂ := (7500000000000 / 22391845114063 : ℚ))
      (L := (489229865493091729373 / 10000000000000000000000 : ℚ))
      (U := (-(14433091499673113264557 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_96 :
    ((123197870720513080647 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(14399661886339595032899 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2247522166198741 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2210785860481439136199 / 10000000000000000000000 : ℝ)) -
              6 * (3220812599981731487411 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (646573553607 / 12800000000000 : ℝ) := by
  have hL1 :
    (123197870720513080647 / 2500000000000000000000 : ℝ) ≤
      Real.log (13446573553607 / 12800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (13446573553607 / 12800000000000 : ℚ))
        (L := (123197870720513080647 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  have hU2 :
    Real.log (718573553607 / 12800000000000 : ℝ) ≤
      (-(14399661886339595032899 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (718573553607 / 12800000000000 : ℚ))
        (r' := (718573553607 / 400000000000 : ℚ))
        (U := (-(14399661886339595032899 / 5000000000000000000000 : ℚ)))
        (U' := (2929017621160404967101 / 5000000000000000000000 : ℚ))
        5 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau158 :
    Real.arctan (280940270774843 / 1250000000000000 : ℝ) ≤
      (2210785860481439136199 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (280940270774843 / 1250000000000000 : ℚ))
        (U := (2210785860481439136199 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2210785860481439136199 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 280940270774843 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 280940270774843 : ℝ) =
              (280940270774843 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau158)
  have hat2 :
    Real.arctan (750000000000000 / 2247522166198741 : ℝ) ≤
      (3220812599981731487411 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 2247522166198741 : ℚ))
        (U := (3220812599981731487411 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (646573553607 / 12800000000000 : ℚ))
      (lo := (2247522166198741 / 10000000000000000 : ℚ))
      (hi := (280940270774843 / 1250000000000000 : ℚ))
      (s := (2247522166198741 / 10000000000000000 : ℚ))
      (r₁ := (13446573553607 / 12800000000000 : ℚ))
      (r₂ := (718573553607 / 12800000000000 : ℚ))
      (z₁ := (1250000000000000 / 280940270774843 : ℚ))
      (z₂ := (750000000000000 / 2247522166198741 : ℚ))
      (L := (123197870720513080647 / 2500000000000000000000 : ℚ))
      (U := (-(14399661886339595032899 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
