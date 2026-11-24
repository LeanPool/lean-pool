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

/-! # V16: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped ArctangentCertificates LogarithmCertificates

lemma V_193 :
    ((1379119536463717589619 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1874058101002048808097 / 1000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1922722546692823 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3671120904872284070399 / 10000000000000000000000 : ℝ)) -
              6 * (1926179010437621127729 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2365991674599 / 16000000000000 : ℝ) := by
  have hL1 :
    (1379119536463717589619 / 10000000000000000000000 : ℝ) ≤
      Real.log (18365991674599 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (18365991674599 / 16000000000000 : ℚ))
        (L := (1379119536463717589619 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (2455991674599 / 16000000000000 : ℝ) ≤
      (-(1874058101002048808097 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2455991674599 / 16000000000000 : ℚ))
        (r' := (2455991674599 / 2000000000000 : ℚ))
        (U := (-(1874058101002048808097 / 1000000000000000000000 : ℚ)))
        (U' := (205383439897951191903 / 1000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau255 :
    Real.arctan (3845445093385649 / 10000000000000000 : ℝ) ≤
      (3671120904872284070399 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3845445093385649 / 10000000000000000 : ℚ))
        (U := (3671120904872284070399 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3671120904872284070399 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3845445093385649 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3845445093385649 : ℝ) =
              (3845445093385649 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau255)
  have hat2 :
    Real.arctan (375000000000000 / 1922722546692823 : ℝ) ≤
      (1926179010437621127729 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 1922722546692823 : ℚ))
        (U := (1926179010437621127729 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2365991674599 / 16000000000000 : ℚ))
      (lo := (1922722546692823 / 5000000000000000 : ℚ))
      (hi := (3845445093385649 / 10000000000000000 : ℚ))
      (s := (1922722546692823 / 5000000000000000 : ℚ))
      (r₁ := (18365991674599 / 16000000000000 : ℚ))
      (r₂ := (2455991674599 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3845445093385649 : ℚ))
      (z₂ := (375000000000000 / 1922722546692823 : ℚ))
      (L := (1379119536463717589619 / 10000000000000000000000 : ℚ))
      (U := (-(1874058101002048808097 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_194 :
    ((1394565529352076953773 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18625649088734036599843 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((120888982420927 / 312500000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (922786131046177653937 / 2500000000000000000000 : ℝ)) -
              6 * (1915004440272120860647 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4788763384469 / 32000000000000 : ℝ) := by
  have hL1 :
    (1394565529352076953773 / 10000000000000000000000 : ℝ) ≤
      Real.log (36788763384469 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (36788763384469 / 32000000000000 : ℚ))
        (L := (1394565529352076953773 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (4968763384469 / 32000000000000 : ℝ) ≤
      (-(18625649088734036599843 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4968763384469 / 32000000000000 : ℚ))
        (r' := (4968763384469 / 4000000000000 : ℚ))
        (U := (-(18625649088734036599843 / 10000000000000000000000 : ℚ)))
        (U' := (2168766320265963400157 / 10000000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau256 :
    Real.arctan (3868447437469667 / 10000000000000000 : ℝ) ≤
      (922786131046177653937 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3868447437469667 / 10000000000000000 : ℚ))
        (U := (922786131046177653937 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (922786131046177653937 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3868447437469667 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3868447437469667 : ℝ) =
              (3868447437469667 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau256)
  have hat2 :
    Real.arctan (23437500000000 / 120888982420927 : ℝ) ≤
      (1915004440272120860647 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (23437500000000 / 120888982420927 : ℚ))
        (U := (1915004440272120860647 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4788763384469 / 32000000000000 : ℚ))
      (lo := (120888982420927 / 312500000000000 : ℚ))
      (hi := (3868447437469667 / 10000000000000000 : ℚ))
      (s := (120888982420927 / 312500000000000 : ℚ))
      (r₁ := (36788763384469 / 32000000000000 : ℚ))
      (r₂ := (4968763384469 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3868447437469667 : ℚ))
      (z₂ := (23437500000000 / 120888982420927 : ℚ))
      (L := (1394565529352076953773 / 10000000000000000000000 : ℚ))
      (U := (-(18625649088734036599843 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_195 :
    ((175284948537260638459 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4642168678222045719597 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3879897470497971 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1850550138337685246867 / 5000000000000000000000 : ℝ)) -
              6 * (1909489605510279217527 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (9634306804209 / 64000000000000 : ℝ) := by
  have hL1 :
    (175284948537260638459 / 1250000000000000000000 : ℝ) ≤
      Real.log (73634306804209 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (73634306804209 / 64000000000000 : ℚ))
        (L := (175284948537260638459 / 1250000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (9994306804209 / 64000000000000 : ℝ) ≤
      (-(4642168678222045719597 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (9994306804209 / 64000000000000 : ℚ))
        (r' := (9994306804209 / 8000000000000 : ℚ))
        (U := (-(4642168678222045719597 / 2500000000000000000000 : ℚ)))
        (U' := (556435174027954280403 / 2500000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau257 :
    Real.arctan (1939948735248987 / 5000000000000000 : ℝ) ≤
      (1850550138337685246867 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1939948735248987 / 5000000000000000 : ℚ))
        (U := (1850550138337685246867 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1850550138337685246867 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1939948735248987 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1939948735248987 : ℝ) =
              (1939948735248987 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau257)
  have hat2 :
    Real.arctan (250000000000000 / 1293299156832657 : ℝ) ≤
      (1909489605510279217527 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1293299156832657 : ℚ))
        (U := (1909489605510279217527 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (9634306804209 / 64000000000000 : ℚ))
      (lo := (3879897470497971 / 10000000000000000 : ℚ))
      (hi := (1939948735248987 / 5000000000000000 : ℚ))
      (s := (3879897470497971 / 10000000000000000 : ℚ))
      (r₁ := (73634306804209 / 64000000000000 : ℚ))
      (r₂ := (9994306804209 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 1939948735248987 : ℚ))
      (z₂ := (250000000000000 / 1293299156832657 : ℚ))
      (L := (175284948537260638459 / 1250000000000000000000 : ℚ))
      (U := (-(4642168678222045719597 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_196 :
    ((1409987701160100614743 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4628005776724920317491 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3891313812414451 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (742203816691221276071 / 2000000000000000000000 : ℝ)) -
              6 * (1904022148523259736843 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (242277170987 / 1600000000000 : ℝ) := by
  have hL1 :
    (1409987701160100614743 / 10000000000000000000000 : ℝ) ≤
      Real.log (1842277170987 / 1600000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1842277170987 / 1600000000000 : ℚ))
        (L := (1409987701160100614743 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (251277170987 / 1600000000000 : ℝ) ≤
      (-(4628005776724920317491 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (251277170987 / 1600000000000 : ℚ))
        (r' := (251277170987 / 200000000000 : ℚ))
        (U := (-(4628005776724920317491 / 2500000000000000000000 : ℚ)))
        (U' := (570598075525079682509 / 2500000000000000000000 : ℚ))
        3 7 (by decide +kernel) (by constructor <;> norm_num)
  have hau258 :
    Real.arctan (1945656906207227 / 5000000000000000 : ℝ) ≤
      (742203816691221276071 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1945656906207227 / 5000000000000000 : ℚ))
        (U := (742203816691221276071 / 2000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (742203816691221276071 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 1945656906207227 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 1945656906207227 : ℝ) =
              (1945656906207227 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau258)
  have hat2 :
    Real.arctan (750000000000000 / 3891313812414451 : ℝ) ≤
      (1904022148523259736843 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 3891313812414451 : ℚ))
        (U := (1904022148523259736843 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (242277170987 / 1600000000000 : ℚ))
      (lo := (3891313812414451 / 10000000000000000 : ℚ))
      (hi := (1945656906207227 / 5000000000000000 : ℚ))
      (s := (3891313812414451 / 10000000000000000 : ℚ))
      (r₁ := (1842277170987 / 1600000000000 : ℚ))
      (r₂ := (251277170987 / 1600000000000 : ℚ))
      (z₁ := (5000000000000000 / 1945656906207227 : ℚ))
      (z₂ := (750000000000000 / 3891313812414451 : ℚ))
      (L := (1409987701160100614743 / 10000000000000000000000 : ℚ))
      (U := (-(4628005776724920317491 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_197 :
    ((283537975419536278287 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18455690634264303292773 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3902696758883327 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (744180251624464067841 / 2000000000000000000000 : ℝ)) -
              6 * (1898601394724880011151 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (9747866874751 / 64000000000000 : ℝ) := by
  have hL1 :
    (283537975419536278287 / 2000000000000000000000 : ℝ) ≤
      Real.log (73747866874751 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (73747866874751 / 64000000000000 : ℚ))
        (L := (283537975419536278287 / 2000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (10107866874751 / 64000000000000 : ℝ) ≤
      (-(18455690634264303292773 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10107866874751 / 64000000000000 : ℚ))
        (r' := (10107866874751 / 8000000000000 : ℚ))
        (U := (-(18455690634264303292773 / 10000000000000000000000 : ℚ)))
        (U' := (2338724774735696707227 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by constructor <;> norm_num)
  have hau259 :
    Real.arctan (390269675888333 / 1000000000000000 : ℝ) ≤
      (744180251624464067841 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (390269675888333 / 1000000000000000 : ℚ))
        (U := (744180251624464067841 / 2000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (744180251624464067841 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 390269675888333 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 390269675888333 : ℝ) =
              (390269675888333 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau259)
  have hat2 :
    Real.arctan (750000000000000 / 3902696758883327 : ℝ) ≤
      (1898601394724880011151 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 3902696758883327 : ℚ))
        (U := (1898601394724880011151 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (9747866874751 / 64000000000000 : ℚ))
      (lo := (3902696758883327 / 10000000000000000 : ℚ))
      (hi := (390269675888333 / 1000000000000000 : ℚ))
      (s := (3902696758883327 / 10000000000000000 : ℚ))
      (r₁ := (73747866874751 / 64000000000000 : ℚ))
      (r₂ := (10107866874751 / 64000000000000 : ℚ))
      (z₁ := (1000000000000000 / 390269675888333 : ℚ))
      (z₂ := (750000000000000 / 3902696758883327 : ℚ))
      (L := (283537975419536278287 / 2000000000000000000000 : ℚ))
      (U := (-(18455690634264303292773 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_198 :
    ((1425386125249237081831 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(73598694878360117537 / 40000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((782809320253901 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3730747109815750035747 / 10000000000000000000000 : ℝ)) -
              6 * (1893226682901490889443 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4902323455011 / 32000000000000 : ℝ) := by
  have hL1 :
    (1425386125249237081831 / 10000000000000000000000 : ℝ) ≤
      Real.log (36902323455011 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (36902323455011 / 32000000000000 : ℚ))
        (L := (1425386125249237081831 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (5082323455011 / 32000000000000 : ℝ) ≤
      (-(73598694878360117537 / 40000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5082323455011 / 32000000000000 : ℚ))
        (r' := (5082323455011 / 4000000000000 : ℚ))
        (U := (-(73598694878360117537 / 40000000000000000000 : ℚ)))
        (U' := (9578966757639882463 / 40000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by constructor <;> norm_num)
  have hau260 :
    Real.arctan (978511650317377 / 2500000000000000 : ℝ) ≤
      (3730747109815750035747 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (978511650317377 / 2500000000000000 : ℚ))
        (U := (3730747109815750035747 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3730747109815750035747 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 978511650317377 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 978511650317377 : ℝ) =
              (978511650317377 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau260)
  have hat2 :
    Real.arctan (150000000000000 / 782809320253901 : ℝ) ≤
      (1893226682901490889443 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 782809320253901 : ℚ))
        (U := (1893226682901490889443 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4902323455011 / 32000000000000 : ℚ))
      (lo := (782809320253901 / 2000000000000000 : ℚ))
      (hi := (978511650317377 / 2500000000000000 : ℚ))
      (s := (782809320253901 / 2000000000000000 : ℚ))
      (r₁ := (36902323455011 / 32000000000000 : ℚ))
      (r₂ := (5082323455011 / 32000000000000 : ℚ))
      (z₁ := (2500000000000000 / 978511650317377 : ℚ))
      (z₂ := (150000000000000 / 782809320253901 : ℚ))
      (L := (1425386125249237081831 / 10000000000000000000000 : ℚ))
      (U := (-(73598694878360117537 / 40000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_199 :
    ((716538227366047056267 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18343968847235335596581 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3925363626725593 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (935139235828401014473 / 2500000000000000000000 : ℝ)) -
              6 * (47197434121825702827 / 250000000000000000000 : ℝ)))) ≤
      Vfield (9861426945293 / 64000000000000 : ℝ) := by
  have hL1 :
    (716538227366047056267 / 5000000000000000000000 : ℝ) ≤
      Real.log (73861426945293 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (73861426945293 / 64000000000000 : ℚ))
        (L := (716538227366047056267 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (10221426945293 / 64000000000000 : ℝ) ≤
      (-(18343968847235335596581 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (10221426945293 / 64000000000000 : ℚ))
        (r' := (10221426945293 / 8000000000000 : ℚ))
        (U := (-(18343968847235335596581 / 10000000000000000000000 : ℚ)))
        (U' := (2450446561764664403419 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by constructor <;> norm_num)
  have hau261 :
    Real.arctan (981340906681399 / 2500000000000000 : ℝ) ≤
      (935139235828401014473 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (981340906681399 / 2500000000000000 : ℚ))
        (U := (935139235828401014473 / 2500000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (935139235828401014473 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 981340906681399 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 981340906681399 : ℝ) =
              (981340906681399 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau261)
  have hat2 :
    Real.arctan (750000000000000 / 3925363626725593 : ℝ) ≤
      (47197434121825702827 / 250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 3925363626725593 : ℚ))
        (U := (47197434121825702827 / 250000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (9861426945293 / 64000000000000 : ℚ))
      (lo := (3925363626725593 / 10000000000000000 : ℚ))
      (hi := (981340906681399 / 2500000000000000 : ℚ))
      (s := (3925363626725593 / 10000000000000000 : ℚ))
      (r₁ := (73861426945293 / 64000000000000 : ℚ))
      (r₂ := (10221426945293 / 64000000000000 : ℚ))
      (z₁ := (2500000000000000 / 981340906681399 : ℚ))
      (z₂ := (750000000000000 / 3925363626725593 : ℚ))
      (L := (716538227366047056267 / 5000000000000000000000 : ℚ))
      (U := (-(18343968847235335596581 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_200 :
    ((360190218660640124399 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(914428627999259877791 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3936648118276669 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (468791382389424016227 / 1250000000000000000000 : ℝ)) -
              6 * (117663300322781655899 / 625000000000000000000 : ℝ)))) ≤
      Vfield (2479551745141 / 16000000000000 : ℝ) := by
  have hL1 :
    (360190218660640124399 / 2500000000000000000000 : ℝ) ≤
      Real.log (18479551745141 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (18479551745141 / 16000000000000 : ℚ))
        (L := (360190218660640124399 / 2500000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (2569551745141 / 16000000000000 : ℝ) ≤
      (-(914428627999259877791 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2569551745141 / 16000000000000 : ℚ))
        (r' := (2569551745141 / 2000000000000 : ℚ))
        (U := (-(914428627999259877791 / 500000000000000000000 : ℚ)))
        (U' := (125292142450740122209 / 500000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by constructor <;> norm_num)
  have hau262 :
    Real.arctan (61510126848073 / 156250000000000 : ℝ) ≤
      (468791382389424016227 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (61510126848073 / 156250000000000 : ℚ))
        (U := (468791382389424016227 / 1250000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (468791382389424016227 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (156250000000000 / 61510126848073 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (156250000000000 / 61510126848073 : ℝ) =
              (61510126848073 / 156250000000000 : ℝ)
            by
        norm_num];
        exact hau262)
  have hat2 :
    Real.arctan (750000000000000 / 3936648118276669 : ℝ) ≤
      (117663300322781655899 / 625000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 3936648118276669 : ℚ))
        (U := (117663300322781655899 / 625000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2479551745141 / 16000000000000 : ℚ))
      (lo := (3936648118276669 / 10000000000000000 : ℚ))
      (hi := (61510126848073 / 156250000000000 : ℚ))
      (s := (3936648118276669 / 10000000000000000 : ℚ))
      (r₁ := (18479551745141 / 16000000000000 : ℚ))
      (r₂ := (2569551745141 / 16000000000000 : ℚ))
      (z₁ := (156250000000000 / 61510126848073 : ℚ))
      (z₂ := (750000000000000 / 3936648118276669 : ℚ))
      (L := (360190218660640124399 / 2500000000000000000000 : ℚ))
      (U := (-(914428627999259877791 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_201 :
    ((722300435672506061083 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18260989071053057397457 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((394227825117491 / 1000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3755204815637543892277 / 10000000000000000000000 : ℝ)) -
              6 * (1879987114489769237383 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (19893193996399 / 128000000000000 : ℝ) := by
  have hL1 :
    (722300435672506061083 / 5000000000000000000000 : ℝ) ≤
      Real.log (147893193996399 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (147893193996399 / 128000000000000 : ℚ))
        (L := (722300435672506061083 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (20613193996399 / 128000000000000 : ℝ) ≤
      (-(18260989071053057397457 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20613193996399 / 128000000000000 : ℚ))
        (r' := (20613193996399 / 16000000000000 : ℚ))
        (U := (-(18260989071053057397457 / 10000000000000000000000 : ℚ)))
        (U' := (2533426337946942602543 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by constructor <;> norm_num)
  have hau263 :
    Real.arctan (3942278251174913 / 10000000000000000 : ℝ) ≤
      (3755204815637543892277 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3942278251174913 / 10000000000000000 : ℚ))
        (U := (3755204815637543892277 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3755204815637543892277 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3942278251174913 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3942278251174913 : ℝ) =
              (3942278251174913 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau263)
  have hat2 :
    Real.arctan (75000000000000 / 394227825117491 : ℝ) ≤
      (1879987114489769237383 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (75000000000000 / 394227825117491 : ℚ))
        (U := (1879987114489769237383 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (19893193996399 / 128000000000000 : ℚ))
      (lo := (394227825117491 / 1000000000000000 : ℚ))
      (hi := (3942278251174913 / 10000000000000000 : ℚ))
      (s := (394227825117491 / 1000000000000000 : ℚ))
      (r₁ := (147893193996399 / 128000000000000 : ℚ))
      (r₂ := (20613193996399 / 128000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3942278251174913 : ℚ))
      (z₂ := (75000000000000 / 394227825117491 : ℚ))
      (L := (722300435672506061083 / 5000000000000000000000 : ℚ))
      (U := (-(18260989071053057397457 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_202 :
    ((1448439394055990394649 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18233481457763565163467 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1973950177451433 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3760069753527545238699 / 10000000000000000000000 : ℝ)) -
              6 * (187737238068757978517 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (1994997403167 / 12800000000000 : ℝ) := by
  have hL1 :
    (1448439394055990394649 / 10000000000000000000000 : ℝ) ≤
      Real.log (14794997403167 / 12800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (14794997403167 / 12800000000000 : ℚ))
        (L := (1448439394055990394649 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (2066997403167 / 12800000000000 : ℝ) ≤
      (-(18233481457763565163467 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2066997403167 / 12800000000000 : ℚ))
        (r' := (2066997403167 / 1600000000000 : ℚ))
        (U := (-(18233481457763565163467 / 10000000000000000000000 : ℚ)))
        (U' := (2560933951236434836533 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by constructor <;> norm_num)
  have hau264 :
    Real.arctan (3947900354902869 / 10000000000000000 : ℝ) ≤
      (3760069753527545238699 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3947900354902869 / 10000000000000000 : ℚ))
        (U := (3760069753527545238699 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3760069753527545238699 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3947900354902869 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3947900354902869 : ℝ) =
              (3947900354902869 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau264)
  have hat2 :
    Real.arctan (125000000000000 / 657983392483811 : ℝ) ≤
      (187737238068757978517 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (125000000000000 / 657983392483811 : ℚ))
        (U := (187737238068757978517 / 1000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1994997403167 / 12800000000000 : ℚ))
      (lo := (1973950177451433 / 5000000000000000 : ℚ))
      (hi := (3947900354902869 / 10000000000000000 : ℚ))
      (s := (1973950177451433 / 5000000000000000 : ℚ))
      (r₁ := (14794997403167 / 12800000000000 : ℚ))
      (r₂ := (2066997403167 / 12800000000000 : ℚ))
      (z₁ := (10000000000000000 / 3947900354902869 : ℚ))
      (z₂ := (125000000000000 / 657983392483811 : ℚ))
      (L := (1448439394055990394649 / 10000000000000000000000 : ℚ))
      (U := (-(18233481457763565163467 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_203 :
    ((1452276443906651095289 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18206049303829734797543 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1976757231857117 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1882462954591030446627 / 5000000000000000000000 : ℝ)) -
              6 * (937384263878327770559 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (20006754066941 / 128000000000000 : ℝ) := by
  have hL1 :
    (1452276443906651095289 / 10000000000000000000000 : ℝ) ≤
      Real.log (148006754066941 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (148006754066941 / 128000000000000 : ℚ))
        (L := (1452276443906651095289 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (20726754066941 / 128000000000000 : ℝ) ≤
      (-(18206049303829734797543 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (20726754066941 / 128000000000000 : ℚ))
        (r' := (20726754066941 / 16000000000000 : ℚ))
        (U := (-(18206049303829734797543 / 10000000000000000000000 : ℚ)))
        (U' := (2588366105170265202457 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by constructor <;> norm_num)
  have hau265 :
    Real.arctan (3953514463714237 / 10000000000000000 : ℝ) ≤
      (1882462954591030446627 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3953514463714237 / 10000000000000000 : ℚ))
        (U := (1882462954591030446627 / 5000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1882462954591030446627 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 3953514463714237 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 3953514463714237 : ℝ) =
              (3953514463714237 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau265)
  have hat2 :
    Real.arctan (375000000000000 / 1976757231857117 : ℝ) ≤
      (937384263878327770559 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 1976757231857117 : ℚ))
        (U := (937384263878327770559 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (20006754066941 / 128000000000000 : ℚ))
      (lo := (1976757231857117 / 5000000000000000 : ℚ))
      (hi := (3953514463714237 / 10000000000000000 : ℚ))
      (s := (1976757231857117 / 5000000000000000 : ℚ))
      (r₁ := (148006754066941 / 128000000000000 : ℚ))
      (r₂ := (20726754066941 / 128000000000000 : ℚ))
      (z₁ := (10000000000000000 / 3953514463714237 : ℚ))
      (z₂ := (375000000000000 / 1976757231857117 : ℚ))
      (L := (1452276443906651095289 / 10000000000000000000000 : ℚ))
      (U := (-(18206049303829734797543 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_204 :
    ((145611202202684841337 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(18178692196381109013093 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3959120611619847 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3769773318745880151089 / 10000000000000000000000 : ℝ)) -
              6 * (1872175480431801522837 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (5015883525553 / 32000000000000 : ℝ) := by
  have hL1 :
    (145611202202684841337 / 1000000000000000000000 : ℝ) ≤
      Real.log (37015883525553 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (37015883525553 / 32000000000000 : ℚ))
        (L := (145611202202684841337 / 1000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (5195883525553 / 32000000000000 : ℝ) ≤
      (-(18178692196381109013093 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5195883525553 / 32000000000000 : ℚ))
        (r' := (5195883525553 / 4000000000000 : ℚ))
        (U := (-(18178692196381109013093 / 10000000000000000000000 : ℚ)))
        (U' := (2615723212618890986907 / 10000000000000000000000 : ℚ))
        3 8 (by decide +kernel) (by constructor <;> norm_num)
  have hau266 :
    Real.arctan (79182412232397 / 200000000000000 : ℝ) ≤
      (3769773318745880151089 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (79182412232397 / 200000000000000 : ℚ))
        (U := (3769773318745880151089 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3769773318745880151089 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (200000000000000 / 79182412232397 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (200000000000000 / 79182412232397 : ℝ) =
              (79182412232397 / 200000000000000 : ℝ)
            by
        norm_num];
        exact hau266)
  have hat2 :
    Real.arctan (250000000000000 / 1319706870539949 : ℝ) ≤
      (1872175480431801522837 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1319706870539949 : ℚ))
        (U := (1872175480431801522837 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (5015883525553 / 32000000000000 : ℚ))
      (lo := (3959120611619847 / 10000000000000000 : ℚ))
      (hi := (79182412232397 / 200000000000000 : ℚ))
      (s := (3959120611619847 / 10000000000000000 : ℚ))
      (r₁ := (37015883525553 / 32000000000000 : ℚ))
      (r₂ := (5195883525553 / 32000000000000 : ℚ))
      (z₁ := (200000000000000 / 79182412232397 : ℚ))
      (z₂ := (250000000000000 / 1319706870539949 : ℚ))
      (L := (145611202202684841337 / 1000000000000000000000 : ℚ))
      (U := (-(18178692196381109013093 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
