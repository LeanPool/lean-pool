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

/-! # V29: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma V_349 :
    ((372432974215837231393 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10420961770985507744611 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2945715338232803 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2661991062193999150973 / 10000000000000000000000 : ℝ))) -
              6 * (1266224519414994741439 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (86772388539 / 250000000000 : ℝ) := by
  have hL1 :
    (372432974215837231393 / 1250000000000000000000 : ℝ) ≤
      Real.log (336772388539 / 250000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (336772388539 / 250000000000 : ℚ))
        (L := (372432974215837231393 / 1250000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hU2 :
    Real.log (88178638539 / 250000000000 : ℝ) ≤
      (-(10420961770985507744611 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (88178638539 / 250000000000 : ℚ))
        (r' := (88178638539 / 62500000000 : ℚ))
        (U := (-(10420961770985507744611 / 10000000000000000000000 : ℚ)))
        (U' := (3441981835014492255389 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by constructor <;> norm_num)
  have hau470 :
    Real.arctan (5891430676465609 / 21606418716193208 : ℝ) ≤
      (2661991062193999150973 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5891430676465609 / 21606418716193208 : ℚ))
        (U := (2661991062193999150973 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau469 :
    Real.arctan (5891430676465609 / 10000000000000000 : ℝ) ≤
      (2 * (2661991062193999150973 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1450802339524151 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (5891430676465609 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5891430676465609 / 10000000000000000 : ℝ) /
                (1 + (1450802339524151 / 1250000000000000 : ℝ)) =
              (5891430676465609 / 21606418716193208 : ℝ)
            by
        norm_num];
        exact hau470)
  have hat1 :
    (Real.pi / 2 - (2 * (2661991062193999150973 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5891430676465609 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5891430676465609 : ℝ) =
              (5891430676465609 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau469)
  have hat2 :
    Real.arctan (375000000000000 / 2945715338232803 : ℝ) ≤
      (1266224519414994741439 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 2945715338232803 : ℚ))
        (U := (1266224519414994741439 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (86772388539 / 250000000000 : ℚ))
      (lo := (2945715338232803 / 5000000000000000 : ℚ))
      (hi := (5891430676465609 / 10000000000000000 : ℚ))
      (s := (2945715338232803 / 5000000000000000 : ℚ))
      (r₁ := (336772388539 / 250000000000 : ℚ))
      (r₂ := (88178638539 / 250000000000 : ℚ))
      (z₁ := (10000000000000000 / 5891430676465609 : ℚ))
      (z₂ := (375000000000000 / 2945715338232803 : ℚ))
      (L := (372432974215837231393 / 1250000000000000000000 : ℚ))
      (U := (-(10420961770985507744611 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_350 :
    ((119954631949475568979 / 400000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10347063308137192662121 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2956796049364893 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1335104378906465501497 / 5000000000000000000000 : ℝ))) -
              6 * (630764785401862489949 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (11190582883251 / 32000000000000 : ℝ) := by
  have hL1 :
    (119954631949475568979 / 400000000000000000000 : ℝ) ≤
      Real.log (43190582883251 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (43190582883251 / 32000000000000 : ℚ))
        (L := (119954631949475568979 / 400000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (11370582883251 / 32000000000000 : ℝ) ≤
      (-(10347063308137192662121 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11370582883251 / 32000000000000 : ℚ))
        (r' := (11370582883251 / 8000000000000 : ℚ))
        (U := (-(10347063308137192662121 / 10000000000000000000000 : ℚ)))
        (U' := (3515880297862807337879 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by constructor <;> norm_num)
  have hau472 :
    Real.arctan (5913592098729789 / 21617683569032140 : ℝ) ≤
      (1335104378906465501497 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5913592098729789 / 21617683569032140 : ℚ))
        (U := (1335104378906465501497 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau471 :
    Real.arctan (5913592098729789 / 10000000000000000 : ℝ) ≤
      (2 * (1335104378906465501497 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (580884178451607 / 500000000000000 : ℝ) ≤
          Real.sqrt (1 + (5913592098729789 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5913592098729789 / 10000000000000000 : ℝ) /
                (1 + (580884178451607 / 500000000000000 : ℝ)) =
              (5913592098729789 / 21617683569032140 : ℝ)
            by
        norm_num];
        exact hau472)
  have hat1 :
    (Real.pi / 2 - (2 * (1335104378906465501497 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5913592098729789 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5913592098729789 : ℝ) =
              (5913592098729789 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau471)
  have hat2 :
    Real.arctan (125000000000000 / 985598683121631 : ℝ) ≤
      (630764785401862489949 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (125000000000000 / 985598683121631 : ℚ))
        (U := (630764785401862489949 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (11190582883251 / 32000000000000 : ℚ))
      (lo := (2956796049364893 / 5000000000000000 : ℚ))
      (hi := (5913592098729789 / 10000000000000000 : ℚ))
      (s := (2956796049364893 / 5000000000000000 : ℚ))
      (r₁ := (43190582883251 / 32000000000000 : ℚ))
      (r₂ := (11370582883251 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 5913592098729789 : ℚ))
      (z₂ := (125000000000000 / 985598683121631 : ℚ))
      (L := (119954631949475568979 / 400000000000000000000 : ℚ))
      (U := (-(10347063308137192662121 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_351 :
    ((3018230232850539159649 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2568426735005533212383 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5935670779677621 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (334797489789192552847 / 1250000000000000000000 : ℝ))) -
              6 * (628443231648490909653 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1127430003351 / 3200000000000 : ℝ) := by
  have hL1 :
    (3018230232850539159649 / 10000000000000000000000 : ℝ) ≤
      Real.log (4327430003351 / 3200000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (4327430003351 / 3200000000000 : ℚ))
        (L := (3018230232850539159649 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (1145430003351 / 3200000000000 : ℝ) ≤
      (-(2568426735005533212383 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1145430003351 / 3200000000000 : ℚ))
        (r' := (1145430003351 / 800000000000 : ℚ))
        (U := (-(2568426735005533212383 / 2500000000000000000000 : ℚ)))
        (U' := (897309166494466787617 / 2500000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by constructor <;> norm_num)
  have hau474 :
    Real.arctan (5935670779677624 / 21628937509709077 : ℝ) ≤
      (334797489789192552847 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5935670779677624 / 21628937509709077 : ℚ))
        (U := (334797489789192552847 / 1250000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau473 :
    Real.arctan (741958847459703 / 1250000000000000 : ℝ) ≤
      (2 * (334797489789192552847 / 1250000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11628937509709077 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (741958847459703 / 1250000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (741958847459703 / 1250000000000000 : ℝ) /
                (1 + (11628937509709077 / 10000000000000000 : ℝ)) =
              (5935670779677624 / 21628937509709077 : ℝ)
            by
        norm_num];
        exact hau474)
  have hat1 :
    (Real.pi / 2 - (2 * (334797489789192552847 / 1250000000000000000000 : ℝ))) ≤
      Real.arctan (1250000000000000 / 741958847459703 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 741958847459703 : ℝ) =
              (741958847459703 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau473)
  have hat2 :
    Real.arctan (250000000000000 / 1978556926559207 : ℝ) ≤
      (628443231648490909653 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1978556926559207 : ℚ))
        (U := (628443231648490909653 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1127430003351 / 3200000000000 : ℚ))
      (lo := (5935670779677621 / 10000000000000000 : ℚ))
      (hi := (741958847459703 / 1250000000000000 : ℚ))
      (s := (5935670779677621 / 10000000000000000 : ℚ))
      (r₁ := (4327430003351 / 3200000000000 : ℚ))
      (r₂ := (1145430003351 / 3200000000000 : ℚ))
      (z₁ := (1250000000000000 / 741958847459703 : ℚ))
      (z₂ := (250000000000000 / 1978556926559207 : ℚ))
      (L := (3018230232850539159649 / 10000000000000000000000 : ℚ))
      (U := (-(2568426735005533212383 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_352 :
    ((759389310323588584061 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10200884771266944986441 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5957667639208997 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2686505063364219207891 / 10000000000000000000000 : ℝ))) -
              6 * (1252294249803677508751 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (11358017183769 / 32000000000000 : ℝ) := by
  have hL1 :
    (759389310323588584061 / 2500000000000000000000 : ℝ) ≤
      Real.log (43358017183769 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (43358017183769 / 32000000000000 : ℚ))
        (L := (759389310323588584061 / 2500000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (11538017183769 / 32000000000000 : ℝ) ≤
      (-(10200884771266944986441 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11538017183769 / 32000000000000 : ℚ))
        (r' := (11538017183769 / 8000000000000 : ℚ))
        (U := (-(10200884771266944986441 / 10000000000000000000000 : ℚ)))
        (U' := (3662058834733055013559 / 10000000000000000000000 : ℚ))
        2 9 (by decide +kernel) (by constructor <;> norm_num)
  have hau476 :
    Real.arctan (2978833819604500 / 10820090284937127 : ℝ) ≤
      (2686505063364219207891 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2978833819604500 / 10820090284937127 : ℚ))
        (U := (2686505063364219207891 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau475 :
    Real.arctan (5957667639209 / 10000000000000 : ℝ) ≤
      (2 * (2686505063364219207891 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5820090284937127 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (5957667639209 / 10000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5957667639209 / 10000000000000 : ℝ) /
                (1 + (5820090284937127 / 5000000000000000 : ℝ)) =
              (2978833819604500 / 10820090284937127 : ℝ)
            by
        norm_num];
        exact hau476)
  have hat1 :
    (Real.pi / 2 - (2 * (2686505063364219207891 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000 / 5957667639209 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000 / 5957667639209 : ℝ) = (5957667639209 / 10000000000000 : ℝ)
            by
        norm_num];
        exact hau475)
  have hat2 :
    Real.arctan (750000000000000 / 5957667639208997 : ℝ) ≤
      (1252294249803677508751 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 5957667639208997 : ℚ))
        (U := (1252294249803677508751 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (11358017183769 / 32000000000000 : ℚ))
      (lo := (5957667639208997 / 10000000000000000 : ℚ))
      (hi := (5957667639209 / 10000000000000 : ℚ))
      (s := (5957667639208997 / 10000000000000000 : ℚ))
      (r₁ := (43358017183769 / 32000000000000 : ℚ))
      (r₂ := (11538017183769 / 32000000000000 : ℚ))
      (z₁ := (10000000000000 / 5957667639209 : ℚ))
      (z₂ := (750000000000000 / 5957667639208997 : ℚ))
      (L := (759389310323588584061 / 2500000000000000000000 : ℚ))
      (U := (-(10200884771266944986441 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_353 :
    ((2437765404834750633 / 8000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5082335795652477889393 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((596863566877371 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1345275269978941688457 / 5000000000000000000000 : ℝ))) -
              6 * (1250016938943352110893 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (22799751517797 / 64000000000000 : ℝ) := by
  have hL1 :
    (2437765404834750633 / 8000000000000000000 : ℝ) ≤
      Real.log (86799751517797 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (86799751517797 / 64000000000000 : ℚ))
        (L := (2437765404834750633 / 8000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (23159751517797 / 64000000000000 : ℝ) ≤
      (-(5082335795652477889393 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23159751517797 / 64000000000000 : ℚ))
        (r' := (23159751517797 / 16000000000000 : ℚ))
        (U := (-(5082335795652477889393 / 5000000000000000000000 : ℚ)))
        (U' := (1849136007347522110607 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau478 :
    Real.arctan (5968635668773713 / 21645798029613848 : ℝ) ≤
      (1345275269978941688457 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5968635668773713 / 21645798029613848 : ℚ))
        (U := (1345275269978941688457 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau477 :
    Real.arctan (5968635668773713 / 10000000000000000 : ℝ) ≤
      (2 * (1345275269978941688457 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1455724753701731 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (5968635668773713 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (5968635668773713 / 10000000000000000 : ℝ) /
                (1 + (1455724753701731 / 1250000000000000 : ℝ)) =
              (5968635668773713 / 21645798029613848 : ℝ)
            by
        norm_num];
        exact hau478)
  have hat1 :
    (Real.pi / 2 - (2 * (1345275269978941688457 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 5968635668773713 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 5968635668773713 : ℝ) =
              (5968635668773713 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau477)
  have hat2 :
    Real.arctan (25000000000000 / 198954522292457 : ℝ) ≤
      (1250016938943352110893 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (25000000000000 / 198954522292457 : ℚ))
        (U := (1250016938943352110893 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (22799751517797 / 64000000000000 : ℚ))
      (lo := (596863566877371 / 1000000000000000 : ℚ))
      (hi := (5968635668773713 / 10000000000000000 : ℚ))
      (s := (596863566877371 / 1000000000000000 : ℚ))
      (r₁ := (86799751517797 / 64000000000000 : ℚ))
      (r₂ := (23159751517797 / 64000000000000 : ℚ))
      (z₁ := (10000000000000000 / 5968635668773713 : ℚ))
      (z₂ := (25000000000000 / 198954522292457 : ℚ))
      (L := (2437765404834750633 / 8000000000000000000 : ℚ))
      (U := (-(5082335795652477889393 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_354 :
    ((3056846968454616536319 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(10128589077740964565741 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5979583580303689 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1347292351694098581751 / 5000000000000000000000 : ℝ))) -
              6 * (623876003640546214071 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (2860433583507 / 8000000000000 : ℝ) := by
  have hL1 :
    (3056846968454616536319 / 10000000000000000000000 : ℝ) ≤
      Real.log (10860433583507 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (10860433583507 / 8000000000000 : ℚ))
        (L := (3056846968454616536319 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (2905433583507 / 8000000000000 : ℝ) ≤
      (-(10128589077740964565741 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2905433583507 / 8000000000000 : ℚ))
        (r' := (2905433583507 / 2000000000000 : ℚ))
        (U := (-(10128589077740964565741 / 10000000000000000000000 : ℚ)))
        (U' := (3734354528259035434259 / 10000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau480 :
    Real.arctan (1494895895075923 / 5412853195256301 : ℝ) ≤
      (1347292351694098581751 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1494895895075923 / 5412853195256301 : ℚ))
        (U := (1347292351694098581751 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau479 :
    Real.arctan (1494895895075923 / 2500000000000000 : ℝ) ≤
      (2 * (1347292351694098581751 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2912853195256301 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (1494895895075923 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1494895895075923 / 2500000000000000 : ℝ) /
                (1 + (2912853195256301 / 2500000000000000 : ℝ)) =
              (1494895895075923 / 5412853195256301 : ℝ)
            by
        norm_num];
        exact hau480)
  have hat1 :
    (Real.pi / 2 - (2 * (1347292351694098581751 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1494895895075923 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1494895895075923 : ℝ) =
              (1494895895075923 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau479)
  have hat2 :
    Real.arctan (750000000000000 / 5979583580303689 : ℝ) ≤
      (623876003640546214071 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 5979583580303689 : ℚ))
        (U := (623876003640546214071 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2860433583507 / 8000000000000 : ℚ))
      (lo := (5979583580303689 / 10000000000000000 : ℚ))
      (hi := (1494895895075923 / 2500000000000000 : ℚ))
      (s := (5979583580303689 / 10000000000000000 : ℚ))
      (r₁ := (10860433583507 / 8000000000000 : ℚ))
      (r₂ := (2905433583507 / 8000000000000 : ℚ))
      (z₁ := (2500000000000000 / 1494895895075923 : ℚ))
      (z₂ := (750000000000000 / 5979583580303689 : ℚ))
      (L := (3056846968454616536319 / 10000000000000000000000 : ℚ))
      (U := (-(10128589077740964565741 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_355 :
    ((766619474111480287379 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(5046318145504354096527 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((5990511484098597 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1349303808025649067077 / 5000000000000000000000 : ℝ))) -
              6 * (1245499343066240103687 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (4593437163663 / 12800000000000 : ℝ) := by
  have hL1 :
    (766619474111480287379 / 2500000000000000000000 : ℝ) ≤
      Real.log (17393437163663 / 12800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (17393437163663 / 12800000000000 : ℚ))
        (L := (766619474111480287379 / 2500000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (4665437163663 / 12800000000000 : ℝ) ≤
      (-(5046318145504354096527 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4665437163663 / 12800000000000 : ℚ))
        (r' := (4665437163663 / 3200000000000 : ℚ))
        (U := (-(5046318145504354096527 / 5000000000000000000000 : ℚ)))
        (U' := (1885153657495645903473 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau482 :
    Real.arctan (5990511484098600 / 21657024828021821 : ℝ) ≤
      (1349303808025649067077 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (5990511484098600 / 21657024828021821 : ℚ))
        (U := (1349303808025649067077 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau481 :
    Real.arctan (29952557420493 / 50000000000000 : ℝ) ≤
      (2 * (1349303808025649067077 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11657024828021821 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (29952557420493 / 50000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (29952557420493 / 50000000000000 : ℝ) /
                (1 + (11657024828021821 / 10000000000000000 : ℝ)) =
              (5990511484098600 / 21657024828021821 : ℝ)
            by
        norm_num];
        exact hau482)
  have hat1 :
    (Real.pi / 2 - (2 * (1349303808025649067077 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (50000000000000 / 29952557420493 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (50000000000000 / 29952557420493 : ℝ) =
              (29952557420493 / 50000000000000 : ℝ)
            by
        norm_num];
        exact hau481)
  have hat2 :
    Real.arctan (250000000000000 / 1996837161366199 : ℝ) ≤
      (1245499343066240103687 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1996837161366199 : ℚ))
        (U := (1245499343066240103687 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4593437163663 / 12800000000000 : ℚ))
      (lo := (5990511484098597 / 10000000000000000 : ℚ))
      (hi := (29952557420493 / 50000000000000 : ℚ))
      (s := (5990511484098597 / 10000000000000000 : ℚ))
      (r₁ := (17393437163663 / 12800000000000 : ℚ))
      (r₂ := (4665437163663 / 12800000000000 : ℚ))
      (z₁ := (50000000000000 / 29952557420493 : ℚ))
      (z₂ := (250000000000000 / 1996837161366199 : ℚ))
      (L := (766619474111480287379 / 2500000000000000000000 : ℚ))
      (U := (-(5046318145504354096527 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_356 :
    ((3076099557883663825427 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2514203075409914914533 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6001419489453879 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2702619339793887572677 / 10000000000000000000000 : ℝ))) -
              6 * (310814708988853740969 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (11525451484287 / 32000000000000 : ℝ) := by
  have hL1 :
    (3076099557883663825427 / 10000000000000000000000 : ℝ) ≤
      Real.log (43525451484287 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (43525451484287 / 32000000000000 : ℚ))
        (L := (3076099557883663825427 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (11705451484287 / 32000000000000 : ℝ) ≤
      (-(2514203075409914914533 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (11705451484287 / 32000000000000 : ℚ))
        (r' := (11705451484287 / 8000000000000 : ℚ))
        (U := (-(2514203075409914914533 / 2500000000000000000000 : ℚ)))
        (U' := (951532826090085085467 / 2500000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau484 :
    Real.arctan (3000709744726941 / 10831317087253892 : ℝ) ≤
      (2702619339793887572677 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3000709744726941 / 10831317087253892 : ℚ))
        (U := (2702619339793887572677 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau483 :
    Real.arctan (3000709744726941 / 5000000000000000 : ℝ) ≤
      (2 * (2702619339793887572677 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1457829271813473 / 1250000000000000 : ℝ) ≤
          Real.sqrt (1 + (3000709744726941 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3000709744726941 / 5000000000000000 : ℝ) /
                (1 + (1457829271813473 / 1250000000000000 : ℝ)) =
              (3000709744726941 / 10831317087253892 : ℝ)
            by
        norm_num];
        exact hau484)
  have hat1 :
    (Real.pi / 2 - (2 * (2702619339793887572677 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3000709744726941 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3000709744726941 : ℝ) =
              (3000709744726941 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau483)
  have hat2 :
    Real.arctan (250000000000000 / 2000473163151293 : ℝ) ≤
      (310814708988853740969 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2000473163151293 : ℚ))
        (U := (310814708988853740969 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (11525451484287 / 32000000000000 : ℚ))
      (lo := (6001419489453879 / 10000000000000000 : ℚ))
      (hi := (3000709744726941 / 5000000000000000 : ℚ))
      (s := (6001419489453879 / 10000000000000000 : ℚ))
      (r₁ := (43525451484287 / 32000000000000 : ℚ))
      (r₂ := (11705451484287 / 32000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3000709744726941 : ℚ))
      (z₂ := (250000000000000 / 2000473163151293 : ℚ))
      (L := (3076099557883663825427 / 10000000000000000000000 : ℚ))
      (U := (-(2514203075409914914533 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_357 :
    ((3085711970582634738283 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1252639523764855944051 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3006153852336759 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2 * (8458187299750094947 / 31250000000000000000 : ℝ))) -
              6 * (620515188494905216727 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (23134620118833 / 64000000000000 : ℝ) := by
  have hL1 :
    (3085711970582634738283 / 10000000000000000000000 : ℝ) ≤
      Real.log (87134620118833 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (87134620118833 / 64000000000000 : ℚ))
        (L := (3085711970582634738283 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (23494620118833 / 64000000000000 : ℝ) ≤
      (-(1252639523764855944051 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23494620118833 / 64000000000000 : ℚ))
        (r' := (23494620118833 / 16000000000000 : ℚ))
        (U := (-(1252639523764855944051 / 1250000000000000000000 : ℚ)))
        (U' := (480228426985144055949 / 1250000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau486 :
    Real.arctan (6012307704673521 / 21668240824377793 : ℝ) ≤
      (8458187299750094947 / 31250000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6012307704673521 / 21668240824377793 : ℚ))
        (U := (8458187299750094947 / 31250000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau485 :
    Real.arctan (6012307704673521 / 10000000000000000 : ℝ) ≤
      (2 * (8458187299750094947 / 31250000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11668240824377793 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6012307704673521 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6012307704673521 / 10000000000000000 : ℝ) /
                (1 + (11668240824377793 / 10000000000000000 : ℝ)) =
              (6012307704673521 / 21668240824377793 : ℝ)
            by
        norm_num];
        exact hau486)
  have hat1 :
    (Real.pi / 2 - (2 * (8458187299750094947 / 31250000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6012307704673521 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6012307704673521 : ℝ) =
              (6012307704673521 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau485)
  have hat2 :
    Real.arctan (125000000000000 / 1002051284112253 : ℝ) ≤
      (620515188494905216727 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (125000000000000 / 1002051284112253 : ℚ))
        (U := (620515188494905216727 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (23134620118833 / 64000000000000 : ℚ))
      (lo := (3006153852336759 / 5000000000000000 : ℚ))
      (hi := (6012307704673521 / 10000000000000000 : ℚ))
      (s := (3006153852336759 / 5000000000000000 : ℚ))
      (r₁ := (87134620118833 / 64000000000000 : ℚ))
      (r₂ := (23494620118833 / 64000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6012307704673521 : ℚ))
      (z₂ := (125000000000000 / 1002051284112253 : ℚ))
      (L := (3085711970582634738283 / 10000000000000000000000 : ℚ))
      (U := (-(1252639523764855944051 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_358 :
    ((773828788076575112559 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4992773523371619840171 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((6023176237082577 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1355304732598921570641 / 5000000000000000000000 : ℝ))) -
              6 * (1238813858572936387099 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (5804584317273 / 16000000000000 : ℝ) := by
  have hL1 :
    (773828788076575112559 / 2500000000000000000000 : ℝ) ≤
      Real.log (21804584317273 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (21804584317273 / 16000000000000 : ℚ))
        (L := (773828788076575112559 / 2500000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (5894584317273 / 16000000000000 : ℝ) ≤
      (-(4992773523371619840171 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5894584317273 / 16000000000000 : ℚ))
        (r' := (5894584317273 / 4000000000000 : ℚ))
        (U := (-(4992773523371619840171 / 5000000000000000000000 : ℚ)))
        (U' := (1938698279628380159829 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau488 :
    Real.arctan (1003862706180430 / 3612307463586199 : ℝ) ≤
      (1355304732598921570641 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1003862706180430 / 3612307463586199 : ℚ))
        (U := (1355304732598921570641 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau487 :
    Real.arctan (301158811854129 / 500000000000000 : ℝ) ≤
      (2 * (1355304732598921570641 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (5836922390758597 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (301158811854129 / 500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (301158811854129 / 500000000000000 : ℝ) /
                (1 + (5836922390758597 / 5000000000000000 : ℝ)) =
              (1003862706180430 / 3612307463586199 : ℝ)
            by
        norm_num];
        exact hau488)
  have hat1 :
    (Real.pi / 2 - (2 * (1355304732598921570641 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (500000000000000 / 301158811854129 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (500000000000000 / 301158811854129 : ℝ) =
              (301158811854129 / 500000000000000 : ℝ)
            by
        norm_num];
        exact hau487)
  have hat2 :
    Real.arctan (250000000000000 / 2007725412360859 : ℝ) ≤
      (1238813858572936387099 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 2007725412360859 : ℚ))
        (U := (1238813858572936387099 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (5804584317273 / 16000000000000 : ℚ))
      (lo := (6023176237082577 / 10000000000000000 : ℚ))
      (hi := (301158811854129 / 500000000000000 : ℚ))
      (s := (6023176237082577 / 10000000000000000 : ℚ))
      (r₁ := (21804584317273 / 16000000000000 : ℚ))
      (r₂ := (5894584317273 / 16000000000000 : ℚ))
      (z₁ := (500000000000000 / 301158811854129 : ℚ))
      (z₂ := (250000000000000 / 2007725412360859 : ℚ))
      (L := (773828788076575112559 / 2500000000000000000000 : ℚ))
      (U := (-(4992773523371619840171 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_359 :
    ((620022657417898369221 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(498390490323817900053 / 500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((602860315550759 / 1000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (542520019722747216779 / 2000000000000000000000 : ℝ))) -
              6 * (1237710043813499311807 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (46520391688443 / 128000000000000 : ℝ) := by
  have hL1 :
    (620022657417898369221 / 2000000000000000000000 : ℝ) ≤
      Real.log (174520391688443 / 128000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (174520391688443 / 128000000000000 : ℚ))
        (L := (620022657417898369221 / 2000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (47240391688443 / 128000000000000 : ℝ) ≤
      (-(498390490323817900053 / 500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (47240391688443 / 128000000000000 : ℚ))
        (r' := (47240391688443 / 32000000000000 : ℚ))
        (U := (-(498390490323817900053 / 500000000000000000000 : ℚ)))
        (U' := (194756689976182099947 / 500000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau490 :
    Real.arctan (6028603155507593 / 21676645751524539 : ℝ) ≤
      (542520019722747216779 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (6028603155507593 / 21676645751524539 : ℚ))
        (U := (542520019722747216779 / 2000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau489 :
    Real.arctan (6028603155507593 / 10000000000000000 : ℝ) ≤
      (2 * (542520019722747216779 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (11676645751524539 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (6028603155507593 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (6028603155507593 / 10000000000000000 : ℝ) /
                (1 + (11676645751524539 / 10000000000000000 : ℝ)) =
              (6028603155507593 / 21676645751524539 : ℝ)
            by
        norm_num];
        exact hau490)
  have hat1 :
    (Real.pi / 2 - (2 * (542520019722747216779 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 6028603155507593 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 6028603155507593 : ℝ) =
              (6028603155507593 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau489)
  have hat2 :
    Real.arctan (75000000000000 / 602860315550759 : ℝ) ≤
      (1237710043813499311807 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (75000000000000 / 602860315550759 : ℚ))
        (U := (1237710043813499311807 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (46520391688443 / 128000000000000 : ℚ))
      (lo := (602860315550759 / 1000000000000000 : ℚ))
      (hi := (6028603155507593 / 10000000000000000 : ℚ))
      (s := (602860315550759 / 1000000000000000 : ℚ))
      (r₁ := (174520391688443 / 128000000000000 : ℚ))
      (r₂ := (47240391688443 / 128000000000000 : ℚ))
      (z₁ := (10000000000000000 / 6028603155507593 : ℚ))
      (z₂ := (75000000000000 / 602860315550759 : ℚ))
      (L := (620022657417898369221 / 2000000000000000000000 : ℚ))
      (U := (-(498390490323817900053 / 500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_360 :
    ((3104909120767000870261 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4975051985741318175863 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1206805038607909 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (2714587987866077907253 / 10000000000000000000000 : ℝ))) -
              6 * (1236609174448796264479 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (23302054419351 / 64000000000000 : ℝ) := by
  have hL1 :
    (3104909120767000870261 / 10000000000000000000000 : ℝ) ≤
      Real.log (87302054419351 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (87302054419351 / 64000000000000 : ℚ))
        (L := (3104909120767000870261 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hU2 :
    Real.log (23662054419351 / 64000000000000 : ℝ) ≤
      (-(4975051985741318175863 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (23662054419351 / 64000000000000 : ℚ))
        (r' := (23662054419351 / 16000000000000 : ℚ))
        (U := (-(4975051985741318175863 / 5000000000000000000000 : ℚ)))
        (U' := (1956419817258681824137 / 5000000000000000000000 : ℚ))
        2 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau492 :
    Real.arctan (1508506298259887 / 5419861512450504 : ℝ) ≤
      (2714587987866077907253 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1508506298259887 / 5419861512450504 : ℚ))
        (U := (2714587987866077907253 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hau491 :
    Real.arctan (1508506298259887 / 2500000000000000 : ℝ) ≤
      (2 * (2714587987866077907253 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (364982689056313 / 312500000000000 : ℝ) ≤
          Real.sqrt (1 + (1508506298259887 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1508506298259887 / 2500000000000000 : ℝ) /
                (1 + (364982689056313 / 312500000000000 : ℝ)) =
              (1508506298259887 / 5419861512450504 : ℝ)
            by
        norm_num];
        exact hau492)
  have hat1 :
    (Real.pi / 2 - (2 * (2714587987866077907253 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1508506298259887 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1508506298259887 : ℝ) =
              (1508506298259887 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau491)
  have hat2 :
    Real.arctan (150000000000000 / 1206805038607909 : ℝ) ≤
      (1236609174448796264479 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 1206805038607909 : ℚ))
        (U := (1236609174448796264479 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (23302054419351 / 64000000000000 : ℚ))
      (lo := (1206805038607909 / 2000000000000000 : ℚ))
      (hi := (1508506298259887 / 2500000000000000 : ℚ))
      (s := (1206805038607909 / 2000000000000000 : ℚ))
      (r₁ := (87302054419351 / 64000000000000 : ℚ))
      (r₂ := (23662054419351 / 64000000000000 : ℚ))
      (z₁ := (2500000000000000 / 1508506298259887 : ℚ))
      (z₂ := (150000000000000 / 1206805038607909 : ℚ))
      (L := (3104909120767000870261 / 10000000000000000000000 : ℚ))
      (U := (-(4975051985741318175863 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
