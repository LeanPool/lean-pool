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

/-! # V01: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma V_13 :
    ((2838708958444624399 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51312936940985871685561 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((84248322090117 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (168480700868393777449 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (138120555504676214793 / 625000000000000000000 : ℝ))))) ≤
      Vfield (283911191 / 1000000000000 : ℝ) := by
  have hL1 :
    (2838708958444624399 / 10000000000000000000000 : ℝ) ≤
      Real.log (1000283911191 / 1000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1000283911191 / 1000000000000 : ℚ))
        (L := (2838708958444624399 / 10000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (5908911191 / 1000000000000 : ℝ) ≤
      (-(51312936940985871685561 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5908911191 / 1000000000000 : ℚ))
        (r' := (5908911191 / 3906250000 : ℚ))
        (U := (-(51312936940985871685561 / 10000000000000000000000 : ℚ)))
        (U' := (4138837483014128314439 / 10000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau27 :
    Real.arctan (84248322090117 / 5000000000000000 : ℝ) ≤
      (168480700868393777449 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (84248322090117 / 5000000000000000 : ℚ))
        (U := (168480700868393777449 / 10000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (168480700868393777449 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 84248322090117 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 84248322090117 : ℝ) =
              (84248322090117 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau27)
  have hal28 :
    (138120555504676214793 / 625000000000000000000 : ℝ) ≤
      Real.arctan (56165548060077 / 250000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (56165548060077 / 250000000000000 : ℚ))
        (L := (138120555504676214793 / 625000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat2 :
    Real.arctan (250000000000000 / 56165548060077 : ℝ) ≤
      (Real.pi / 2 - (138120555504676214793 / 625000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 56165548060077 : ℝ) =
              (56165548060077 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hal28)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (283911191 / 1000000000000 : ℚ))
      (lo := (168496644180231 / 10000000000000000 : ℚ))
      (hi := (84248322090117 / 5000000000000000 : ℚ))
      (s := (84248322090117 / 5000000000000000 : ℚ))
      (r₁ := (1000283911191 / 1000000000000 : ℚ))
      (r₂ := (5908911191 / 1000000000000 : ℚ))
      (z₁ := (5000000000000000 / 84248322090117 : ℚ))
      (z₂ := (250000000000000 / 56165548060077 : ℚ))
      (L := (2838708958444624399 / 10000000000000000000000 : ℚ))
      (U := (-(51312936940985871685561 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_14 :
    ((3400600750179924673 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(51218264559151743459197 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((36884571408653 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (46100488200992503859 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (37673974722398950663 / 156250000000000000000 : ℝ))))) ≤
      Vfield (170058951 / 500000000000 : ℝ) := by
  have hL1 :
    (3400600750179924673 / 10000000000000000000000 : ℝ) ≤
      Real.log (500170058951 / 500000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (500170058951 / 500000000000 : ℚ))
        (L := (3400600750179924673 / 10000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (2982558951 / 500000000000 : ℝ) ≤
      (-(51218264559151743459197 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2982558951 / 500000000000 : ℚ))
        (r' := (2982558951 / 1953125000 : ℚ))
        (U := (-(51218264559151743459197 / 10000000000000000000000 : ℚ)))
        (U' := (4233509864848256540803 / 10000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau29 :
    Real.arctan (36884571408653 / 2000000000000000 : ℝ) ≤
      (46100488200992503859 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (36884571408653 / 2000000000000000 : ℚ))
        (U := (46100488200992503859 / 2500000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (46100488200992503859 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 36884571408653 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 36884571408653 : ℝ) =
              (36884571408653 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau29)
  have hal30 :
    (37673974722398950663 / 156250000000000000000 : ℝ) ≤
      Real.arctan (92211428521631 / 375000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (92211428521631 / 375000000000000 : ℚ))
        (L := (37673974722398950663 / 156250000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat2 :
    Real.arctan (375000000000000 / 92211428521631 : ℝ) ≤
      (Real.pi / 2 - (37673974722398950663 / 156250000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (375000000000000 / 92211428521631 : ℝ) =
              (92211428521631 / 375000000000000 : ℝ)
            by
        norm_num];
        exact hal30)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (170058951 / 500000000000 : ℚ))
      (lo := (92211428521631 / 5000000000000000 : ℚ))
      (hi := (36884571408653 / 2000000000000000 : ℚ))
      (s := (36884571408653 / 2000000000000000 : ℚ))
      (r₁ := (500170058951 / 500000000000 : ℚ))
      (r₂ := (2982558951 / 500000000000 : ℚ))
      (z₁ := (2000000000000000 / 36884571408653 : ℚ))
      (z₂ := (375000000000000 / 92211428521631 : ℚ))
      (L := (3400600750179924673 / 10000000000000000000000 : ℚ))
      (U := (-(51218264559151743459197 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_15 :
    ((396246097145057287 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25562240032020096608843 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((24884879099817 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (99526369538609389173 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (324319511825085218099 / 1250000000000000000000 : ℝ))))) ≤
      Vfield (396324613 / 1000000000000 : ℝ) := by
  have hL1 :
    (396246097145057287 / 1000000000000000000000 : ℝ) ≤
      Real.log (1000396324613 / 1000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1000396324613 / 1000000000000 : ℚ))
        (L := (396246097145057287 / 1000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (6021324613 / 1000000000000 : ℝ) ≤
      (-(25562240032020096608843 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6021324613 / 1000000000000 : ℚ))
        (r' := (6021324613 / 3906250000 : ℚ))
        (U := (-(25562240032020096608843 / 5000000000000000000000 : ℚ)))
        (U' := (2163647179979903391157 / 5000000000000000000000 : ℚ))
        8 10 (by decide +kernel) (by constructor <;> norm_num)
  have hau31 :
    Real.arctan (24884879099817 / 1250000000000000 : ℝ) ≤
      (99526369538609389173 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (24884879099817 / 1250000000000000 : ℚ))
        (U := (99526369538609389173 / 5000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (99526369538609389173 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 24884879099817 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 24884879099817 : ℝ) =
              (24884879099817 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau31)
  have hal32 :
    (324319511825085218099 / 1250000000000000000000 : ℝ) ≤
      Real.arctan (66359677599511 / 250000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (66359677599511 / 250000000000000 : ℚ))
        (L := (324319511825085218099 / 1250000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hat2 :
    Real.arctan (250000000000000 / 66359677599511 : ℝ) ≤
      (Real.pi / 2 - (324319511825085218099 / 1250000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 66359677599511 : ℝ) =
              (66359677599511 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hal32)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (396324613 / 1000000000000 : ℚ))
      (lo := (199079032798533 / 10000000000000000 : ℚ))
      (hi := (24884879099817 / 1250000000000000 : ℚ))
      (s := (24884879099817 / 1250000000000000 : ℚ))
      (r₁ := (1000396324613 / 1000000000000 : ℚ))
      (r₂ := (6021324613 / 1000000000000 : ℚ))
      (z₁ := (1250000000000000 / 24884879099817 : ℚ))
      (z₂ := (250000000000000 / 66359677599511 : ℚ))
      (L := (396246097145057287 / 1000000000000000000000 : ℚ))
      (U := (-(25562240032020096608843 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_16 :
    ((2435712931404190679 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25487292403074346048679 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((110369975480201 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (27588013595377272983 / 1250000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (143118806689254327513 / 500000000000000000000 : ℝ))))) ≤
      Vfield (974522519 / 2000000000000 : ℝ) := by
  have hL1 :
    (2435712931404190679 / 5000000000000000000000 : ℝ) ≤
      Real.log (2000974522519 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2000974522519 / 2000000000000 : ℚ))
        (L := (2435712931404190679 / 5000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (12224522519 / 2000000000000 : ℝ) ≤
      (-(25487292403074346048679 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12224522519 / 2000000000000 : ℚ))
        (r' := (12224522519 / 7812500000 : ℚ))
        (U := (-(25487292403074346048679 / 5000000000000000000000 : ℚ)))
        (U' := (2238594808925653951321 / 5000000000000000000000 : ℚ))
        8 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau33 :
    Real.arctan (110369975480201 / 5000000000000000 : ℝ) ≤
      (27588013595377272983 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (110369975480201 / 5000000000000000 : ℚ))
        (U := (27588013595377272983 / 1250000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (27588013595377272983 / 1250000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 110369975480201 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 110369975480201 : ℝ) =
              (110369975480201 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau33)
  have hal34 :
    (143118806689254327513 / 500000000000000000000 : ℝ) ≤
      Real.arctan (220739950960399 / 750000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (220739950960399 / 750000000000000 : ℚ))
        (L := (143118806689254327513 / 500000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hat2 :
    Real.arctan (750000000000000 / 220739950960399 : ℝ) ≤
      (Real.pi / 2 - (143118806689254327513 / 500000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 220739950960399 : ℝ) =
              (220739950960399 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal34)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (974522519 / 2000000000000 : ℚ))
      (lo := (220739950960399 / 10000000000000000 : ℚ))
      (hi := (110369975480201 / 5000000000000000 : ℚ))
      (s := (110369975480201 / 5000000000000000 : ℚ))
      (r₁ := (2000974522519 / 2000000000000 : ℚ))
      (r₂ := (12224522519 / 2000000000000 : ℚ))
      (z₁ := (5000000000000000 / 110369975480201 : ℚ))
      (z₂ := (750000000000000 / 220739950960399 : ℚ))
      (L := (2435712931404190679 / 5000000000000000000000 : ℚ))
      (U := (-(25487292403074346048679 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_17 :
    ((2890154069979049949 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(25413451632679054566369 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((30057182637849 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (120205566586796683229 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (3102561376671980779519 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (289098953 / 500000000000 : ℝ) := by
  have hL1 :
    (2890154069979049949 / 5000000000000000000000 : ℝ) ≤
      Real.log (500289098953 / 500000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (500289098953 / 500000000000 : ℚ))
        (L := (2890154069979049949 / 5000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (3101598953 / 500000000000 : ℝ) ≤
      (-(25413451632679054566369 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3101598953 / 500000000000 : ℚ))
        (r' := (3101598953 / 1953125000 : ℚ))
        (U := (-(25413451632679054566369 / 5000000000000000000000 : ℚ)))
        (U' := (2312435579320945433631 / 5000000000000000000000 : ℚ))
        8 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau35 :
    Real.arctan (30057182637849 / 1250000000000000 : ℝ) ≤
      (120205566586796683229 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (30057182637849 / 1250000000000000 : ℚ))
        (U := (120205566586796683229 / 5000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (120205566586796683229 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 30057182637849 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 30057182637849 : ℝ) =
              (30057182637849 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau35)
  have hal36 :
    (3102561376671980779519 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (80152487034263 / 250000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (80152487034263 / 250000000000000 : ℚ))
        (L := (3102561376671980779519 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hat2 :
    Real.arctan (250000000000000 / 80152487034263 : ℝ) ≤
      (Real.pi / 2 - (3102561376671980779519 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 80152487034263 : ℝ) =
              (80152487034263 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hal36)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (289098953 / 500000000000 : ℚ))
      (lo := (240457461102789 / 10000000000000000 : ℚ))
      (hi := (30057182637849 / 1250000000000000 : ℚ))
      (s := (30057182637849 / 1250000000000000 : ℚ))
      (r₁ := (500289098953 / 500000000000 : ℚ))
      (r₂ := (3101598953 / 500000000000 : ℚ))
      (z₁ := (1250000000000000 / 30057182637849 : ℚ))
      (z₂ := (250000000000000 / 80152487034263 : ℚ))
      (L := (2890154069979049949 / 5000000000000000000000 : ℚ))
      (U := (-(25413451632679054566369 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_18 :
    ((7296953385895796397 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(50585194098875661653047 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((270178021126813 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (54022462008273651983 / 2000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (691531386986268494069 / 2000000000000000000000 : ℝ))))) ≤
      Vfield (729961631 / 1000000000000 : ℝ) := by
  have hL1 :
    (7296953385895796397 / 10000000000000000000000 : ℝ) ≤
      Real.log (1000729961631 / 1000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1000729961631 / 1000000000000 : ℚ))
        (L := (7296953385895796397 / 10000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (6354961631 / 1000000000000 : ℝ) ≤
      (-(50585194098875661653047 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6354961631 / 1000000000000 : ℚ))
        (r' := (6354961631 / 3906250000 : ℚ))
        (U := (-(50585194098875661653047 / 10000000000000000000000 : ℚ)))
        (U' := (4866580325124338346953 / 10000000000000000000000 : ℚ))
        8 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau37 :
    Real.arctan (270178021126813 / 10000000000000000 : ℝ) ≤
      (54022462008273651983 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (270178021126813 / 10000000000000000 : ℚ))
        (U := (54022462008273651983 / 2000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (54022462008273651983 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 270178021126813 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 270178021126813 : ℝ) =
              (270178021126813 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau37)
  have hal38 :
    (691531386986268494069 / 2000000000000000000000 : ℝ) ≤
      Real.arctan (27017802112681 / 75000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (27017802112681 / 75000000000000 : ℚ))
        (L := (691531386986268494069 / 2000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat2 :
    Real.arctan (75000000000000 / 27017802112681 : ℝ) ≤
      (Real.pi / 2 - (691531386986268494069 / 2000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (75000000000000 / 27017802112681 : ℝ) =
              (27017802112681 / 75000000000000 : ℝ)
            by
        norm_num];
        exact hal38)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (729961631 / 1000000000000 : ℚ))
      (lo := (27017802112681 / 1000000000000000 : ℚ))
      (hi := (270178021126813 / 10000000000000000 : ℚ))
      (s := (270178021126813 / 10000000000000000 : ℚ))
      (r₁ := (1000729961631 / 1000000000000 : ℚ))
      (r₂ := (6354961631 / 1000000000000 : ℚ))
      (z₁ := (10000000000000000 / 270178021126813 : ℚ))
      (z₂ := (75000000000000 / 27017802112681 : ℚ))
      (L := (7296953385895796397 / 10000000000000000000000 : ℚ))
      (U := (-(50585194098875661653047 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_19 :
    ((1611037951921033759 / 2000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(50466495663078367309339 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((283873826461689 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (283797610683746791347 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (3618342583696765969299 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (1611686987 / 2000000000000 : ℝ) := by
  have hL1 :
    (1611037951921033759 / 2000000000000000000000 : ℝ) ≤
      Real.log (2001611686987 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2001611686987 / 2000000000000 : ℚ))
        (L := (1611037951921033759 / 2000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (12861686987 / 2000000000000 : ℝ) ≤
      (-(50466495663078367309339 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (12861686987 / 2000000000000 : ℚ))
        (r' := (12861686987 / 7812500000 : ℚ))
        (U := (-(50466495663078367309339 / 10000000000000000000000 : ℚ)))
        (U' := (4985278760921632690661 / 10000000000000000000000 : ℚ))
        8 11 (by decide +kernel) (by constructor <;> norm_num)
  have hau39 :
    Real.arctan (283873826461689 / 10000000000000000 : ℝ) ≤
      (283797610683746791347 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (283873826461689 / 10000000000000000 : ℚ))
        (U := (283797610683746791347 / 10000000000000000000000 : ℚ))
        3 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (283797610683746791347 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 283873826461689 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 283873826461689 : ℝ) =
              (283873826461689 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau39)
  have hal40 :
    (3618342583696765969299 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (47312304410281 / 125000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (47312304410281 / 125000000000000 : ℚ))
        (L := (3618342583696765969299 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hat2 :
    Real.arctan (125000000000000 / 47312304410281 : ℝ) ≤
      (Real.pi / 2 - (3618342583696765969299 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (125000000000000 / 47312304410281 : ℝ) =
              (47312304410281 / 125000000000000 : ℝ)
            by
        norm_num];
        exact hal40)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1611686987 / 2000000000000 : ℚ))
      (lo := (141936913230843 / 5000000000000000 : ℚ))
      (hi := (283873826461689 / 10000000000000000 : ℚ))
      (s := (283873826461689 / 10000000000000000 : ℚ))
      (r₁ := (2001611686987 / 2000000000000 : ℚ))
      (r₂ := (12861686987 / 2000000000000 : ℚ))
      (z₁ := (10000000000000000 / 283873826461689 : ℚ))
      (z₂ := (125000000000000 / 47312304410281 : ℚ))
      (L := (1611037951921033759 / 2000000000000000000000 : ℚ))
      (U := (-(50466495663078367309339 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_20 :
    ((35253474581734419 / 40000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(6293648705936709382501 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((148469302887837 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (74212844787754867117 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (3769825878752123006391 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (220431339 / 250000000000 : ℝ) := by
  have hL1 :
    (35253474581734419 / 40000000000000000000 : ℝ) ≤ Real.log (250220431339 / 250000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (250220431339 / 250000000000 : ℚ))
        (L := (35253474581734419 / 40000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (1626681339 / 250000000000 : ℝ) ≤
      (-(6293648705936709382501 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1626681339 / 250000000000 : ℚ))
        (r' := (1626681339 / 976562500 : ℚ))
        (U := (-(6293648705936709382501 / 1250000000000000000000 : ℚ)))
        (U' := (637823097063290617499 / 1250000000000000000000 : ℚ))
        8 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau41 :
    Real.arctan (148469302887837 / 5000000000000000 : ℝ) ≤
      (74212844787754867117 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (148469302887837 / 5000000000000000 : ℚ))
        (U := (74212844787754867117 / 2500000000000000000000 : ℚ))
        3 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (74212844787754867117 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (5000000000000000 / 148469302887837 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 148469302887837 : ℝ) =
              (148469302887837 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau41)
  have hal42 :
    (3769825878752123006391 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (98979535258557 / 250000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (98979535258557 / 250000000000000 : ℚ))
        (L := (3769825878752123006391 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat2 :
    Real.arctan (250000000000000 / 98979535258557 : ℝ) ≤
      (Real.pi / 2 - (3769825878752123006391 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 98979535258557 : ℝ) =
              (98979535258557 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hal42)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (220431339 / 250000000000 : ℚ))
      (lo := (296938605775671 / 10000000000000000 : ℚ))
      (hi := (148469302887837 / 5000000000000000 : ℚ))
      (s := (148469302887837 / 5000000000000000 : ℚ))
      (r₁ := (250220431339 / 250000000000 : ℚ))
      (r₂ := (1626681339 / 250000000000 : ℚ))
      (z₁ := (5000000000000000 / 148469302887837 : ℚ))
      (z₂ := (250000000000000 / 98979535258557 : ℚ))
      (L := (35253474581734419 / 40000000000000000000 : ℚ))
      (U := (-(6293648705936709382501 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_21 :
    ((2528385230620046493 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(50151154605132541364319 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3180983626569 / 100000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (79497784202311396663 / 2500000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (2005672468682107829937 / 5000000000000000000000 : ℝ))))) ≤
      Vfield (4047462733 / 4000000000000 : ℝ) := by
  have hL1 :
    (2528385230620046493 / 2500000000000000000000 : ℝ) ≤
      Real.log (4004047462733 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (4004047462733 / 4000000000000 : ℚ))
        (L := (2528385230620046493 / 2500000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (26547462733 / 4000000000000 : ℝ) ≤
      (-(50151154605132541364319 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (26547462733 / 4000000000000 : ℚ))
        (r' := (26547462733 / 15625000000 : ℚ))
        (U := (-(50151154605132541364319 / 10000000000000000000000 : ℚ)))
        (U' := (5300619818867458635681 / 10000000000000000000000 : ℚ))
        8 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau43 :
    Real.arctan (3180983626569 / 100000000000000 : ℝ) ≤
      (79497784202311396663 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3180983626569 / 100000000000000 : ℚ))
        (U := (79497784202311396663 / 2500000000000000000000 : ℚ))
        3 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (79497784202311396663 / 2500000000000000000000 : ℝ)) ≤
      Real.arctan (100000000000000 / 3180983626569 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (100000000000000 / 3180983626569 : ℝ) =
              (3180983626569 / 100000000000000 : ℝ)
            by
        norm_num];
        exact hau43)
  have hal44 :
    (2005672468682107829937 / 5000000000000000000000 : ℝ) ≤
      Real.arctan (106032787552299 / 250000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (106032787552299 / 250000000000000 : ℚ))
        (L := (2005672468682107829937 / 5000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat2 :
    Real.arctan (250000000000000 / 106032787552299 : ℝ) ≤
      (Real.pi / 2 - (2005672468682107829937 / 5000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (250000000000000 / 106032787552299 : ℝ) =
              (106032787552299 / 250000000000000 : ℝ)
            by
        norm_num];
        exact hal44)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (4047462733 / 4000000000000 : ℚ))
      (lo := (318098362656897 / 10000000000000000 : ℚ))
      (hi := (3180983626569 / 100000000000000 : ℚ))
      (s := (3180983626569 / 100000000000000 : ℚ))
      (r₁ := (4004047462733 / 4000000000000 : ℚ))
      (r₂ := (26547462733 / 4000000000000 : ℚ))
      (z₁ := (100000000000000 / 3180983626569 : ℚ))
      (z₂ := (250000000000000 / 106032787552299 : ℚ))
      (L := (2528385230620046493 / 2500000000000000000000 : ℚ))
      (U := (-(50151154605132541364319 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_22 :
    ((5706772088353681693 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(24978482657227015538013 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((67587158854327 / 2000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (337807240776056924649 / 10000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (4233370302187970192887 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (2284012021 / 2000000000000 : ℝ) := by
  have hL1 :
    (5706772088353681693 / 5000000000000000000000 : ℝ) ≤
      Real.log (2002284012021 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2002284012021 / 2000000000000 : ℚ))
        (L := (5706772088353681693 / 5000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (13534012021 / 2000000000000 : ℝ) ≤
      (-(24978482657227015538013 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (13534012021 / 2000000000000 : ℚ))
        (r' := (13534012021 / 7812500000 : ℚ))
        (U := (-(24978482657227015538013 / 5000000000000000000000 : ℚ)))
        (U' := (2747404554772984461987 / 5000000000000000000000 : ℚ))
        8 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau45 :
    Real.arctan (67587158854327 / 2000000000000000 : ℝ) ≤
      (337807240776056924649 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (67587158854327 / 2000000000000000 : ℚ))
        (U := (337807240776056924649 / 10000000000000000000000 : ℚ))
        3 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (337807240776056924649 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2000000000000000 / 67587158854327 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 67587158854327 : ℝ) =
              (67587158854327 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau45)
  have hal46 :
    (4233370302187970192887 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (21120987141977 / 46875000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (21120987141977 / 46875000000000 : ℚ))
        (L := (4233370302187970192887 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hat2 :
    Real.arctan (46875000000000 / 21120987141977 : ℝ) ≤
      (Real.pi / 2 - (4233370302187970192887 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (46875000000000 / 21120987141977 : ℝ) =
              (21120987141977 / 46875000000000 : ℝ)
            by
        norm_num];
        exact hal46)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2284012021 / 2000000000000 : ℚ))
      (lo := (21120987141977 / 625000000000000 : ℚ))
      (hi := (67587158854327 / 2000000000000000 : ℚ))
      (s := (67587158854327 / 2000000000000000 : ℚ))
      (r₁ := (2002284012021 / 2000000000000 : ℚ))
      (r₂ := (13534012021 / 2000000000000 : ℚ))
      (z₁ := (2000000000000000 / 67587158854327 : ℚ))
      (z₂ := (46875000000000 / 21120987141977 : ℚ))
      (L := (5706772088353681693 / 5000000000000000000000 : ℚ))
      (U := (-(24978482657227015538013 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_23 :
    ((6356689226027724381 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(12441618812709760022989 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((44583950618293 / 1250000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (178260237063611828863 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (221953446107719388427 / 500000000000000000000 : ℝ))))) ≤
      Vfield (5088585351 / 4000000000000 : ℝ) := by
  have hL1 :
    (6356689226027724381 / 5000000000000000000000 : ℝ) ≤
      Real.log (4005088585351 / 4000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (4005088585351 / 4000000000000 : ℚ))
        (L := (6356689226027724381 / 5000000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (27588585351 / 4000000000000 : ℝ) ≤
      (-(12441618812709760022989 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (27588585351 / 4000000000000 : ℚ))
        (r' := (27588585351 / 15625000000 : ℚ))
        (U := (-(12441618812709760022989 / 2500000000000000000000 : ℚ)))
        (U' := (1421324793290239977011 / 2500000000000000000000 : ℚ))
        8 12 (by decide +kernel) (by constructor <;> norm_num)
  have hau47 :
    Real.arctan (44583950618293 / 1250000000000000 : ℝ) ≤
      (178260237063611828863 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (44583950618293 / 1250000000000000 : ℚ))
        (U := (178260237063611828863 / 5000000000000000000000 : ℚ))
        3 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (178260237063611828863 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1250000000000000 / 44583950618293 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1250000000000000 / 44583950618293 : ℝ) =
              (44583950618293 / 1250000000000000 : ℝ)
            by
        norm_num];
        exact hau47)
  have hal48 :
    (221953446107719388427 / 500000000000000000000 : ℝ) ≤
      Real.arctan (356671604946341 / 750000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (356671604946341 / 750000000000000 : ℚ))
        (L := (221953446107719388427 / 500000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hat2 :
    Real.arctan (750000000000000 / 356671604946341 : ℝ) ≤
      (Real.pi / 2 - (221953446107719388427 / 500000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (750000000000000 / 356671604946341 : ℝ) =
              (356671604946341 / 750000000000000 : ℝ)
            by
        norm_num];
        exact hal48)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (5088585351 / 4000000000000 : ℚ))
      (lo := (356671604946341 / 10000000000000000 : ℚ))
      (hi := (44583950618293 / 1250000000000000 : ℚ))
      (s := (44583950618293 / 1250000000000000 : ℚ))
      (r₁ := (4005088585351 / 4000000000000 : ℚ))
      (r₂ := (27588585351 / 4000000000000 : ℚ))
      (z₁ := (1250000000000000 / 44583950618293 : ℚ))
      (z₂ := (750000000000000 / 356671604946341 : ℚ))
      (L := (6356689226027724381 / 5000000000000000000000 : ℚ))
      (U := (-(12441618812709760022989 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_24 :
    ((350326094811190417 / 250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(49579546107330803619953 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((374471182469361 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (187148145473045818201 / 5000000000000000000000 : ℝ)) -
              6 * (Real.pi / 2 - (4630833778944860274891 / 10000000000000000000000 : ℝ))))) ≤
      Vfield (280457333 / 200000000000 : ℝ) := by
  have hL1 :
    (350326094811190417 / 250000000000000000000 : ℝ) ≤
      Real.log (200280457333 / 200000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (200280457333 / 200000000000 : ℚ))
        (L := (350326094811190417 / 250000000000000000000 : ℚ))
        2 (by decide +kernel))
  have hU2 :
    Real.log (1405457333 / 200000000000 : ℝ) ≤
      (-(49579546107330803619953 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1405457333 / 200000000000 : ℚ))
        (r' := (1405457333 / 781250000 : ℚ))
        (U := (-(49579546107330803619953 / 10000000000000000000000 : ℚ)))
        (U' := (5872228316669196380047 / 10000000000000000000000 : ℚ))
        8 13 (by decide +kernel) (by constructor <;> norm_num)
  have hau49 :
    Real.arctan (374471182469361 / 10000000000000000 : ℝ) ≤
      (187148145473045818201 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (374471182469361 / 10000000000000000 : ℚ))
        (U := (187148145473045818201 / 5000000000000000000000 : ℚ))
        3 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (187148145473045818201 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 374471182469361 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 374471182469361 : ℝ) =
              (374471182469361 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau49)
  have hal50 :
    (4630833778944860274891 / 10000000000000000000000 : ℝ) ≤
      Real.arctan (62411863744893 / 125000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_ge_of_series_rat
        (z := (62411863744893 / 125000000000000 : ℚ))
        (L := (4630833778944860274891 / 10000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hat2 :
    Real.arctan (125000000000000 / 62411863744893 : ℝ) ≤
      (Real.pi / 2 - (4630833778944860274891 / 10000000000000000000000 : ℝ)) :=
    arctan_le_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (125000000000000 / 62411863744893 : ℝ) =
              (62411863744893 / 125000000000000 : ℝ)
            by
        norm_num];
        exact hal50)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (280457333 / 200000000000 : ℚ))
      (lo := (187235591234679 / 5000000000000000 : ℚ))
      (hi := (374471182469361 / 10000000000000000 : ℚ))
      (s := (374471182469361 / 10000000000000000 : ℚ))
      (r₁ := (200280457333 / 200000000000 : ℚ))
      (r₂ := (1405457333 / 200000000000 : ℚ))
      (z₁ := (10000000000000000 / 374471182469361 : ℚ))
      (z₂ := (125000000000000 / 62411863744893 : ℚ))
      (L := (350326094811190417 / 250000000000000000000 : ℚ))
      (U := (-(49579546107330803619953 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inr ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
