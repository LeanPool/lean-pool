/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

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

/-! # V46: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

lemma V_553 :
    ((2445721257994797455589 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4517002183391446592761 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3971523528403931 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3356292705214036771549 / 10000000000000000000000 : ℝ))) -
              6 * (941430856712295929961 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (8075775557973 / 12800000000000 : ℝ) := by
  have hL1 :
    (2445721257994797455589 / 5000000000000000000000 : ℝ) ≤
      Real.log (20875775557973 / 12800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (20875775557973 / 12800000000000 : ℚ))
        (L := (2445721257994797455589 / 5000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (8147775557973 / 12800000000000 : ℝ) ≤
      (-(4517002183391446592761 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (8147775557973 / 12800000000000 : ℝ) = (8147775557973 / 6400000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (8147775557973 / 6400000000000 : ℚ))
             (U := (2414469619608553407239 / 10000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (8147775557973 / 6400000000000 : ℝ) ≤
            (2414469619608553407239 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau878 :
    Real.arctan (7943047056807865 / 22770747689413649 : ℝ) ≤
      (3356292705214036771549 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7943047056807865 / 22770747689413649 : ℚ))
        (U := (3356292705214036771549 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau877 :
    Real.arctan (1588609411361573 / 2000000000000000 : ℝ) ≤
      (2 * (3356292705214036771549 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12770747689413649 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1588609411361573 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1588609411361573 / 2000000000000000 : ℝ) /
                (1 + (12770747689413649 / 10000000000000000 : ℝ)) =
              (7943047056807865 / 22770747689413649 : ℝ)
            by
        norm_num];
        exact hau878)
  have hat1 :
    (Real.pi / 2 - (2 * (3356292705214036771549 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1588609411361573 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1588609411361573 : ℝ) =
              (1588609411361573 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau877)
  have hat2 :
    Real.arctan (375000000000000 / 3971523528403931 : ℝ) ≤
      (941430856712295929961 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 3971523528403931 : ℚ))
        (U := (941430856712295929961 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (8075775557973 / 12800000000000 : ℚ))
      (lo := (3971523528403931 / 5000000000000000 : ℚ))
      (hi := (1588609411361573 / 2000000000000000 : ℚ))
      (s := (3971523528403931 / 5000000000000000 : ℚ))
      (r₁ := (20875775557973 / 12800000000000 : ℚ))
      (r₂ := (8147775557973 / 12800000000000 : ℚ))
      (z₁ := (2000000000000000 / 1588609411361573 : ℚ))
      (z₂ := (375000000000000 / 3971523528403931 : ℚ))
      (L := (2445721257994797455589 / 5000000000000000000000 : ℚ))
      (U := (-(4517002183391446592761 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_554 :
    ((2449015504249571333993 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4500130194867739664721 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7949810374586183 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (671673097886714578427 / 2000000000000000000000 : ℝ))) -
              6 * (37625386017259067461 / 400000000000000000000 : ℝ)))) ≤
      Vfield (20223835197401 / 32000000000000 : ℝ) := by
  have hL1 :
    (2449015504249571333993 / 5000000000000000000000 : ℝ) ≤
      Real.log (52223835197401 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (52223835197401 / 32000000000000 : ℚ))
        (L := (2449015504249571333993 / 5000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (20403835197401 / 32000000000000 : ℝ) ≤
      (-(4500130194867739664721 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20403835197401 / 32000000000000 : ℝ) = (20403835197401 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (20403835197401 / 16000000000000 : ℚ))
             (U := (2431341608132260335279 / 10000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (20403835197401 / 16000000000000 : ℝ) ≤
            (2431341608132260335279 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau880 :
    Real.arctan (3974905187293093 / 11387477690604448 : ℝ) ≤
      (671673097886714578427 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3974905187293093 / 11387477690604448 : ℚ))
        (U := (671673097886714578427 / 2000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau879 :
    Real.arctan (3974905187293093 / 5000000000000000 : ℝ) ≤
      (2 * (671673097886714578427 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (199608677831389 / 156250000000000 : ℝ) ≤
          Real.sqrt (1 + (3974905187293093 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3974905187293093 / 5000000000000000 : ℝ) /
                (1 + (199608677831389 / 156250000000000 : ℝ)) =
              (3974905187293093 / 11387477690604448 : ℝ)
            by
        norm_num];
        exact hau880)
  have hat1 :
    (Real.pi / 2 - (2 * (671673097886714578427 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3974905187293093 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3974905187293093 : ℝ) =
              (3974905187293093 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau879)
  have hat2 :
    Real.arctan (750000000000000 / 7949810374586183 : ℝ) ≤
      (37625386017259067461 / 400000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 7949810374586183 : ℚ))
        (U := (37625386017259067461 / 400000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (20223835197401 / 32000000000000 : ℚ))
      (lo := (7949810374586183 / 10000000000000000 : ℚ))
      (hi := (3974905187293093 / 5000000000000000 : ℚ))
      (s := (7949810374586183 / 10000000000000000 : ℚ))
      (r₁ := (52223835197401 / 32000000000000 : ℚ))
      (r₂ := (20403835197401 / 32000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3974905187293093 : ℚ))
      (z₂ := (750000000000000 / 7949810374586183 : ℚ))
      (L := (2449015504249571333993 / 5000000000000000000000 : ℚ))
      (U := (-(4500130194867739664721 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_555 :
    ((4904615163043244052437 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4483286624802846121209 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7956567943346689 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3360435148132570495601 / 10000000000000000000000 : ℝ))) -
              6 * (187968092181113295817 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (40516462999739 / 64000000000000 : ℝ) := by
  have hL1 :
    (4904615163043244052437 / 10000000000000000000000 : ℝ) ≤
      Real.log (104516462999739 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (104516462999739 / 64000000000000 : ℚ))
        (L := (4904615163043244052437 / 10000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (40876462999739 / 64000000000000 : ℝ) ≤
      (-(4483286624802846121209 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (40876462999739 / 64000000000000 : ℝ) = (40876462999739 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (40876462999739 / 32000000000000 : ℚ))
             (U := (2448185178197153878791 / 10000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (40876462999739 / 32000000000000 : ℝ) ≤
            (2448185178197153878791 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau882 :
    Real.arctan (7956567943346692 / 22779161687571379 : ℝ) ≤
      (3360435148132570495601 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7956567943346692 / 22779161687571379 : ℚ))
        (U := (3360435148132570495601 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau881 :
    Real.arctan (1989141985836673 / 2500000000000000 : ℝ) ≤
      (2 * (3360435148132570495601 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12779161687571379 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1989141985836673 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1989141985836673 / 2500000000000000 : ℝ) /
                (1 + (12779161687571379 / 10000000000000000 : ℝ)) =
              (7956567943346692 / 22779161687571379 : ℝ)
            by
        norm_num];
        exact hau882)
  have hat1 :
    (Real.pi / 2 - (2 * (3360435148132570495601 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1989141985836673 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1989141985836673 : ℝ) =
              (1989141985836673 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau881)
  have hat2 :
    Real.arctan (750000000000000 / 7956567943346689 : ℝ) ≤
      (187968092181113295817 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 7956567943346689 : ℚ))
        (U := (187968092181113295817 / 2000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (40516462999739 / 64000000000000 : ℚ))
      (lo := (7956567943346689 / 10000000000000000 : ℚ))
      (hi := (1989141985836673 / 2500000000000000 : ℚ))
      (s := (7956567943346689 / 10000000000000000 : ℚ))
      (r₁ := (104516462999739 / 64000000000000 : ℚ))
      (r₂ := (40876462999739 / 64000000000000 : ℚ))
      (z₁ := (2500000000000000 / 1989141985836673 : ℚ))
      (z₂ := (750000000000000 / 7956567943346689 : ℚ))
      (L := (4904615163043244052437 / 10000000000000000000000 : ℚ))
      (U := (-(4483286624802846121209 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_556 :
    ((2455597492665253910909 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2233235688812019465853 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1592663955545001 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3362501689903647580097 / 10000000000000000000000 : ℝ))) -
              6 * (234762069908735241679 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (10146313901169 / 16000000000000 : ℝ) := by
  have hL1 :
    (2455597492665253910909 / 5000000000000000000000 : ℝ) ≤
      Real.log (26146313901169 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (26146313901169 / 16000000000000 : ℚ))
        (L := (2455597492665253910909 / 5000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (10236313901169 / 16000000000000 : ℝ) ≤
      (-(2233235688812019465853 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (10236313901169 / 16000000000000 : ℝ) = (10236313901169 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (10236313901169 / 8000000000000 : ℚ))
             (U := (1232500212687980534147 / 5000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (10236313901169 / 8000000000000 : ℝ) ≤
            (1232500212687980534147 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau884 :
    Real.arctan (3981659888862504 / 11391683304934355 : ℝ) ≤
      (3362501689903647580097 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3981659888862504 / 11391683304934355 : ℚ))
        (U := (3362501689903647580097 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau883 :
    Real.arctan (497707486107813 / 625000000000000 : ℝ) ≤
      (2 * (3362501689903647580097 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (1278336660986871 / 1000000000000000 : ℝ) ≤
          Real.sqrt (1 + (497707486107813 / 625000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (497707486107813 / 625000000000000 : ℝ) /
                (1 + (1278336660986871 / 1000000000000000 : ℝ)) =
              (3981659888862504 / 11391683304934355 : ℝ)
            by
        norm_num];
        exact hau884)
  have hat1 :
    (Real.pi / 2 - (2 * (3362501689903647580097 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (625000000000000 / 497707486107813 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (625000000000000 / 497707486107813 : ℝ) =
              (497707486107813 / 625000000000000 : ℝ)
            by
        norm_num];
        exact hau883)
  have hat2 :
    Real.arctan (50000000000000 / 530887985181667 : ℝ) ≤
      (234762069908735241679 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (50000000000000 / 530887985181667 : ℚ))
        (U := (234762069908735241679 / 2500000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (10146313901169 / 16000000000000 : ℚ))
      (lo := (1592663955545001 / 2000000000000000 : ℚ))
      (hi := (497707486107813 / 625000000000000 : ℚ))
      (s := (1592663955545001 / 2000000000000000 : ℚ))
      (r₁ := (26146313901169 / 16000000000000 : ℚ))
      (r₂ := (10236313901169 / 16000000000000 : ℚ))
      (z₁ := (625000000000000 / 497707486107813 : ℚ))
      (z₂ := (50000000000000 / 530887985181667 : ℚ))
      (L := (2455597492665253910909 / 5000000000000000000000 : ℚ))
      (U := (-(2233235688812019465853 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_557 :
    ((4917770481058281652449 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4449684358239905772299 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7970065892294761 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (672913024660701932149 / 2000000000000000000000 : ℝ))) -
              6 * (117282262271255301799 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (40654048209613 / 64000000000000 : ℝ) := by
  have hL1 :
    (4917770481058281652449 / 10000000000000000000000 : ℝ) ≤
      Real.log (104654048209613 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (104654048209613 / 64000000000000 : ℚ))
        (L := (4917770481058281652449 / 10000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (41014048209613 / 64000000000000 : ℝ) ≤
      (-(4449684358239905772299 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (41014048209613 / 64000000000000 : ℝ) = (41014048209613 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (41014048209613 / 32000000000000 : ℚ))
             (U := (2481787444760094227701 / 10000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (41014048209613 / 32000000000000 : ℝ) ≤
            (2481787444760094227701 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau886 :
    Real.arctan (3985032946147382 / 11393785074733125 : ℝ) ≤
      (672913024660701932149 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3985032946147382 / 11393785074733125 : ℚ))
        (U := (672913024660701932149 / 2000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau885 :
    Real.arctan (1992516473073691 / 2500000000000000 : ℝ) ≤
      (2 * (672913024660701932149 / 2000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (10230056119573 / 8000000000000 : ℝ) ≤
          Real.sqrt (1 + (1992516473073691 / 2500000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1992516473073691 / 2500000000000000 : ℝ) /
                (1 + (10230056119573 / 8000000000000 : ℝ)) =
              (3985032946147382 / 11393785074733125 : ℝ)
            by
        norm_num];
        exact hau886)
  have hat1 :
    (Real.pi / 2 - (2 * (672913024660701932149 / 2000000000000000000000 : ℝ))) ≤
      Real.arctan (2500000000000000 / 1992516473073691 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1992516473073691 : ℝ) =
              (1992516473073691 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau885)
  have hat2 :
    Real.arctan (750000000000000 / 7970065892294761 : ℝ) ≤
      (117282262271255301799 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 7970065892294761 : ℚ))
        (U := (117282262271255301799 / 1250000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (40654048209613 / 64000000000000 : ℚ))
      (lo := (7970065892294761 / 10000000000000000 : ℚ))
      (hi := (1992516473073691 / 2500000000000000 : ℚ))
      (s := (7970065892294761 / 10000000000000000 : ℚ))
      (r₁ := (104654048209613 / 64000000000000 : ℚ))
      (r₂ := (41014048209613 / 64000000000000 : ℚ))
      (z₁ := (2500000000000000 / 1992516473073691 : ℚ))
      (z₂ := (750000000000000 / 7970065892294761 : ℚ))
      (L := (4917770481058281652449 / 10000000000000000000000 : ℚ))
      (U := (-(4449684358239905772299 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_558 :
    ((4924341655912681739097 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4432925472037122503297 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((3988403150783981 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1683312728426578497401 / 5000000000000000000000 : ℝ))) -
              6 * (937469908111000802269 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (814456816291 / 1280000000000 : ℝ) := by
  have hL1 :
    (4924341655912681739097 / 10000000000000000000000 : ℝ) ≤
      Real.log (2094456816291 / 1280000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2094456816291 / 1280000000000 : ℚ))
        (L := (4924341655912681739097 / 10000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (821656816291 / 1280000000000 : ℝ) ≤
      (-(4432925472037122503297 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (821656816291 / 1280000000000 : ℝ) = (821656816291 / 640000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (821656816291 / 640000000000 : ℚ))
             (U := (2498546330962877496703 / 10000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (821656816291 / 640000000000 : ℝ) ≤
            (2498546330962877496703 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau888 :
    Real.arctan (7976806301567965 / 22791772307727118 : ℝ) ≤
      (1683312728426578497401 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (7976806301567965 / 22791772307727118 : ℚ))
        (U := (1683312728426578497401 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau887 :
    Real.arctan (1595361260313593 / 2000000000000000 : ℝ) ≤
      (2 * (1683312728426578497401 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6395886153863559 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (1595361260313593 / 2000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (1595361260313593 / 2000000000000000 : ℝ) /
                (1 + (6395886153863559 / 5000000000000000 : ℝ)) =
              (7976806301567965 / 22791772307727118 : ℝ)
            by
        norm_num];
        exact hau888)
  have hat1 :
    (Real.pi / 2 - (2 * (1683312728426578497401 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (2000000000000000 / 1595361260313593 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2000000000000000 / 1595361260313593 : ℝ) =
              (1595361260313593 / 2000000000000000 : ℝ)
            by
        norm_num];
        exact hau887)
  have hat2 :
    Real.arctan (375000000000000 / 3988403150783981 : ℝ) ≤
      (937469908111000802269 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 3988403150783981 : ℚ))
        (U := (937469908111000802269 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (814456816291 / 1280000000000 : ℚ))
      (lo := (3988403150783981 / 5000000000000000 : ℚ))
      (hi := (1595361260313593 / 2000000000000000 : ℚ))
      (s := (3988403150783981 / 5000000000000000 : ℚ))
      (r₁ := (2094456816291 / 1280000000000 : ℚ))
      (r₂ := (821656816291 / 1280000000000 : ℚ))
      (z₁ := (2000000000000000 / 1595361260313593 : ℚ))
      (z₂ := (375000000000000 / 3988403150783981 : ℚ))
      (L := (4924341655912681739097 / 10000000000000000000000 : ℚ))
      (U := (-(4432925472037122503297 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_559 :
    ((2465454257784311148601 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2208097312438626819047 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((7983541019995351 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (1684341349519044723379 / 5000000000000000000000 : ℝ))) -
              6 * (936683701107258921899 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (40791633419487 / 64000000000000 : ℝ) := by
  have hL1 :
    (2465454257784311148601 / 5000000000000000000000 : ℝ) ≤
      Real.log (104791633419487 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (104791633419487 / 64000000000000 : ℚ))
        (L := (2465454257784311148601 / 5000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (41151633419487 / 64000000000000 : ℝ) ≤
      (-(2208097312438626819047 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (41151633419487 / 64000000000000 : ℝ) = (41151633419487 / 32000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (41151633419487 / 32000000000000 : ℚ))
             (U := (1257638589061373180953 / 5000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (41151633419487 / 32000000000000 : ℝ) ≤
            (1257638589061373180953 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau890 :
    Real.arctan (3991770509997677 / 11397986543006097 : ℝ) ≤
      (1684341349519044723379 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (3991770509997677 / 11397986543006097 : ℚ))
        (U := (1684341349519044723379 / 5000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau889 :
    Real.arctan (3991770509997677 / 5000000000000000 : ℝ) ≤
      (2 * (1684341349519044723379 / 5000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (6397986543006097 / 5000000000000000 : ℝ) ≤
          Real.sqrt (1 + (3991770509997677 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (3991770509997677 / 5000000000000000 : ℝ) /
                (1 + (6397986543006097 / 5000000000000000 : ℝ)) =
              (3991770509997677 / 11397986543006097 : ℝ)
            by
        norm_num];
        exact hau890)
  have hat1 :
    (Real.pi / 2 - (2 * (1684341349519044723379 / 5000000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 3991770509997677 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 3991770509997677 : ℝ) =
              (3991770509997677 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau889)
  have hat2 :
    Real.arctan (750000000000000 / 7983541019995351 : ℝ) ≤
      (936683701107258921899 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 7983541019995351 : ℚ))
        (U := (936683701107258921899 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (40791633419487 / 64000000000000 : ℚ))
      (lo := (7983541019995351 / 10000000000000000 : ℚ))
      (hi := (3991770509997677 / 5000000000000000 : ℚ))
      (s := (7983541019995351 / 10000000000000000 : ℚ))
      (r₁ := (104791633419487 / 64000000000000 : ℚ))
      (r₂ := (41151633419487 / 64000000000000 : ℚ))
      (z₁ := (5000000000000000 / 3991770509997677 : ℚ))
      (z₂ := (750000000000000 / 7983541019995351 : ℚ))
      (L := (2465454257784311148601 / 5000000000000000000000 : ℚ))
      (U := (-(2208097312438626819047 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_560 :
    ((4937471065689844968309 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(549936465386697441599 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1997567515491693 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (842684214577127660523 / 2500000000000000000000 : ℝ))) -
              6 * (467949734428600301737 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (5107553253053 / 8000000000000 : ℝ) := by
  have hL1 :
    (4937471065689844968309 / 10000000000000000000000 : ℝ) ≤
      Real.log (13107553253053 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (13107553253053 / 8000000000000 : ℚ))
        (L := (4937471065689844968309 / 10000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (5152553253053 / 8000000000000 : ℝ) ≤
      (-(549936465386697441599 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (5152553253053 / 8000000000000 : ℝ) = (5152553253053 / 4000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (5152553253053 / 4000000000000 : ℚ))
             (U := (316497509988302558401 / 1250000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (5152553253053 / 4000000000000 : ℝ) ≤
            (316497509988302558401 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau892 :
    Real.arctan (2663423353988925 / 7600057495226708 : ℝ) ≤
      (842684214577127660523 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (2663423353988925 / 7600057495226708 : ℚ))
        (U := (842684214577127660523 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau891 :
    Real.arctan (319610802478671 / 400000000000000 : ℝ) ≤
      (2 * (842684214577127660523 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (3200043121420031 / 2500000000000000 : ℝ) ≤
          Real.sqrt (1 + (319610802478671 / 400000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (319610802478671 / 400000000000000 : ℝ) /
                (1 + (3200043121420031 / 2500000000000000 : ℝ)) =
              (2663423353988925 / 7600057495226708 : ℝ)
            by
        norm_num];
        exact hau892)
  have hat1 :
    (Real.pi / 2 - (2 * (842684214577127660523 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (400000000000000 / 319610802478671 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (400000000000000 / 319610802478671 : ℝ) =
              (319610802478671 / 400000000000000 : ℝ)
            by
        norm_num];
        exact hau891)
  have hat2 :
    Real.arctan (62500000000000 / 665855838497231 : ℝ) ≤
      (467949734428600301737 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (62500000000000 / 665855838497231 : ℚ))
        (U := (467949734428600301737 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (5107553253053 / 8000000000000 : ℚ))
      (lo := (1997567515491693 / 2500000000000000 : ℚ))
      (hi := (319610802478671 / 400000000000000 : ℚ))
      (s := (1997567515491693 / 2500000000000000 : ℚ))
      (r₁ := (13107553253053 / 8000000000000 : ℚ))
      (r₂ := (5152553253053 / 8000000000000 : ℚ))
      (z₁ := (400000000000000 / 319610802478671 : ℚ))
      (z₂ := (62500000000000 / 665855838497231 : ℚ))
      (L := (4937471065689844968309 / 10000000000000000000000 : ℚ))
      (U := (-(549936465386697441599 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_561 :
    ((4950583259927416104161 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2183084691663832143643 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((8003711173798727 / 10000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (843708990432839064989 / 2500000000000000000000 : ℝ))) -
              6 * (467168447827085537807 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (20499005617149 / 32000000000000 : ℝ) := by
  have hL1 :
    (4950583259927416104161 / 10000000000000000000000 : ℝ) ≤
      Real.log (52499005617149 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (52499005617149 / 32000000000000 : ℚ))
        (L := (4950583259927416104161 / 10000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (20679005617149 / 32000000000000 : ℝ) ≤
      (-(2183084691663832143643 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20679005617149 / 32000000000000 : ℝ) = (20679005617149 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (20679005617149 / 16000000000000 : ℚ))
             (U := (1282651209836167856357 / 5000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (20679005617149 / 16000000000000 : ℝ) ≤
            (1282651209836167856357 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau894 :
    Real.arctan (8003711173798730 / 22808567154588003 : ℝ) ≤
      (843708990432839064989 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8003711173798730 / 22808567154588003 : ℚ))
        (U := (843708990432839064989 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau893 :
    Real.arctan (800371117379873 / 1000000000000000 : ℝ) ≤
      (2 * (843708990432839064989 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12808567154588003 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (800371117379873 / 1000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (800371117379873 / 1000000000000000 : ℝ) /
                (1 + (12808567154588003 / 10000000000000000 : ℝ)) =
              (8003711173798730 / 22808567154588003 : ℝ)
            by
        norm_num];
        exact hau894)
  have hat1 :
    (Real.pi / 2 - (2 * (843708990432839064989 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (1000000000000000 / 800371117379873 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 800371117379873 : ℝ) =
              (800371117379873 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau893)
  have hat2 :
    Real.arctan (750000000000000 / 8003711173798727 : ℝ) ≤
      (467168447827085537807 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 8003711173798727 : ℚ))
        (U := (467168447827085537807 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (20499005617149 / 32000000000000 : ℚ))
      (lo := (8003711173798727 / 10000000000000000 : ℚ))
      (hi := (800371117379873 / 1000000000000000 : ℚ))
      (s := (8003711173798727 / 10000000000000000 : ℚ))
      (r₁ := (52499005617149 / 32000000000000 : ℚ))
      (r₂ := (20679005617149 / 32000000000000 : ℚ))
      (z₁ := (1000000000000000 / 800371117379873 : ℚ))
      (z₂ := (750000000000000 / 8003711173798727 : ℚ))
      (L := (4950583259927416104161 / 10000000000000000000000 : ℚ))
      (U := (-(2183084691663832143643 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_562 :
    ((2481839141856494072461 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2166478856360513774443 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((1603425950195627 / 2000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (844730708506255858439 / 2500000000000000000000 : ℝ))) -
              6 * (466391061526950188599 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (10283899111043 / 16000000000000 : ℝ) := by
  have hL1 :
    (2481839141856494072461 / 5000000000000000000000 : ℝ) ≤
      Real.log (26283899111043 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (26283899111043 / 16000000000000 : ℚ))
        (L := (2481839141856494072461 / 5000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (10373899111043 / 16000000000000 : ℝ) ≤
      (-(2166478856360513774443 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (10373899111043 / 16000000000000 : ℝ) = (10373899111043 / 8000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (10373899111043 / 8000000000000 : ℚ))
             (U := (1299257045139486225557 / 5000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (10373899111043 / 8000000000000 : ℝ) ≤
            (1299257045139486225557 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau896 :
    Real.arctan (8017129750978138 / 22816956325275465 : ℝ) ≤
      (844730708506255858439 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8017129750978138 / 22816956325275465 : ℚ))
        (U := (844730708506255858439 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau895 :
    Real.arctan (4008564875489069 / 5000000000000000 : ℝ) ≤
      (2 * (844730708506255858439 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2563391265055093 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (4008564875489069 / 5000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (4008564875489069 / 5000000000000000 : ℝ) /
                (1 + (2563391265055093 / 2000000000000000 : ℝ)) =
              (8017129750978138 / 22816956325275465 : ℝ)
            by
        norm_num];
        exact hau896)
  have hat1 :
    (Real.pi / 2 - (2 * (844730708506255858439 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (5000000000000000 / 4008564875489069 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (5000000000000000 / 4008564875489069 : ℝ) =
              (4008564875489069 / 5000000000000000 : ℝ)
            by
        norm_num];
        exact hau895)
  have hat2 :
    Real.arctan (150000000000000 / 1603425950195627 : ℝ) ≤
      (466391061526950188599 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (150000000000000 / 1603425950195627 : ℚ))
        (U := (466391061526950188599 / 5000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (10283899111043 / 16000000000000 : ℚ))
      (lo := (1603425950195627 / 2000000000000000 : ℚ))
      (hi := (4008564875489069 / 5000000000000000 : ℚ))
      (s := (1603425950195627 / 2000000000000000 : ℚ))
      (r₁ := (26283899111043 / 16000000000000 : ℚ))
      (r₂ := (10373899111043 / 16000000000000 : ℚ))
      (z₁ := (5000000000000000 / 4008564875489069 : ℚ))
      (z₂ := (150000000000000 / 1603425950195627 : ℚ))
      (L := (2481839141856494072461 / 5000000000000000000000 : ℚ))
      (U := (-(2166478856360513774443 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_563 :
    ((4976756181957258726983 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(1074963994651026888953 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4015262953233787 / 5000000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (845749385385216735619 / 2500000000000000000000 : ℝ))) -
              6 * (931235086368221112029 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (20636590827023 / 32000000000000 : ℝ) := by
  have hL1 :
    (4976756181957258726983 / 10000000000000000000000 : ℝ) ≤
      Real.log (52636590827023 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (52636590827023 / 32000000000000 : ℚ))
        (L := (4976756181957258726983 / 10000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (20816590827023 / 32000000000000 : ℝ) ≤
      (-(1074963994651026888953 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20816590827023 / 32000000000000 : ℝ) = (20816590827023 / 16000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (20816590827023 / 16000000000000 : ℚ))
             (U := (657903956098973111047 / 2500000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (20816590827023 / 16000000000000 : ℝ) ≤
            (657903956098973111047 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau898 :
    Real.arctan (8030525906467577 / 22825340008531815 : ℝ) ≤
      (845749385385216735619 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8030525906467577 / 22825340008531815 : ℚ))
        (U := (845749385385216735619 / 2500000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau897 :
    Real.arctan (8030525906467577 / 10000000000000000 : ℝ) ≤
      (2 * (845749385385216735619 / 2500000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (2565068001706363 / 2000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8030525906467577 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8030525906467577 / 10000000000000000 : ℝ) /
                (1 + (2565068001706363 / 2000000000000000 : ℝ)) =
              (8030525906467577 / 22825340008531815 : ℝ)
            by
        norm_num];
        exact hau898)
  have hat1 :
    (Real.pi / 2 - (2 * (845749385385216735619 / 2500000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8030525906467577 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8030525906467577 : ℝ) =
              (8030525906467577 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau897)
  have hat2 :
    Real.arctan (375000000000000 / 4015262953233787 : ℝ) ≤
      (931235086368221112029 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 4015262953233787 : ℚ))
        (U := (931235086368221112029 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (20636590827023 / 32000000000000 : ℚ))
      (lo := (4015262953233787 / 5000000000000000 : ℚ))
      (hi := (8030525906467577 / 10000000000000000 : ℚ))
      (s := (4015262953233787 / 5000000000000000 : ℚ))
      (r₁ := (52636590827023 / 32000000000000 : ℚ))
      (r₂ := (20816590827023 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 8030525906467577 : ℚ))
      (z₂ := (375000000000000 / 4015262953233787 : ℚ))
      (L := (4976756181957258726983 / 10000000000000000000000 : ℚ))
      (U := (-(1074963994651026888953 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_564 :
    ((498981699939495428459 / 1000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(853372691111829526357 / 2000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2010974938072249 / 2500000000000000 : ℝ) *
            (Real.pi +
                (Real.pi / 2 - (2 * (3387060150084523494817 / 10000000000000000000000 : ℝ))) -
              6 * (929695721657504509173 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (517634585799 / 800000000000 : ℝ) := by
  have hL1 :
    (498981699939495428459 / 1000000000000000000000 : ℝ) ≤
      Real.log (1317634585799 / 800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (1317634585799 / 800000000000 : ℚ))
        (L := (498981699939495428459 / 1000000000000000000000 : ℚ))
        11 (by decide +kernel))
  have hU2 :
    Real.log (522134585799 / 800000000000 : ℝ) ≤
      (-(853372691111829526357 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (522134585799 / 800000000000 : ℝ) = (522134585799 / 400000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (522134585799 / 400000000000 : ℚ))
             (U := (532921669488170473643 / 2000000000000000000000 : ℚ))
             8 (by decide +kernel)) :
          Real.log (522134585799 / 400000000000 : ℝ) ≤
            (532921669488170473643 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau900 :
    Real.arctan (8043899752288999 / 22833718215111121 : ℝ) ≤
      (3387060150084523494817 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (8043899752288999 / 22833718215111121 : ℚ))
        (U := (3387060150084523494817 / 10000000000000000000000 : ℚ))
        8 (by decide +kernel))
  have hau899 :
    Real.arctan (8043899752288999 / 10000000000000000 : ℝ) ≤
      (2 * (3387060150084523494817 / 10000000000000000000000 : ℝ)) :=
    arctan_le_half (by norm_num) (by norm_num)
      (le_sqrt_of_sq_le (by norm_num) (by norm_num) :
        (12833718215111121 / 10000000000000000 : ℝ) ≤
          Real.sqrt (1 + (8043899752288999 / 10000000000000000 : ℝ) ^ 2))
      (by
        rw [show
            (8043899752288999 / 10000000000000000 : ℝ) /
                (1 + (12833718215111121 / 10000000000000000 : ℝ)) =
              (8043899752288999 / 22833718215111121 : ℝ)
            by
        norm_num];
        exact hau900)
  have hat1 :
    (Real.pi / 2 - (2 * (3387060150084523494817 / 10000000000000000000000 : ℝ))) ≤
      Real.arctan (10000000000000000 / 8043899752288999 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 8043899752288999 : ℝ) =
              (8043899752288999 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau899)
  have hat2 :
    Real.arctan (187500000000000 / 2010974938072249 : ℝ) ≤
      (929695721657504509173 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (187500000000000 / 2010974938072249 : ℚ))
        (U := (929695721657504509173 / 10000000000000000000000 : ℚ))
        4 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (517634585799 / 800000000000 : ℚ))
      (lo := (2010974938072249 / 2500000000000000 : ℚ))
      (hi := (8043899752288999 / 10000000000000000 : ℚ))
      (s := (2010974938072249 / 2500000000000000 : ℚ))
      (r₁ := (1317634585799 / 800000000000 : ℚ))
      (r₂ := (522134585799 / 800000000000 : ℚ))
      (z₁ := (10000000000000000 / 8043899752288999 : ℚ))
      (z₂ := (187500000000000 / 2010974938072249 : ℚ))
      (L := (498981699939495428459 / 1000000000000000000000 : ℚ))
      (U := (-(853372691111829526357 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
