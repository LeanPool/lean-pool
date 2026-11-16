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

/-! # V19: certified bounds for the zeta(5) proof -/

@[expose] public section

open Finset

namespace Zeta5Irrational

lemma V_229 :
    ((196312570291665255689 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8695478910589005680281 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4123762613683913 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1955649145612707344259 / 5000000000000000000000 : ℝ)) -
              6 * (224882887845839136873 / 1250000000000000000000 : ℝ)))) ≤
      Vfield (10883467580171 / 64000000000000 : ℝ) := by
  have hL1 :
    (196312570291665255689 / 1250000000000000000000 : ℝ) ≤
      Real.log (74883467580171 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (74883467580171 / 64000000000000 : ℚ))
        (L := (196312570291665255689 / 1250000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (11243467580171 / 64000000000000 : ℝ) ≤
      (-(8695478910589005680281 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (11243467580171 / 64000000000000 : ℝ) = (11243467580171 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (11243467580171 / 8000000000000 : ℚ))
             (U := (1701728793910994319719 / 5000000000000000000000 : ℚ))
             9 (by decide +kernel)) :
          Real.log (11243467580171 / 8000000000000 : ℝ) ≤
            (1701728793910994319719 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau291 :
    Real.arctan (1030940653420979 / 2500000000000000 : ℝ) ≤
      (1955649145612707344259 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1030940653420979 / 2500000000000000 : ℚ))
        (U := (1955649145612707344259 / 5000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1955649145612707344259 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1030940653420979 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1030940653420979 : ℝ) =
              (1030940653420979 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau291)
  have hat2 :
    Real.arctan (750000000000000 / 4123762613683913 : ℝ) ≤
      (224882887845839136873 / 1250000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 4123762613683913 : ℚ))
        (U := (224882887845839136873 / 1250000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (10883467580171 / 64000000000000 : ℚ))
      (lo := (4123762613683913 / 10000000000000000 : ℚ))
      (hi := (1030940653420979 / 2500000000000000 : ℚ))
      (s := (4123762613683913 / 10000000000000000 : ℚ))
      (r₁ := (74883467580171 / 64000000000000 : ℚ))
      (r₂ := (11243467580171 / 64000000000000 : ℚ))
      (z₁ := (2500000000000000 / 1030940653420979 : ℚ))
      (z₂ := (750000000000000 / 4123762613683913 : ℚ))
      (L := (196312570291665255689 / 1250000000000000000000 : ℚ))
      (U := (-(8695478910589005680281 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_230 :
    ((197260017728728357033 / 1250000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17340584442306510414111 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2067252820721749 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (39204764633408501653 / 100000000000000000000 : ℝ)) -
              6 * (112155517789191659431 / 625000000000000000000 : ℝ)))) ≤
      Vfield (5470123807721 / 32000000000000 : ℝ) := by
  have hL1 :
    (197260017728728357033 / 1250000000000000000000 : ℝ) ≤
      Real.log (37470123807721 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (37470123807721 / 32000000000000 : ℚ))
        (L := (197260017728728357033 / 1250000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (5650123807721 / 32000000000000 : ℝ) ≤
      (-(17340584442306510414111 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (5650123807721 / 32000000000000 : ℝ) = (5650123807721 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (5650123807721 / 4000000000000 : ℚ))
             (U := (3453830966693489585889 / 10000000000000000000000 : ℚ))
             9 (by decide +kernel)) :
          Real.log (5650123807721 / 4000000000000 : ℝ) ≤
            (3453830966693489585889 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau292 :
    Real.arctan (4134505641443501 / 10000000000000000 : ℝ) ≤
      (39204764633408501653 / 100000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4134505641443501 / 10000000000000000 : ℚ))
        (U := (39204764633408501653 / 100000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (39204764633408501653 / 100000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4134505641443501 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4134505641443501 : ℝ) =
              (4134505641443501 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau292)
  have hat2 :
    Real.arctan (375000000000000 / 2067252820721749 : ℝ) ≤
      (112155517789191659431 / 625000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 2067252820721749 : ℚ))
        (U := (112155517789191659431 / 625000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (5470123807721 / 32000000000000 : ℚ))
      (lo := (2067252820721749 / 5000000000000000 : ℚ))
      (hi := (4134505641443501 / 10000000000000000 : ℚ))
      (s := (2067252820721749 / 5000000000000000 : ℚ))
      (r₁ := (37470123807721 / 32000000000000 : ℚ))
      (r₂ := (5650123807721 / 32000000000000 : ℚ))
      (z₁ := (10000000000000000 / 4134505641443501 : ℚ))
      (z₂ := (375000000000000 / 2067252820721749 : ℚ))
      (L := (197260017728728357033 / 1250000000000000000000 : ℚ))
      (U := (-(17340584442306510414111 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_231 :
    ((792826990337347588387 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8645231769943453544543 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2072610413478559 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (785924783077314604701 / 2000000000000000000000 : ℝ)) -
              6 * (447487048230703640181 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (10997027650713 / 64000000000000 : ℝ) := by
  have hL1 :
    (792826990337347588387 / 5000000000000000000000 : ℝ) ≤
      Real.log (74997027650713 / 64000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (74997027650713 / 64000000000000 : ℚ))
        (L := (792826990337347588387 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (11357027650713 / 64000000000000 : ℝ) ≤
      (-(8645231769943453544543 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (11357027650713 / 64000000000000 : ℝ) = (11357027650713 / 8000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (11357027650713 / 8000000000000 : ℚ))
             (U := (1751975934556546455457 / 5000000000000000000000 : ℚ))
             9 (by decide +kernel)) :
          Real.log (11357027650713 / 8000000000000 : ℝ) ≤
            (1751975934556546455457 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau293 :
    Real.arctan (4145220826957121 / 10000000000000000 : ℝ) ≤
      (785924783077314604701 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4145220826957121 / 10000000000000000 : ℚ))
        (U := (785924783077314604701 / 2000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (785924783077314604701 / 2000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4145220826957121 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4145220826957121 : ℝ) =
              (4145220826957121 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau293)
  have hat2 :
    Real.arctan (375000000000000 / 2072610413478559 : ℝ) ≤
      (447487048230703640181 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 2072610413478559 : ℚ))
        (U := (447487048230703640181 / 2500000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (10997027650713 / 64000000000000 : ℚ))
      (lo := (2072610413478559 / 5000000000000000 : ℚ))
      (hi := (4145220826957121 / 10000000000000000 : ℚ))
      (s := (2072610413478559 / 5000000000000000 : ℚ))
      (r₁ := (74997027650713 / 64000000000000 : ℚ))
      (r₂ := (11357027650713 / 64000000000000 : ℚ))
      (z₁ := (10000000000000000 / 4145220826957121 : ℚ))
      (z₂ := (375000000000000 / 2072610413478559 : ℚ))
      (L := (792826990337347588387 / 5000000000000000000000 : ℚ))
      (U := (-(8645231769943453544543 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_232 :
    ((796611043778550434037 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4310148148915218457899 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((259744274098869 / 625000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1969370438785238650359 / 5000000000000000000000 : ℝ)) -
              6 * (892721195245301638437 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (345431490187 / 2000000000000 : ℝ) := by
  have hL1 :
    (796611043778550434037 / 5000000000000000000000 : ℝ) ≤
      Real.log (2345431490187 / 2000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (2345431490187 / 2000000000000 : ℚ))
        (L := (796611043778550434037 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (356681490187 / 2000000000000 : ℝ) ≤
      (-(4310148148915218457899 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (356681490187 / 2000000000000 : ℝ) = (356681490187 / 250000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (356681490187 / 250000000000 : ℚ))
             (U := (888455703334781542101 / 2500000000000000000000 : ℚ))
             9 (by decide +kernel)) :
          Real.log (356681490187 / 250000000000 : ℝ) ≤
            (888455703334781542101 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau294 :
    Real.arctan (4155908385581907 / 10000000000000000 : ℝ) ≤
      (1969370438785238650359 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4155908385581907 / 10000000000000000 : ℚ))
        (U := (1969370438785238650359 / 5000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1969370438785238650359 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4155908385581907 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4155908385581907 : ℝ) =
              (4155908385581907 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau294)
  have hat2 :
    Real.arctan (15625000000000 / 86581424699623 : ℝ) ≤
      (892721195245301638437 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (15625000000000 / 86581424699623 : ℚ))
        (U := (892721195245301638437 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (345431490187 / 2000000000000 : ℚ))
      (lo := (259744274098869 / 625000000000000 : ℚ))
      (hi := (4155908385581907 / 10000000000000000 : ℚ))
      (s := (259744274098869 / 625000000000000 : ℚ))
      (r₁ := (2345431490187 / 2000000000000 : ℚ))
      (r₂ := (356681490187 / 2000000000000 : ℚ))
      (z₁ := (10000000000000000 / 4155908385581907 : ℚ))
      (z₂ := (15625000000000 / 86581424699623 : ℚ))
      (L := (796611043778550434037 / 5000000000000000000000 : ℚ))
      (U := (-(4310148148915218457899 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_233 :
    ((804170570046356540339 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17141590695463957545947 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4177201469832627 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3956884238851918576391 / 10000000000000000000000 : ℝ)) -
              6 * (177653194295087677753 / 1000000000000000000000 : ℝ)))) ≤
      Vfield (5583683878263 / 32000000000000 : ℝ) := by
  have hL1 :
    (804170570046356540339 / 5000000000000000000000 : ℝ) ≤
      Real.log (37583683878263 / 32000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (37583683878263 / 32000000000000 : ℚ))
        (L := (804170570046356540339 / 5000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (5763683878263 / 32000000000000 : ℝ) ≤
      (-(17141590695463957545947 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (5763683878263 / 32000000000000 : ℝ) = (5763683878263 / 4000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (5763683878263 / 4000000000000 : ℚ))
             (U := (3652824713536042454053 / 10000000000000000000000 : ℚ))
             9 (by decide +kernel)) :
          Real.log (5763683878263 / 4000000000000 : ℝ) ≤
            (3652824713536042454053 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau295 :
    Real.arctan (417720146983263 / 1000000000000000 : ℝ) ≤
      (3956884238851918576391 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (417720146983263 / 1000000000000000 : ℚ))
        (U := (3956884238851918576391 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3956884238851918576391 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 417720146983263 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 417720146983263 : ℝ) =
              (417720146983263 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau295)
  have hat2 :
    Real.arctan (250000000000000 / 1392400489944209 : ℝ) ≤
      (177653194295087677753 / 1000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1392400489944209 : ℚ))
        (U := (177653194295087677753 / 1000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (5583683878263 / 32000000000000 : ℚ))
      (lo := (4177201469832627 / 10000000000000000 : ℚ))
      (hi := (417720146983263 / 1000000000000000 : ℚ))
      (s := (4177201469832627 / 10000000000000000 : ℚ))
      (r₁ := (37583683878263 / 32000000000000 : ℚ))
      (r₂ := (5763683878263 / 32000000000000 : ℚ))
      (z₁ := (1000000000000000 / 417720146983263 : ℚ))
      (z₂ := (250000000000000 / 1392400489944209 : ℚ))
      (L := (804170570046356540339 / 5000000000000000000000 : ℚ))
      (U := (-(17141590695463957545947 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_234 :
    ((1623437368556860115687 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(17043559332240260533931 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2099193281346059 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (3974908332220430602867 / 10000000000000000000000 : ℝ)) -
              6 * (1767753594973346520647 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (2820231956767 / 16000000000000 : ℝ) := by
  have hL1 :
    (1623437368556860115687 / 10000000000000000000000 : ℝ) ≤
      Real.log (18820231956767 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (18820231956767 / 16000000000000 : ℚ))
        (L := (1623437368556860115687 / 10000000000000000000000 : ℚ))
        6 (by decide +kernel))
  have hU2 :
    Real.log (2910231956767 / 16000000000000 : ℝ) ≤
      (-(17043559332240260533931 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (2910231956767 / 16000000000000 : ℝ) = (2910231956767 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (2910231956767 / 2000000000000 : ℚ))
             (U := (3750856076759739466069 / 10000000000000000000000 : ℚ))
             10 (by decide +kernel)) :
          Real.log (2910231956767 / 2000000000000 : ℝ) ≤
            (3750856076759739466069 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau296 :
    Real.arctan (4198386562692121 / 10000000000000000 : ℝ) ≤
      (3974908332220430602867 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4198386562692121 / 10000000000000000 : ℚ))
        (U := (3974908332220430602867 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (3974908332220430602867 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4198386562692121 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4198386562692121 : ℝ) =
              (4198386562692121 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau296)
  have hat2 :
    Real.arctan (375000000000000 / 2099193281346059 : ℝ) ≤
      (1767753594973346520647 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 2099193281346059 : ℚ))
        (U := (1767753594973346520647 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2820231956767 / 16000000000000 : ℚ))
      (lo := (2099193281346059 / 5000000000000000 : ℚ))
      (hi := (4198386562692121 / 10000000000000000 : ℚ))
      (s := (2099193281346059 / 5000000000000000 : ℚ))
      (r₁ := (18820231956767 / 16000000000000 : ℚ))
      (r₂ := (2910231956767 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 4198386562692121 : ℚ))
      (z₂ := (375000000000000 / 2099193281346059 : ℚ))
      (L := (1623437368556860115687 / 10000000000000000000000 : ℚ))
      (U := (-(17043559332240260533931 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_235 :
    ((8192554208785925893 / 50000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8473239830903755215511 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2109732645385169 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (1996407449528079098729 / 5000000000000000000000 : ℝ)) -
              6 * (879552057096567979033 / 5000000000000000000000 : ℝ)))) ≤
      Vfield (1139448789761 / 6400000000000 : ℝ) := by
  have hL1 :
    (8192554208785925893 / 50000000000000000000 : ℝ) ≤
      Real.log (7539448789761 / 6400000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (7539448789761 / 6400000000000 : ℚ))
        (L := (8192554208785925893 / 50000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hU2 :
    Real.log (1175448789761 / 6400000000000 : ℝ) ≤
      (-(8473239830903755215511 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1175448789761 / 6400000000000 : ℝ) = (1175448789761 / 800000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (1175448789761 / 800000000000 : ℚ))
             (U := (1923967873596244784489 / 5000000000000000000000 : ℚ))
             10 (by decide +kernel)) :
          Real.log (1175448789761 / 800000000000 : ℝ) ≤
            (1923967873596244784489 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau297 :
    Real.arctan (4219465290770341 / 10000000000000000 : ℝ) ≤
      (1996407449528079098729 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4219465290770341 / 10000000000000000 : ℚ))
        (U := (1996407449528079098729 / 5000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (1996407449528079098729 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4219465290770341 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4219465290770341 : ℝ) =
              (4219465290770341 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau297)
  have hat2 :
    Real.arctan (375000000000000 / 2109732645385169 : ℝ) ≤
      (879552057096567979033 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 2109732645385169 : ℚ))
        (U := (879552057096567979033 / 5000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1139448789761 / 6400000000000 : ℚ))
      (lo := (2109732645385169 / 5000000000000000 : ℚ))
      (hi := (4219465290770341 / 10000000000000000 : ℚ))
      (s := (2109732645385169 / 5000000000000000 : ℚ))
      (r₁ := (7539448789761 / 6400000000000 : ℚ))
      (r₂ := (1175448789761 / 6400000000000 : ℚ))
      (z₁ := (10000000000000000 / 4219465290770341 : ℚ))
      (z₂ := (375000000000000 / 2109732645385169 : ℚ))
      (L := (8192554208785925893 / 50000000000000000000 : ℚ))
      (U := (-(8473239830903755215511 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_236 :
    ((25836900440478381773 / 156250000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2106291672941955151379 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4240439240248289 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4010605638583281302999 / 10000000000000000000000 : ℝ)) -
              6 * (54705636809765470191 / 312500000000000000000 : ℝ)))) ≤
      Vfield (1438505996019 / 8000000000000 : ℝ) := by
  have hL1 :
    (25836900440478381773 / 156250000000000000000 : ℝ) ≤
      Real.log (9438505996019 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (9438505996019 / 8000000000000 : ℚ))
        (L := (25836900440478381773 / 156250000000000000000 : ℚ))
        7 (by decide +kernel))
  have hU2 :
    Real.log (1483505996019 / 8000000000000 : ℝ) ≤
      (-(2106291672941955151379 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1483505996019 / 8000000000000 : ℝ) = (1483505996019 / 1000000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (1483505996019 / 1000000000000 : ℚ))
             (U := (493010253183044848621 / 1250000000000000000000 : ℚ))
             10 (by decide +kernel)) :
          Real.log (1483505996019 / 1000000000000 : ℝ) ≤
            (493010253183044848621 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau298 :
    Real.arctan (1060109810062073 / 2500000000000000 : ℝ) ≤
      (4010605638583281302999 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (1060109810062073 / 2500000000000000 : ℚ))
        (U := (4010605638583281302999 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (4010605638583281302999 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (2500000000000000 / 1060109810062073 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (2500000000000000 / 1060109810062073 : ℝ) =
              (1060109810062073 / 2500000000000000 : ℝ)
            by
        norm_num];
        exact hau298)
  have hat2 :
    Real.arctan (750000000000000 / 4240439240248289 : ℝ) ≤
      (54705636809765470191 / 312500000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (750000000000000 / 4240439240248289 : ℚ))
        (U := (54705636809765470191 / 312500000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1438505996019 / 8000000000000 : ℚ))
      (lo := (4240439240248289 / 10000000000000000 : ℚ))
      (hi := (1060109810062073 / 2500000000000000 : ℚ))
      (s := (4240439240248289 / 10000000000000000 : ℚ))
      (r₁ := (9438505996019 / 8000000000000 : ℚ))
      (r₂ := (1483505996019 / 8000000000000 : ℚ))
      (z₁ := (2500000000000000 / 1060109810062073 : ℚ))
      (z₂ := (750000000000000 / 4240439240248289 : ℚ))
      (L := (25836900440478381773 / 156250000000000000000 : ℚ))
      (U := (-(2106291672941955151379 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_237 :
    ((1683595413202401175063 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(8330385197728652168027 / 5000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2141039477139623 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4045846230365333599963 / 10000000000000000000000 : ℝ)) -
              6 * (86694908410619904871 / 500000000000000000000 : ℝ)))) ≤
      Vfield (2933792027309 / 16000000000000 : ℝ) := by
  have hL1 :
    (1683595413202401175063 / 10000000000000000000000 : ℝ) ≤
      Real.log (18933792027309 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (18933792027309 / 16000000000000 : ℚ))
        (L := (1683595413202401175063 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hU2 :
    Real.log (3023792027309 / 16000000000000 : ℝ) ≤
      (-(8330385197728652168027 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3023792027309 / 16000000000000 : ℝ) = (3023792027309 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (3023792027309 / 2000000000000 : ℚ))
             (U := (2066822506771347831973 / 5000000000000000000000 : ℚ))
             10 (by decide +kernel)) :
          Real.log (3023792027309 / 2000000000000 : ℝ) ≤
            (2066822506771347831973 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau299 :
    Real.arctan (4282078954279249 / 10000000000000000 : ℝ) ≤
      (4045846230365333599963 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4282078954279249 / 10000000000000000 : ℚ))
        (U := (4045846230365333599963 / 10000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (4045846230365333599963 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4282078954279249 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4282078954279249 : ℝ) =
              (4282078954279249 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau299)
  have hat2 :
    Real.arctan (375000000000000 / 2141039477139623 : ℝ) ≤
      (86694908410619904871 / 500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 2141039477139623 : ℚ))
        (U := (86694908410619904871 / 500000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (2933792027309 / 16000000000000 : ℚ))
      (lo := (2141039477139623 / 5000000000000000 : ℚ))
      (hi := (4282078954279249 / 10000000000000000 : ℚ))
      (s := (2141039477139623 / 5000000000000000 : ℚ))
      (r₁ := (18933792027309 / 16000000000000 : ℚ))
      (r₂ := (3023792027309 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 4282078954279249 : ℚ))
      (z₂ := (375000000000000 / 2141039477139623 : ℚ))
      (L := (1683595413202401175063 / 10000000000000000000000 : ℚ))
      (U := (-(8330385197728652168027 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_238 :
    ((1713539265424779612481 / 10000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(2059341758896377698357 / 1250000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2161658818542197 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2040321455583755349747 / 5000000000000000000000 : ℝ)) -
              6 * (343536800730602077419 / 2000000000000000000000 : ℝ)))) ≤
      Vfield (149528603129 / 800000000000 : ℝ) := by
  have hL1 :
    (1713539265424779612481 / 10000000000000000000000 : ℝ) ≤
      Real.log (949528603129 / 800000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (949528603129 / 800000000000 : ℚ))
        (L := (1713539265424779612481 / 10000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hU2 :
    Real.log (154028603129 / 800000000000 : ℝ) ≤
      (-(2059341758896377698357 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (154028603129 / 800000000000 : ℝ) = (154028603129 / 100000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (154028603129 / 100000000000 : ℚ))
             (U := (539960167228622301643 / 1250000000000000000000 : ℚ))
             10 (by decide +kernel)) :
          Real.log (154028603129 / 100000000000 : ℝ) ≤
            (539960167228622301643 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau300 :
    Real.arctan (4323317637084397 / 10000000000000000 : ℝ) ≤
      (2040321455583755349747 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4323317637084397 / 10000000000000000 : ℚ))
        (U := (2040321455583755349747 / 5000000000000000000000 : ℚ))
        9 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2040321455583755349747 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4323317637084397 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4323317637084397 : ℝ) =
              (4323317637084397 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau300)
  have hat2 :
    Real.arctan (375000000000000 / 2161658818542197 : ℝ) ≤
      (343536800730602077419 / 2000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 2161658818542197 : ℚ))
        (U := (343536800730602077419 / 2000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (149528603129 / 800000000000 : ℚ))
      (lo := (2161658818542197 / 5000000000000000 : ℚ))
      (hi := (4323317637084397 / 10000000000000000 : ℚ))
      (s := (2161658818542197 / 5000000000000000 : ℚ))
      (r₁ := (949528603129 / 800000000000 : ℚ))
      (r₂ := (154028603129 / 800000000000 : ℚ))
      (z₁ := (10000000000000000 / 4323317637084397 : ℚ))
      (z₂ := (375000000000000 / 2161658818542197 : ℚ))
      (L := (1713539265424779612481 / 10000000000000000000000 : ℚ))
      (U := (-(2059341758896377698357 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_239 :
    ((871696860918730643327 / 5000000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(16292095582403450641143 / 10000000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((2182083328585823 / 5000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (4115007895609233887117 / 10000000000000000000000 : ℝ)) -
              6 * (1701916397919497671761 / 10000000000000000000000 : ℝ)))) ≤
      Vfield (3047352097851 / 16000000000000 : ℝ) := by
  have hL1 :
    (871696860918730643327 / 5000000000000000000000 : ℝ) ≤
      Real.log (19047352097851 / 16000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (19047352097851 / 16000000000000 : ℚ))
        (L := (871696860918730643327 / 5000000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hU2 :
    Real.log (3137352097851 / 16000000000000 : ℝ) ≤
      (-(16292095582403450641143 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (3137352097851 / 16000000000000 : ℝ) = (3137352097851 / 2000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (3137352097851 / 2000000000000 : ℚ))
             (U := (4502319826596549358857 / 10000000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (3137352097851 / 2000000000000 : ℝ) ≤
            (4502319826596549358857 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau301 :
    Real.arctan (4364166657171649 / 10000000000000000 : ℝ) ≤
      (4115007895609233887117 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (4364166657171649 / 10000000000000000 : ℚ))
        (U := (4115007895609233887117 / 10000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (4115007895609233887117 / 10000000000000000000000 : ℝ)) ≤
      Real.arctan (10000000000000000 / 4364166657171649 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (10000000000000000 / 4364166657171649 : ℝ) =
              (4364166657171649 / 10000000000000000 : ℝ)
            by
        norm_num];
        exact hau301)
  have hat2 :
    Real.arctan (375000000000000 / 2182083328585823 : ℝ) ≤
      (1701916397919497671761 / 10000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (375000000000000 / 2182083328585823 : ℚ))
        (U := (1701916397919497671761 / 10000000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (3047352097851 / 16000000000000 : ℚ))
      (lo := (2182083328585823 / 5000000000000000 : ℚ))
      (hi := (4364166657171649 / 10000000000000000 : ℚ))
      (s := (2182083328585823 / 5000000000000000 : ℚ))
      (r₁ := (19047352097851 / 16000000000000 : ℚ))
      (r₂ := (3137352097851 / 16000000000000 : ℚ))
      (z₁ := (10000000000000000 / 4364166657171649 : ℚ))
      (z₂ := (375000000000000 / 2182083328585823 : ℚ))
      (L := (871696860918730643327 / 5000000000000000000000 : ℚ))
      (U := (-(16292095582403450641143 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

lemma V_240 :
    ((443289828656272310679 / 2500000000000000000000 : ℝ) -
              6 * (3 / 40) * (-(4028183258387475971649 / 2500000000000000000000 : ℝ)) -
            2 +
          12 * (3 / 40) +
        2 *
          ((4404636855861387 / 10000000000000000 : ℝ) *
            (Real.pi + (Real.pi / 2 - (2074476423521889182987 / 5000000000000000000000 : ℝ)) -
              6 * (421643805205669706173 / 2500000000000000000000 : ℝ)))) ≤
      Vfield (1552066066561 / 8000000000000 : ℝ) := by
  have hL1 :
    (443289828656272310679 / 2500000000000000000000 : ℝ) ≤
      Real.log (9552066066561 / 8000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_ge_of_ge_one_rat
        (r := (9552066066561 / 8000000000000 : ℚ))
        (L := (443289828656272310679 / 2500000000000000000000 : ℚ))
        7 (by decide +kernel))
  have hU2 :
    Real.log (1597066066561 / 8000000000000 : ℝ) ≤
      (-(4028183258387475971649 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (1597066066561 / 8000000000000 : ℝ) = (1597066066561 / 1000000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        ((by
           simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using log_le_of_ge_one_rat
             (r := (1597066066561 / 1000000000000 : ℚ))
             (U := (1170420593862524028351 / 2500000000000000000000 : ℚ))
             11 (by decide +kernel)) :
          Real.log (1597066066561 / 1000000000000 : ℝ) ≤
            (1170420593862524028351 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  have hau302 :
    Real.arctan (440463685586139 / 1000000000000000 : ℝ) ≤
      (2074476423521889182987 / 5000000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (440463685586139 / 1000000000000000 : ℚ))
        (U := (2074476423521889182987 / 5000000000000000000000 : ℚ))
        10 (by decide +kernel))
  have hat1 :
    (Real.pi / 2 - (2074476423521889182987 / 5000000000000000000000 : ℝ)) ≤
      Real.arctan (1000000000000000 / 440463685586139 : ℝ) :=
    arctan_ge_inv (by norm_num)
      (by
        rw [show
            (1 : ℝ) / (1000000000000000 / 440463685586139 : ℝ) =
              (440463685586139 / 1000000000000000 : ℝ)
            by
        norm_num];
        exact hau302)
  have hat2 :
    Real.arctan (250000000000000 / 1468212285287129 : ℝ) ≤
      (421643805205669706173 / 2500000000000000000000 : ℝ) :=
    (by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using arctan_le_of_series_rat
        (z := (250000000000000 / 1468212285287129 : ℚ))
        (U := (421643805205669706173 / 2500000000000000000000 : ℚ))
        5 (by decide +kernel))
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
    Vfield_lower_certificate
      (t := (1552066066561 / 8000000000000 : ℚ))
      (lo := (4404636855861387 / 10000000000000000 : ℚ))
      (hi := (440463685586139 / 1000000000000000 : ℚ))
      (s := (4404636855861387 / 10000000000000000 : ℚ))
      (r₁ := (9552066066561 / 8000000000000 : ℚ))
      (r₂ := (1597066066561 / 8000000000000 : ℚ))
      (z₁ := (1000000000000000 / 440463685586139 : ℚ))
      (z₂ := (250000000000000 / 1468212285287129 : ℚ))
      (L := (443289828656272310679 / 2500000000000000000000 : ℚ))
      (U := (-(4028183258387475971649 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hL1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hU2)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat1)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using hat2)
      (Or.inl ⟨rfl, by linarith only [Real.pi_gt_d20, Real.pi_lt_d20]⟩)

end Zeta5Irrational
