/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Real.Pi.Bounds
import LeanPool.Zeta5Irrational.Table.U42
import LeanPool.Zeta5Irrational.Table.U43
import LeanPool.Zeta5Irrational.Table.U44
import LeanPool.Zeta5Irrational.Table.U45
import LeanPool.Zeta5Irrational.Table.U46
import LeanPool.Zeta5Irrational.Table.U47
import LeanPool.Zeta5Irrational.Table.U48
import LeanPool.Zeta5Irrational.Table.U49
import LeanPool.Zeta5Irrational.Table.U50
import LeanPool.Zeta5Irrational.Table.U51
import LeanPool.Zeta5Irrational.Table.U52
import LeanPool.Zeta5Irrational.Table.U53
import LeanPool.Zeta5Irrational.Table.U54
import LeanPool.Zeta5Irrational.Table.U55
import LeanPool.Zeta5Irrational.Table.U56
import LeanPool.Zeta5Irrational.Table.V42
import LeanPool.Zeta5Irrational.Table.V43
import LeanPool.Zeta5Irrational.Table.V44
import LeanPool.Zeta5Irrational.Table.V45
import LeanPool.Zeta5Irrational.Table.V46
import LeanPool.Zeta5Irrational.Table.V47
import LeanPool.Zeta5Irrational.Table.V48
import LeanPool.Zeta5Irrational.Table.V49
import LeanPool.Zeta5Irrational.Table.V50
import LeanPool.Zeta5Irrational.Table.V51
import LeanPool.Zeta5Irrational.Table.V52
import LeanPool.Zeta5Irrational.Table.V53
import LeanPool.Zeta5Irrational.Table.V54
import LeanPool.Zeta5Irrational.Table.V55
import LeanPool.Zeta5Irrational.Table.V56

/-! # Interval certificates 513 through 683

These independent endpoint checks use only the corresponding upper and lower table bounds.
The covering argument is assembled in `LeanPool.Zeta5Irrational.Table.Intervals`.
-/

@[expose] public section

open Finset

namespace Zeta5Irrational

lemma tc_513 :
    ∀ t,
      (36111549776069 / 64000000000000 : ℝ) ≤ t →
        t ≤ (4523929582263 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_514 V_513
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_514 :
    ∀ t,
      (4523929582263 / 8000000000000 : ℝ) ≤ t →
        t ≤ (18175605211087 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_515 V_514
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_515 :
    ∀ t,
      (18175605211087 / 32000000000000 : ℝ) ≤ t →
        t ≤ (9127746046561 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_516 V_515
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_516 :
    ∀ t,
      (9127746046561 / 16000000000000 : ℝ) ≤ t →
        t ≤ (18335378975157 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_517 V_516
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_517 :
    ∀ t,
      (18335378975157 / 32000000000000 : ℝ) ≤ t →
        t ≤ (2301908232149 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_518 V_517
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_518 :
    ∀ t,
      (2301908232149 / 4000000000000 : ℝ) ≤ t →
        t ≤ (18495152739227 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_519 V_518
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_519 :
    ∀ t,
      (18495152739227 / 32000000000000 : ℝ) ≤ t →
        t ≤ (9287519810631 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_520 V_519
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_520 :
    ∀ t,
      (9287519810631 / 16000000000000 : ℝ) ≤ t →
        t ≤ (4683703346333 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_521 V_520
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_521 :
    ∀ t,
      (4683703346333 / 8000000000000 : ℝ) ≤ t →
        t ≤ (9447293574701 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_522 V_521
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_522 :
    ∀ t,
      (9447293574701 / 16000000000000 : ℝ) ≤ t →
        t ≤ (297724389273 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_523 V_522
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_523 :
    ∀ t,
      (297724389273 / 500000000000 : ℝ) ≤ t →
        t ≤ (19123153518409 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_524 V_523
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_524 :
    ∀ t,
      (19123153518409 / 32000000000000 : ℝ) ≤ t →
        t ≤ (9595973061673 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_525 V_524
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_525 :
    ∀ t,
      (9595973061673 / 16000000000000 : ℝ) ≤ t →
        t ≤ (19260738728283 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_526 V_525
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_526 :
    ∀ t,
      (19260738728283 / 32000000000000 : ℝ) ≤ t →
        t ≤ (38590270061503 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_527 V_526
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_527 :
    ∀ t,
      (38590270061503 / 64000000000000 : ℝ) ≤ t →
        t ≤ (966476566661 / 1600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_528 V_527
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_528 :
    ∀ t,
      (966476566661 / 1600000000000 : ℝ) ≤ t →
        t ≤ (38727855271377 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_529 V_528
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_529 :
    ∀ t,
      (38727855271377 / 64000000000000 : ℝ) ≤ t →
        t ≤ (19398323938157 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_530 V_529
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_530 :
    ∀ t,
      (19398323938157 / 32000000000000 : ℝ) ≤ t →
        t ≤ (38865440481251 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_531 V_530
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_531 :
    ∀ t,
      (38865440481251 / 64000000000000 : ℝ) ≤ t →
        t ≤ (9733558271547 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_532 V_531
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_532 :
    ∀ t,
      (9733558271547 / 16000000000000 : ℝ) ≤ t →
        t ≤ (312024205529 / 512000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_533 V_532
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_533 :
    ∀ t,
      (312024205529 / 512000000000 : ℝ) ≤ t →
        t ≤ (19535909148031 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_534 V_533
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_534 :
    ∀ t,
      (19535909148031 / 32000000000000 : ℝ) ≤ t →
        t ≤ (39140610900999 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_535 V_534
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_535 :
    ∀ t,
      (39140610900999 / 64000000000000 : ℝ) ≤ t →
        t ≤ (2450587719121 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_536 V_535
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_536 :
    ∀ t,
      (2450587719121 / 4000000000000 : ℝ) ≤ t →
        t ≤ (39278196110873 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_537 V_536
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_537 :
    ∀ t,
      (39278196110873 / 64000000000000 : ℝ) ≤ t →
        t ≤ (3934698871581 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_538 V_537
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_538 :
    ∀ t,
      (3934698871581 / 6400000000000 : ℝ) ≤ t →
        t ≤ (39415781320747 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_539 V_538
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_539 :
    ∀ t,
      (39415781320747 / 64000000000000 : ℝ) ≤ t →
        t ≤ (9871143481421 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_540 V_539
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_540 :
    ∀ t,
      (9871143481421 / 16000000000000 : ℝ) ≤ t →
        t ≤ (39553366530621 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_541 V_540
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_541 :
    ∀ t,
      (39553366530621 / 64000000000000 : ℝ) ≤ t →
        t ≤ (19811079567779 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_542 V_541
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_542 :
    ∀ t,
      (19811079567779 / 32000000000000 : ℝ) ≤ t →
        t ≤ (7938190348099 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_543 V_542
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_543 :
    ∀ t,
      (7938190348099 / 12800000000000 : ℝ) ≤ t →
        t ≤ (4969968043179 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_544 V_543
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_544 :
    ∀ t,
      (4969968043179 / 8000000000000 : ℝ) ≤ t →
        t ≤ (39828536950369 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_545 V_544
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_545 :
    ∀ t,
      (39828536950369 / 64000000000000 : ℝ) ≤ t →
        t ≤ (19948664777653 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_546 V_545
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_546 :
    ∀ t,
      (19948664777653 / 32000000000000 : ℝ) ≤ t →
        t ≤ (39966122160243 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_547 V_546
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_547 :
    ∀ t,
      (39966122160243 / 64000000000000 : ℝ) ≤ t →
        t ≤ (2001745738259 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_548 V_547
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_548 :
    ∀ t,
      (2001745738259 / 3200000000000 : ℝ) ≤ t →
        t ≤ (40103707370117 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_549 V_548
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_549 :
    ∀ t,
      (40103707370117 / 64000000000000 : ℝ) ≤ t →
        t ≤ (20086249987527 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_550 V_549
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_550 :
    ∀ t,
      (20086249987527 / 32000000000000 : ℝ) ≤ t →
        t ≤ (40241292579991 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_551 V_550
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_551 :
    ∀ t,
      (40241292579991 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1259690162029 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_552 V_551
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_552 :
    ∀ t,
      (1259690162029 / 2000000000000 : ℝ) ≤ t →
        t ≤ (8075775557973 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_553 V_552
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_553 :
    ∀ t,
      (8075775557973 / 12800000000000 : ℝ) ≤ t →
        t ≤ (20223835197401 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_554 V_553
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_554 :
    ∀ t,
      (20223835197401 / 32000000000000 : ℝ) ≤ t →
        t ≤ (40516462999739 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_555 V_554
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_555 :
    ∀ t,
      (40516462999739 / 64000000000000 : ℝ) ≤ t →
        t ≤ (10146313901169 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_556 V_555
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_556 :
    ∀ t,
      (10146313901169 / 16000000000000 : ℝ) ≤ t →
        t ≤ (40654048209613 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_557 V_556
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_557 :
    ∀ t,
      (40654048209613 / 64000000000000 : ℝ) ≤ t →
        t ≤ (814456816291 / 1280000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_558 V_557
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_558 :
    ∀ t,
      (814456816291 / 1280000000000 : ℝ) ≤ t →
        t ≤ (40791633419487 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_559 V_558
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_559 :
    ∀ t,
      (40791633419487 / 64000000000000 : ℝ) ≤ t →
        t ≤ (5107553253053 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_560 V_559
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_560 :
    ∀ t,
      (5107553253053 / 8000000000000 : ℝ) ≤ t →
        t ≤ (20499005617149 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_561 V_560
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_561 :
    ∀ t,
      (20499005617149 / 32000000000000 : ℝ) ≤ t →
        t ≤ (10283899111043 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_562 V_561
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_562 :
    ∀ t,
      (10283899111043 / 16000000000000 : ℝ) ≤ t →
        t ≤ (20636590827023 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_563 V_562
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_563 :
    ∀ t,
      (20636590827023 / 32000000000000 : ℝ) ≤ t →
        t ≤ (517634585799 / 800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_564 V_563
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_564 :
    ∀ t,
      (517634585799 / 800000000000 : ℝ) ≤ t →
        t ≤ (20774176036897 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_565 V_564
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_565 :
    ∀ t,
      (20774176036897 / 32000000000000 : ℝ) ≤ t →
        t ≤ (10421484320917 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_566 V_565
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_566 :
    ∀ t,
      (10421484320917 / 16000000000000 : ℝ) ≤ t →
        t ≤ (20911761246771 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_567 V_566
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_567 :
    ∀ t,
      (20911761246771 / 32000000000000 : ℝ) ≤ t →
        t ≤ (5245138462927 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_568 V_567
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_568 :
    ∀ t,
      (5245138462927 / 8000000000000 : ℝ) ≤ t →
        t ≤ (10559069530791 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_569 V_568
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_569 :
    ∀ t,
      (10559069530791 / 16000000000000 : ℝ) ≤ t →
        t ≤ (664241383483 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_570 V_569
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_570 :
    ∀ t,
      (664241383483 / 1000000000000 : ℝ) ≤ t →
        t ≤ (4261528693017 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_571 V_570
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_571 :
    ∀ t,
      (4261528693017 / 6400000000000 : ℝ) ≤ t →
        t ≤ (10679781329357 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_572 V_571
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_572 :
    ∀ t,
      (10679781329357 / 16000000000000 : ℝ) ≤ t →
        t ≤ (21411481852343 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_573 V_572
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_573 :
    ∀ t,
      (21411481852343 / 32000000000000 : ℝ) ≤ t →
        t ≤ (5365850261493 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_574 V_573
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_574 :
    ∀ t,
      (5365850261493 / 8000000000000 : ℝ) ≤ t →
        t ≤ (21515320239601 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_575 V_574
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_575 :
    ∀ t,
      (21515320239601 / 32000000000000 : ℝ) ≤ t →
        t ≤ (43082559672831 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_576 V_575
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_576 :
    ∀ t,
      (43082559672831 / 64000000000000 : ℝ) ≤ t →
        t ≤ (2156723943323 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_577 V_576
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_577 :
    ∀ t,
      (2156723943323 / 3200000000000 : ℝ) ≤ t →
        t ≤ (43186398060089 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_578 V_577
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_578 :
    ∀ t,
      (43186398060089 / 64000000000000 : ℝ) ≤ t →
        t ≤ (21619158626859 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_579 V_578
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_579 :
    ∀ t,
      (21619158626859 / 32000000000000 : ℝ) ≤ t →
        t ≤ (43290236447347 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_580 V_579
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_580 :
    ∀ t,
      (43290236447347 / 64000000000000 : ℝ) ≤ t →
        t ≤ (2708884727561 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_581 V_580
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_581 :
    ∀ t,
      (2708884727561 / 4000000000000 : ℝ) ≤ t →
        t ≤ (8678814966921 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_582 V_581
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_582 :
    ∀ t,
      (8678814966921 / 12800000000000 : ℝ) ≤ t →
        t ≤ (21722997014117 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_583 V_582
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_583 :
    ∀ t,
      (21722997014117 / 32000000000000 : ℝ) ≤ t →
        t ≤ (43497913221863 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_584 V_583
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_584 :
    ∀ t,
      (43497913221863 / 64000000000000 : ℝ) ≤ t →
        t ≤ (10887458103873 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_585 V_584
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_585 :
    ∀ t,
      (10887458103873 / 16000000000000 : ℝ) ≤ t →
        t ≤ (43601751609121 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_586 V_585
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_586 :
    ∀ t,
      (43601751609121 / 64000000000000 : ℝ) ≤ t →
        t ≤ (174614683211 / 256000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_587 V_586
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_587 :
    ∀ t,
      (174614683211 / 256000000000 : ℝ) ≤ t →
        t ≤ (43705589996379 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_588 V_587
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_588 :
    ∀ t,
      (43705589996379 / 64000000000000 : ℝ) ≤ t →
        t ≤ (5469688648751 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_589 V_588
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_589 :
    ∀ t,
      (5469688648751 / 8000000000000 : ℝ) ≤ t →
        t ≤ (43809428383637 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_590 V_589
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_590 :
    ∀ t,
      (43809428383637 / 64000000000000 : ℝ) ≤ t →
        t ≤ (21930673788633 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_591 V_590
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_591 :
    ∀ t,
      (21930673788633 / 32000000000000 : ℝ) ≤ t →
        t ≤ (8782653354179 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_592 V_591
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_592 :
    ∀ t,
      (8782653354179 / 12800000000000 : ℝ) ≤ t →
        t ≤ (10991296491131 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_593 V_592
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_593 :
    ∀ t,
      (10991296491131 / 16000000000000 : ℝ) ≤ t →
        t ≤ (44017105158153 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_594 V_593
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_594 :
    ∀ t,
      (44017105158153 / 64000000000000 : ℝ) ≤ t →
        t ≤ (22034512175891 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_595 V_594
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_595 :
    ∀ t,
      (22034512175891 / 32000000000000 : ℝ) ≤ t →
        t ≤ (44120943545411 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_596 V_595
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_596 :
    ∀ t,
      (44120943545411 / 64000000000000 : ℝ) ≤ t →
        t ≤ (276080392119 / 400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_597 V_596
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_597 :
    ∀ t,
      (276080392119 / 400000000000 : ℝ) ≤ t →
        t ≤ (44224781932669 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_598 V_597
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_598 :
    ∀ t,
      (44224781932669 / 64000000000000 : ℝ) ≤ t →
        t ≤ (22138350563149 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_599 V_598
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_599 :
    ∀ t,
      (22138350563149 / 32000000000000 : ℝ) ≤ t →
        t ≤ (44328620319927 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_600 V_599
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_600 :
    ∀ t,
      (44328620319927 / 64000000000000 : ℝ) ≤ t →
        t ≤ (11095134878389 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_601 V_600
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_601 :
    ∀ t,
      (11095134878389 / 16000000000000 : ℝ) ≤ t →
        t ≤ (8886491741437 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_602 V_601
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_602 :
    ∀ t,
      (8886491741437 / 12800000000000 : ℝ) ≤ t →
        t ≤ (22242188950407 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_603 V_602
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_603 :
    ∀ t,
      (22242188950407 / 32000000000000 : ℝ) ≤ t →
        t ≤ (5573527036009 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_604 V_603
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_604 :
    ∀ t,
      (5573527036009 / 8000000000000 : ℝ) ≤ t →
        t ≤ (4469205467533 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_605 V_604
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_605 :
    ∀ t,
      (4469205467533 / 6400000000000 : ℝ) ≤ t →
        t ≤ (11198973265647 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_606 V_605
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_606 :
    ∀ t,
      (11198973265647 / 16000000000000 : ℝ) ≤ t →
        t ≤ (22449865724923 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_607 V_606
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_607 :
    ∀ t,
      (22449865724923 / 32000000000000 : ℝ) ≤ t →
        t ≤ (2812723114819 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_608 V_607
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_608 :
    ∀ t,
      (2812723114819 / 4000000000000 : ℝ) ≤ t →
        t ≤ (22553704112181 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_609 V_608
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_609 :
    ∀ t,
      (22553704112181 / 32000000000000 : ℝ) ≤ t →
        t ≤ (2260562330581 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_610 V_609
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_610 :
    ∀ t,
      (2260562330581 / 3200000000000 : ℝ) ≤ t →
        t ≤ (22657542499439 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_611 V_610
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_611 :
    ∀ t,
      (22657542499439 / 32000000000000 : ℝ) ≤ t →
        t ≤ (5677365423267 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_612 V_611
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_612 :
    ∀ t,
      (5677365423267 / 8000000000000 : ℝ) ≤ t →
        t ≤ (22761380886697 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_613 V_612
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_613 :
    ∀ t,
      (22761380886697 / 32000000000000 : ℝ) ≤ t →
        t ≤ (11406650040163 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_614 V_613
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_614 :
    ∀ t,
      (11406650040163 / 16000000000000 : ℝ) ≤ t →
        t ≤ (89520072139 / 125000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_615 V_614
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_615 :
    ∀ t,
      (89520072139 / 125000000000 : ℝ) ≤ t →
        t ≤ (11489045952349 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_616 V_615
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_616 :
    ∀ t,
      (11489045952349 / 16000000000000 : ℝ) ≤ t →
        t ≤ (4601713724651 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_617 V_616
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_617 :
    ∀ t,
      (4601713724651 / 6400000000000 : ℝ) ≤ t →
        t ≤ (5759761335453 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_618 V_617
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_618 :
    ∀ t,
      (5759761335453 / 8000000000000 : ℝ) ≤ t →
        t ≤ (23069522060369 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_619 V_618
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_619 :
    ∀ t,
      (23069522060369 / 32000000000000 : ℝ) ≤ t →
        t ≤ (11549999389463 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_620 V_619
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_620 :
    ∀ t,
      (11549999389463 / 16000000000000 : ℝ) ≤ t →
        t ≤ (23130475497483 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_621 V_620
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_621 :
    ∀ t,
      (23130475497483 / 32000000000000 : ℝ) ≤ t →
        t ≤ (579023805401 / 800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_622 V_621
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_622 :
    ∀ t,
      (579023805401 / 800000000000 : ℝ) ≤ t →
        t ≤ (23191428934597 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_623 V_622
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_623 :
    ∀ t,
      (23191428934597 / 32000000000000 : ℝ) ≤ t →
        t ≤ (11610952826577 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_624 V_623
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_624 :
    ∀ t,
      (11610952826577 / 16000000000000 : ℝ) ≤ t →
        t ≤ (23252382371711 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_625 V_624
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_625 :
    ∀ t,
      (23252382371711 / 32000000000000 : ℝ) ≤ t →
        t ≤ (5820714772567 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_626 V_625
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_626 :
    ∀ t,
      (5820714772567 / 8000000000000 : ℝ) ≤ t →
        t ≤ (932533432353 / 1280000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_627 V_626
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_627 :
    ∀ t,
      (932533432353 / 1280000000000 : ℝ) ≤ t →
        t ≤ (11671906263691 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_628 V_627
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_628 :
    ∀ t,
      (11671906263691 / 16000000000000 : ℝ) ≤ t →
        t ≤ (23374289245939 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_629 V_628
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_629 :
    ∀ t,
      (23374289245939 / 32000000000000 : ℝ) ≤ t →
        t ≤ (1462797872781 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_630 V_629
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_630 :
    ∀ t,
      (1462797872781 / 2000000000000 : ℝ) ≤ t →
        t ≤ (23435242683053 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_631 V_630
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_631 :
    ∀ t,
      (23435242683053 / 32000000000000 : ℝ) ≤ t →
        t ≤ (2346571940161 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_632 V_631
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_632 :
    ∀ t,
      (2346571940161 / 3200000000000 : ℝ) ≤ t →
        t ≤ (23496196120167 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_633 V_632
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_633 :
    ∀ t,
      (23496196120167 / 32000000000000 : ℝ) ≤ t →
        t ≤ (5881668209681 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_634 V_633
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_634 :
    ∀ t,
      (5881668209681 / 8000000000000 : ℝ) ≤ t →
        t ≤ (23557149557281 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_635 V_634
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_635 :
    ∀ t,
      (23557149557281 / 32000000000000 : ℝ) ≤ t →
        t ≤ (11793813137919 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_636 V_635
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_636 :
    ∀ t,
      (11793813137919 / 16000000000000 : ℝ) ≤ t →
        t ≤ (4723620598879 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_637 V_636
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_637 :
    ∀ t,
      (4723620598879 / 6400000000000 : ℝ) ≤ t →
        t ≤ (2956072464119 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_638 V_637
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_638 :
    ∀ t,
      (2956072464119 / 4000000000000 : ℝ) ≤ t →
        t ≤ (23679056431509 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_639 V_638
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_639 :
    ∀ t,
      (23679056431509 / 32000000000000 : ℝ) ≤ t →
        t ≤ (11854766575033 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_640 V_639
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_640 :
    ∀ t,
      (11854766575033 / 16000000000000 : ℝ) ≤ t →
        t ≤ (23740009868623 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_641 V_640
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_641 :
    ∀ t,
      (23740009868623 / 32000000000000 : ℝ) ≤ t →
        t ≤ (1188524329359 / 1600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_642 V_641
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_642 :
    ∀ t,
      (1188524329359 / 1600000000000 : ℝ) ≤ t →
        t ≤ (23800963305737 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_643 V_642
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_643 :
    ∀ t,
      (23800963305737 / 32000000000000 : ℝ) ≤ t →
        t ≤ (11915720012147 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_644 V_643
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_644 :
    ∀ t,
      (11915720012147 / 16000000000000 : ℝ) ≤ t →
        t ≤ (746637295669 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_645 V_644
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_645 :
    ∀ t,
      (746637295669 / 1000000000000 : ℝ) ≤ t →
        t ≤ (765809953469387 / 1024000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_646 V_645
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_646 :
    ∀ t,
      (765809953469387 / 1024000000000000 : ℝ) ≤ t →
        t ≤ (383531658086859 / 512000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_647 V_646
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_647 :
    ∀ t,
      (383531658086859 / 512000000000000 : ℝ) ≤ t →
        t ≤ (768316678878049 / 1024000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_648 V_647
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_648 :
    ∀ t,
      (768316678878049 / 1024000000000000 : ℝ) ≤ t →
        t ≤ (38478502079119 / 51200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_649 V_648
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_649 :
    ∀ t,
      (38478502079119 / 51200000000000 : ℝ) ≤ t →
        t ≤ (770823404286711 / 1024000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_650 V_649
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_650 :
    ∀ t,
      (770823404286711 / 1024000000000000 : ℝ) ≤ t →
        t ≤ (386038383495521 / 512000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_651 V_650
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_651 :
    ∀ t,
      (386038383495521 / 512000000000000 : ℝ) ≤ t →
        t ≤ (773330129695373 / 1024000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_652 V_651
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_652 :
    ∀ t,
      (773330129695373 / 1024000000000000 : ℝ) ≤ t →
        t ≤ (96822936549963 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_653 V_652
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_653 :
    ∀ t,
      (96822936549963 / 128000000000000 : ℝ) ≤ t →
        t ≤ (155167371020807 / 204800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_654 V_653
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_654 :
    ∀ t,
      (155167371020807 / 204800000000000 : ℝ) ≤ t →
        t ≤ (388545108904183 / 512000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_655 V_654
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_655 :
    ∀ t,
      (388545108904183 / 512000000000000 : ℝ) ≤ t →
        t ≤ (194899235804257 / 256000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_656 V_655
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_656 :
    ∀ t,
      (194899235804257 / 256000000000000 : ℝ) ≤ t →
        t ≤ (78210366862569 / 102400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_657 V_656
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_657 :
    ∀ t,
      (78210366862569 / 102400000000000 : ℝ) ≤ t →
        t ≤ (49038149627147 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_658 V_657
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_658 :
    ∀ t,
      (49038149627147 / 64000000000000 : ℝ) ≤ t →
        t ≤ (393558559721507 / 512000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_659 V_658
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_659 :
    ∀ t,
      (393558559721507 / 512000000000000 : ℝ) ≤ t →
        t ≤ (197405961212919 / 256000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_660 V_659
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_660 :
    ∀ t,
      (197405961212919 / 256000000000000 : ℝ) ≤ t →
        t ≤ (396065285130169 / 512000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_661 V_660
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_661 :
    ∀ t,
      (396065285130169 / 512000000000000 : ℝ) ≤ t →
        t ≤ (794637295669 / 1024000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_662 V_661
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_662 :
    ∀ t,
      (794637295669 / 1024000000000 : ℝ) ≤ t →
        t ≤ (398572010538831 / 512000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_663 V_662
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_663 :
    ∀ t,
      (398572010538831 / 512000000000000 : ℝ) ≤ t →
        t ≤ (199912686621581 / 256000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_664 V_663
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_664 :
    ∀ t,
      (199912686621581 / 256000000000000 : ℝ) ≤ t →
        t ≤ (25145756165739 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_665 V_664
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_665 :
    ∀ t,
      (25145756165739 / 32000000000000 : ℝ) ≤ t →
        t ≤ (202419412030243 / 256000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_666 V_665
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_666 :
    ∀ t,
      (202419412030243 / 256000000000000 : ℝ) ≤ t →
        t ≤ (101836387367287 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_667 V_666
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_667 :
    ∀ t,
      (101836387367287 / 128000000000000 : ℝ) ≤ t →
        t ≤ (40985227487781 / 51200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_668 V_667
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_668 :
    ∀ t,
      (40985227487781 / 51200000000000 : ℝ) ≤ t →
        t ≤ (51544875035809 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_669 V_668
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_669 :
    ∀ t,
      (51544875035809 / 64000000000000 : ℝ) ≤ t →
        t ≤ (104343112775949 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_670 V_669
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_670 :
    ∀ t,
      (104343112775949 / 128000000000000 : ℝ) ≤ t →
        t ≤ (2639911887007 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_671 V_670
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_671 :
    ∀ t,
      (2639911887007 / 3200000000000 : ℝ) ≤ t →
        t ≤ (106849838184611 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_672 V_671
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_672 :
    ∀ t,
      (106849838184611 / 128000000000000 : ℝ) ≤ t →
        t ≤ (54051600444471 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_673 V_672
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_673 :
    ∀ t,
      (54051600444471 / 64000000000000 : ℝ) ≤ t →
        t ≤ (27652481574401 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_674 V_673
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_674 :
    ∀ t,
      (27652481574401 / 32000000000000 : ℝ) ≤ t →
        t ≤ (56558325853133 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_675 V_674
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_675 :
    ∀ t,
      (56558325853133 / 64000000000000 : ℝ) ≤ t →
        t ≤ (7226461069683 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_676 V_675
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_676 :
    ∀ t,
      (7226461069683 / 8000000000000 : ℝ) ≤ t →
        t ≤ (30159206983063 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_677 V_676
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_677 :
    ∀ t,
      (30159206983063 / 32000000000000 : ℝ) ≤ t →
        t ≤ (15706284843697 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_678 V_677
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_678 :
    ∀ t,
      (15706284843697 / 16000000000000 : ℝ) ≤ t →
        t ≤ (4239911887007 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_679 V_678
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_679 :
    ∀ t,
      (4239911887007 / 4000000000000 : ℝ) ≤ t →
        t ≤ (18213010252359 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_680 V_679
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_680 :
    ∀ t,
      (18213010252359 / 16000000000000 : ℝ) ≤ t →
        t ≤ (1946637295669 / 1600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_681 V_680
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_681 :
    ∀ t,
      (1946637295669 / 1600000000000 : ℝ) ≤ t →
        t ≤ (2746637295669 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_682 V_681
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_682 :
    ∀ t,
      (2746637295669 / 2000000000000 : ℝ) ≤ t →
        t ≤ (6746637295669 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_683 V_682
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_683 :
    ∀ t,
      (6746637295669 / 4000000000000 : ℝ) ≤ t → t ≤ (2 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_684 V_683
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

end Zeta5Irrational
