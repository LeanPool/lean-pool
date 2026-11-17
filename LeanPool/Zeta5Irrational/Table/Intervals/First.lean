/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Real.Pi.Bounds
import LeanPool.Zeta5Irrational.Table.Bracket
import LeanPool.Zeta5Irrational.Table.U00
import LeanPool.Zeta5Irrational.Table.U01
import LeanPool.Zeta5Irrational.Table.U02
import LeanPool.Zeta5Irrational.Table.U03
import LeanPool.Zeta5Irrational.Table.U04
import LeanPool.Zeta5Irrational.Table.U05
import LeanPool.Zeta5Irrational.Table.U06
import LeanPool.Zeta5Irrational.Table.U07
import LeanPool.Zeta5Irrational.Table.U08
import LeanPool.Zeta5Irrational.Table.U09
import LeanPool.Zeta5Irrational.Table.U10
import LeanPool.Zeta5Irrational.Table.U11
import LeanPool.Zeta5Irrational.Table.U12
import LeanPool.Zeta5Irrational.Table.U13
import LeanPool.Zeta5Irrational.Table.V00
import LeanPool.Zeta5Irrational.Table.V01
import LeanPool.Zeta5Irrational.Table.V02
import LeanPool.Zeta5Irrational.Table.V03
import LeanPool.Zeta5Irrational.Table.V04
import LeanPool.Zeta5Irrational.Table.V05
import LeanPool.Zeta5Irrational.Table.V06
import LeanPool.Zeta5Irrational.Table.V07
import LeanPool.Zeta5Irrational.Table.V08
import LeanPool.Zeta5Irrational.Table.V09
import LeanPool.Zeta5Irrational.Table.V10
import LeanPool.Zeta5Irrational.Table.V11
import LeanPool.Zeta5Irrational.Table.V12
import LeanPool.Zeta5Irrational.Table.V13
import LeanPool.Zeta5Irrational.Table.V14

/-! # Interval certificates 0 through 170

These independent endpoint checks use only the corresponding upper and lower table bounds.
The covering argument is assembled in `LeanPool.Zeta5Irrational.Table.Intervals`.
-/

@[expose] public section

open Finset

namespace Zeta5Irrational

lemma tc_0 :
    ∀ t, (0 : ℝ) ≤ t → t ≤ (7174131 / 200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_0 V_1
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_1 :
    ∀ t,
      (7174131 / 200000000000 : ℝ) ≤ t →
        t ≤ (21522393 / 400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_1 V_2
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_2 :
    ∀ t,
      (21522393 / 400000000000 : ℝ) ≤ t →
        t ≤ (7174131 / 100000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_2 V_3
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_3 :
    ∀ t,
      (7174131 / 100000000000 : ℝ) ≤ t →
        t ≤ (14825913 / 200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_3 V_4
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_4 :
    ∀ t,
      (14825913 / 200000000000 : ℝ) ≤ t →
        t ≤ (78667711 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_4 V_5
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_5 :
    ∀ t,
      (78667711 / 1000000000000 : ℝ) ≤ t →
        t ≤ (85815639 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_5 V_6
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_6 :
    ∀ t,
      (85815639 / 1000000000000 : ℝ) ≤ t →
        t ≤ (19269871 / 200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_6 V_7
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_7 :
    ∀ t,
      (19269871 / 200000000000 : ℝ) ≤ t →
        t ≤ (55761057 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_7 V_8
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_8 :
    ∀ t,
      (55761057 / 500000000000 : ℝ) ≤ t →
        t ≤ (33336783 / 250000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_8 V_9
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_9 :
    ∀ t,
      (33336783 / 250000000000 : ℝ) ≤ t →
        t ≤ (82548843 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_9 V_10
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_10 :
    ∀ t,
      (82548843 / 500000000000 : ℝ) ≤ t →
        t ≤ (53051547 / 250000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_10 V_11
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_11 :
    ∀ t,
      (53051547 / 250000000000 : ℝ) ≤ t →
        t ≤ (496117379 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_11 V_12
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_12 :
    ∀ t,
      (496117379 / 2000000000000 : ℝ) ≤ t →
        t ≤ (283911191 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_12 V_13
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_13 :
    ∀ t,
      (283911191 / 1000000000000 : ℝ) ≤ t →
        t ≤ (170058951 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_13 V_14
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_14 :
    ∀ t,
      (170058951 / 500000000000 : ℝ) ≤ t →
        t ≤ (396324613 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_14 V_15
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_15 :
    ∀ t,
      (396324613 / 1000000000000 : ℝ) ≤ t →
        t ≤ (974522519 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_15 V_16
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_16 :
    ∀ t,
      (974522519 / 2000000000000 : ℝ) ≤ t →
        t ≤ (289098953 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_16 V_17
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_17 :
    ∀ t,
      (289098953 / 500000000000 : ℝ) ≤ t →
        t ≤ (729961631 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_17 V_18
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_18 :
    ∀ t,
      (729961631 / 1000000000000 : ℝ) ≤ t →
        t ≤ (1611686987 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_18 V_19
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_19 :
    ∀ t,
      (1611686987 / 2000000000000 : ℝ) ≤ t →
        t ≤ (220431339 / 250000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_19 V_20
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_20 :
    ∀ t,
      (220431339 / 250000000000 : ℝ) ≤ t →
        t ≤ (4047462733 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_20 V_21
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_21 :
    ∀ t,
      (4047462733 / 4000000000000 : ℝ) ≤ t →
        t ≤ (2284012021 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_21 V_22
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_22 :
    ∀ t,
      (2284012021 / 2000000000000 : ℝ) ≤ t →
        t ≤ (5088585351 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_22 V_23
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_23 :
    ∀ t,
      (5088585351 / 4000000000000 : ℝ) ≤ t →
        t ≤ (280457333 / 200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_23 V_24
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_24 :
    ∀ t,
      (280457333 / 200000000000 : ℝ) ≤ t →
        t ≤ (6519108259 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_24 V_25
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_25 :
    ∀ t,
      (6519108259 / 4000000000000 : ℝ) ≤ t →
        t ≤ (3714534929 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_25 V_26
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_26 :
    ∀ t,
      (3714534929 / 2000000000000 : ℝ) ≤ t →
        t ≤ (8339031457 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_26 V_27
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_27 :
    ∀ t,
      (8339031457 / 4000000000000 : ℝ) ≤ t →
        t ≤ (289031033 / 125000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_27 V_28
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_28 :
    ∀ t,
      (289031033 / 125000000000 : ℝ) ≤ t →
        t ≤ (124379927 / 40000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_28 V_29
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_29 :
    ∀ t,
      (124379927 / 40000000000 : ℝ) ≤ t →
        t ≤ (7016246261 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_29 V_30
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_30 :
    ∀ t,
      (7016246261 / 2000000000000 : ℝ) ≤ t →
        t ≤ (1953374043 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_left (by norm_num) (by norm_num [aρ_1]) U_30 V_31
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_31 :
    ∀ t,
      (1953374043 / 500000000000 : ℝ) ≤ t →
        t ≤ (59205077 / 10000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2 h0
  have eq1 : qm = (59205077 / 10000000000 : ℝ) := by norm_num [qm]
  exact
    check_mid_left Umid_le V_32 (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) t
      (by rw [aρ_1]; exact h1) (by rw [eq1]; exact h2) h0

lemma tc_32 :
    ∀ t,
      (59205077 / 10000000000 : ℝ) ≤ t →
        t ≤ (59205079 / 10000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2 h0
  have eq1 : qm = (59205077 / 10000000000 : ℝ) := by norm_num [qm]
  have eq2 : qp = (59205079 / 10000000000 : ℝ) := by norm_num [qp]
  exact
    check_mid Umid_le V_br (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) t
      (by rw [eq1]; exact h1) (by rw [eq2]; exact h2) h0

lemma tc_33 :
    ∀ t,
      (59205079 / 10000000000 : ℝ) ≤ t →
        t ≤ (8992695531 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2 h0
  have eq2 : qp = (59205079 / 10000000000 : ℝ) := by norm_num [qp]
  exact
    check_mid_right Umid_le V_33 (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20]) t
      (by rw [eq2]; exact h1) (by rw [bρ_1]; exact h2) h0

lemma tc_34 :
    ∀ t,
      (8992695531 / 1000000000000 : ℝ) ≤ t →
        t ≤ (19572466643 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_35 V_34
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_35 :
    ∀ t,
      (19572466643 / 2000000000000 : ℝ) ≤ t →
        t ≤ (40732008867 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_36 V_35
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_36 :
    ∀ t,
      (40732008867 / 4000000000000 : ℝ) ≤ t →
        t ≤ (1322471389 / 125000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_37 V_36
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_37 :
    ∀ t,
      (1322471389 / 125000000000 : ℝ) ≤ t →
        t ≤ (4549323561 / 400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_38 V_37
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_38 :
    ∀ t,
      (4549323561 / 400000000000 : ℝ) ≤ t →
        t ≤ (12166846693 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_39 V_38
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_39 :
    ∀ t,
      (12166846693 / 1000000000000 : ℝ) ≤ t →
        t ≤ (3068199571 / 200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_40 V_39
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_40 :
    ∀ t,
      (3068199571 / 200000000000 : ℝ) ≤ t →
        t ≤ (255845148549 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_41 V_40
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_41 :
    ∀ t,
      (255845148549 / 16000000000000 : ℝ) ≤ t →
        t ≤ (133117165709 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_42 V_41
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_42 :
    ∀ t,
      (133117165709 / 8000000000000 : ℝ) ≤ t →
        t ≤ (108571569141 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_43 V_42
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_43 :
    ∀ t,
      (108571569141 / 6400000000000 : ℝ) ≤ t →
        t ≤ (276623514287 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_44 V_43
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_44 :
    ∀ t,
      (276623514287 / 16000000000000 : ℝ) ≤ t →
        t ≤ (563636211443 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_45 V_44
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_45 :
    ∀ t,
      (563636211443 / 32000000000000 : ℝ) ≤ t →
        t ≤ (71753174289 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_46 V_45
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_46 :
    ∀ t,
      (71753174289 / 4000000000000 : ℝ) ≤ t →
        t ≤ (584414577181 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_47 V_46
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_47 :
    ∀ t,
      (584414577181 / 32000000000000 : ℝ) ≤ t →
        t ≤ (11896075201 / 640000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_48 V_47
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_48 :
    ∀ t,
      (11896075201 / 640000000000 : ℝ) ≤ t →
        t ≤ (605192942919 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_49 V_48
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_49 :
    ∀ t,
      (605192942919 / 32000000000000 : ℝ) ≤ t →
        t ≤ (153895531447 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_50 V_49
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_50 :
    ∀ t,
      (153895531447 / 8000000000000 : ℝ) ≤ t →
        t ≤ (318180245763 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_51 V_50
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_51 :
    ∀ t,
      (318180245763 / 16000000000000 : ℝ) ≤ t →
        t ≤ (41071178579 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_52 V_51
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_52 :
    ∀ t,
      (41071178579 / 2000000000000 : ℝ) ≤ t →
        t ≤ (34934779437 / 1600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_53 V_52
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_53 :
    ∀ t,
      (34934779437 / 1600000000000 : ℝ) ≤ t →
        t ≤ (92531540027 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_54 V_53
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_54 :
    ∀ t,
      (92531540027 / 4000000000000 : ℝ) ≤ t →
        t ≤ (6432545181 / 250000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_55 V_54
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_55 :
    ∀ t,
      (6432545181 / 250000000000 : ℝ) ≤ t →
        t ≤ (213931144553 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_56 V_55
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_56 :
    ∀ t,
      (213931144553 / 8000000000000 : ℝ) ≤ t →
        t ≤ (435951987867 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_57 V_56
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_57 :
    ∀ t,
      (435951987867 / 16000000000000 : ℝ) ≤ t →
        t ≤ (111010421657 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_58 V_57
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_58 :
    ∀ t,
      (111010421657 / 4000000000000 : ℝ) ≤ t →
        t ≤ (452131385389 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_59 V_58
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_59 :
    ∀ t,
      (452131385389 / 16000000000000 : ℝ) ≤ t →
        t ≤ (912352469539 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_60 V_59
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_60 :
    ∀ t,
      (912352469539 / 32000000000000 : ℝ) ≤ t →
        t ≤ (9204421683 / 320000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_61 V_60
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_61 :
    ∀ t,
      (9204421683 / 320000000000 : ℝ) ≤ t →
        t ≤ (928531867061 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_62 V_61
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_62 :
    ∀ t,
      (928531867061 / 32000000000000 : ℝ) ≤ t →
        t ≤ (468310782911 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_63 V_62
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_63 :
    ∀ t,
      (468310782911 / 16000000000000 : ℝ) ≤ t →
        t ≤ (944711264583 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_64 V_63
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_64 :
    ∀ t,
      (944711264583 / 32000000000000 : ℝ) ≤ t →
        t ≤ (59550060209 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_65 V_64
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_65 :
    ∀ t,
      (59550060209 / 2000000000000 : ℝ) ≤ t →
        t ≤ (192178132421 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_66 V_65
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_66 :
    ∀ t,
      (192178132421 / 6400000000000 : ℝ) ≤ t →
        t ≤ (484490180433 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_67 V_66
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_67 :
    ∀ t,
      (484490180433 / 16000000000000 : ℝ) ≤ t →
        t ≤ (977070059627 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_68 V_67
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_68 :
    ∀ t,
      (977070059627 / 32000000000000 : ℝ) ≤ t →
        t ≤ (246289939597 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_69 V_68
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_69 :
    ∀ t,
      (246289939597 / 8000000000000 : ℝ) ≤ t →
        t ≤ (100133915591 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_70 V_69
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_70 :
    ∀ t,
      (100133915591 / 3200000000000 : ℝ) ≤ t →
        t ≤ (127189819179 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_71 V_70
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_71 :
    ∀ t,
      (127189819179 / 4000000000000 : ℝ) ≤ t →
        t ≤ (516848975477 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_72 V_71
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_72 :
    ∀ t,
      (516848975477 / 16000000000000 : ℝ) ≤ t →
        t ≤ (262469337119 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_73 V_72
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_73 :
    ∀ t,
      (262469337119 / 8000000000000 : ℝ) ≤ t →
        t ≤ (6763975897 / 200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_74 V_73
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_74 :
    ∀ t,
      (6763975897 / 200000000000 : ℝ) ≤ t →
        t ≤ (278648734641 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_75 V_74
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_75 :
    ∀ t,
      (278648734641 / 8000000000000 : ℝ) ≤ t →
        t ≤ (143369216701 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_76 V_75
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_76 :
    ∀ t,
      (143369216701 / 4000000000000 : ℝ) ≤ t →
        t ≤ (75729457731 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_77 V_76
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_77 :
    ∀ t,
      (75729457731 / 2000000000000 : ℝ) ≤ t →
        t ≤ (20954789123 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_78 V_77
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_78 :
    ∀ t,
      (20954789123 / 500000000000 : ℝ) ≤ t →
        t ≤ (694494763253 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_79 V_78
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_79 :
    ∀ t,
      (694494763253 / 16000000000000 : ℝ) ≤ t →
        t ≤ (1412931037823 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_80 V_79
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_80 :
    ∀ t,
      (1412931037823 / 32000000000000 : ℝ) ≤ t →
        t ≤ (71843627457 / 1600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_81 V_80
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_81 :
    ∀ t,
      (71843627457 / 1600000000000 : ℝ) ≤ t →
        t ≤ (2897686609597 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_82 V_81
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_82 :
    ∀ t,
      (2897686609597 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1460814060457 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_83 V_82
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_83 :
    ∀ t,
      (1460814060457 / 32000000000000 : ℝ) ≤ t →
        t ≤ (2945569632231 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_84 V_83
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_84 :
    ∀ t,
      (2945569632231 / 64000000000000 : ℝ) ≤ t →
        t ≤ (742377785887 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_85 V_84
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_85 :
    ∀ t,
      (742377785887 / 16000000000000 : ℝ) ≤ t →
        t ≤ (598690530973 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_86 V_85
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_86 :
    ∀ t,
      (598690530973 / 12800000000000 : ℝ) ≤ t →
        t ≤ (1508697083091 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_87 V_86
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_87 :
    ∀ t,
      (1508697083091 / 32000000000000 : ℝ) ≤ t →
        t ≤ (3041335677499 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_88 V_87
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_88 :
    ∀ t,
      (3041335677499 / 64000000000000 : ℝ) ≤ t →
        t ≤ (191579824301 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_89 V_88
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_89 :
    ∀ t,
      (191579824301 / 4000000000000 : ℝ) ≤ t →
        t ≤ (3089218700133 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_90 V_89
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_90 :
    ∀ t,
      (3089218700133 / 64000000000000 : ℝ) ≤ t →
        t ≤ (62263204229 / 1280000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_91 V_90
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_91 :
    ∀ t,
      (62263204229 / 1280000000000 : ℝ) ≤ t →
        t ≤ (3137101722767 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_92 V_91
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_92 :
    ∀ t,
      (3137101722767 / 64000000000000 : ℝ) ≤ t →
        t ≤ (790260808521 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_93 V_92
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_93 :
    ∀ t,
      (790260808521 / 16000000000000 : ℝ) ≤ t →
        t ≤ (3184984745401 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_94 V_93
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_94 :
    ∀ t,
      (3184984745401 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1604463128359 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_95 V_94
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_95 :
    ∀ t,
      (1604463128359 / 32000000000000 : ℝ) ≤ t →
        t ≤ (646573553607 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_96 V_95
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_96 :
    ∀ t,
      (646573553607 / 12800000000000 : ℝ) ≤ t →
        t ≤ (407101159919 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_97 V_96
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_97 :
    ∀ t,
      (407101159919 / 8000000000000 : ℝ) ≤ t →
        t ≤ (1652346150993 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_98 V_97
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_98 :
    ∀ t,
      (1652346150993 / 32000000000000 : ℝ) ≤ t →
        t ≤ (167628766231 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_99 V_98
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_99 :
    ∀ t,
      (167628766231 / 3200000000000 : ℝ) ≤ t →
        t ≤ (1700229173627 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_100 V_99
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_100 :
    ∀ t,
      (1700229173627 / 32000000000000 : ℝ) ≤ t →
        t ≤ (107760667809 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_101 V_100
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_101 :
    ∀ t,
      (107760667809 / 2000000000000 : ℝ) ≤ t →
        t ≤ (886026853789 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_102 V_101
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_102 :
    ∀ t,
      (886026853789 / 16000000000000 : ℝ) ≤ t →
        t ≤ (454984182553 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_103 V_102
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_103 :
    ∀ t,
      (454984182553 / 8000000000000 : ℝ) ≤ t →
        t ≤ (47892569387 / 800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_104 V_103
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_104 :
    ∀ t,
      (47892569387 / 800000000000 : ℝ) ≤ t →
        t ≤ (502867205187 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_105 V_104
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_105 :
    ∀ t,
      (502867205187 / 8000000000000 : ℝ) ≤ t →
        t ≤ (65851089563 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_106 V_105
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_106 :
    ∀ t,
      (65851089563 / 1000000000000 : ℝ) ≤ t →
        t ≤ (2140864814337 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_107 V_106
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_107 :
    ∀ t,
      (2140864814337 / 32000000000000 : ℝ) ≤ t →
        t ≤ (1087247381329 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_108 V_107
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_108 :
    ∀ t,
      (1087247381329 / 16000000000000 : ℝ) ≤ t →
        t ≤ (2208124710979 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_109 V_108
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_109 :
    ∀ t,
      (2208124710979 / 32000000000000 : ℝ) ≤ t →
        t ≤ (4449879370279 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_110 V_109
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_110 :
    ∀ t,
      (4449879370279 / 64000000000000 : ℝ) ≤ t →
        t ≤ (22417546593 / 320000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_111 V_110
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_111 :
    ∀ t,
      (22417546593 / 320000000000 : ℝ) ≤ t →
        t ≤ (4517139266921 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_112 V_111
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_112 :
    ∀ t,
      (4517139266921 / 64000000000000 : ℝ) ≤ t →
        t ≤ (2275384607621 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_113 V_112
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_113 :
    ∀ t,
      (2275384607621 / 32000000000000 : ℝ) ≤ t →
        t ≤ (4584399163563 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_114 V_113
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_114 :
    ∀ t,
      (4584399163563 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1154507277971 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_115 V_114
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_115 :
    ∀ t,
      (1154507277971 / 16000000000000 : ℝ) ≤ t →
        t ≤ (930331812041 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_116 V_115
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_116 :
    ∀ t,
      (930331812041 / 12800000000000 : ℝ) ≤ t →
        t ≤ (2342644504263 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_117 V_116
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_117 :
    ∀ t,
      (2342644504263 / 32000000000000 : ℝ) ≤ t →
        t ≤ (9404207965373 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_118 V_117
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_118 :
    ∀ t,
      (9404207965373 / 128000000000000 : ℝ) ≤ t →
        t ≤ (4718918956847 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_119 V_118
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_119 :
    ∀ t,
      (4718918956847 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1894293572403 / 25600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_120 V_119
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_120 :
    ∀ t,
      (1894293572403 / 25600000000000 : ℝ) ≤ t →
        t ≤ (297034306573 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_121 V_120
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_121 :
    ∀ t,
      (297034306573 / 4000000000000 : ℝ) ≤ t →
        t ≤ (9538727758657 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_122 V_121
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_122 :
    ∀ t,
      (9538727758657 / 128000000000000 : ℝ) ≤ t →
        t ≤ (4786178853489 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_123 V_122
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_123 :
    ∀ t,
      (4786178853489 / 64000000000000 : ℝ) ≤ t →
        t ≤ (9605987655299 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_124 V_123
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_124 :
    ∀ t,
      (9605987655299 / 128000000000000 : ℝ) ≤ t →
        t ≤ (481980880181 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_125 V_124
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_125 :
    ∀ t,
      (481980880181 / 6400000000000 : ℝ) ≤ t →
        t ≤ (9673247551941 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_126 V_125
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_126 :
    ∀ t,
      (9673247551941 / 128000000000000 : ℝ) ≤ t →
        t ≤ (4853438750131 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_127 V_126
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_127 :
    ∀ t,
      (4853438750131 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1221767174613 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_128 V_127
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_128 :
    ∀ t,
      (1221767174613 / 16000000000000 : ℝ) ≤ t →
        t ≤ (4920698646773 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_129 V_128
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_129 :
    ∀ t,
      (4920698646773 / 64000000000000 : ℝ) ≤ t →
        t ≤ (2477164297547 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_130 V_129
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_130 :
    ∀ t,
      (2477164297547 / 32000000000000 : ℝ) ≤ t →
        t ≤ (997591708683 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_131 V_130
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_131 :
    ∀ t,
      (997591708683 / 12800000000000 : ℝ) ≤ t →
        t ≤ (627698561467 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_132 V_131
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_132 :
    ∀ t,
      (627698561467 / 8000000000000 : ℝ) ≤ t →
        t ≤ (5055218440057 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_133 V_132
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_133 :
    ∀ t,
      (5055218440057 / 64000000000000 : ℝ) ≤ t →
        t ≤ (2544424194189 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_134 V_133
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_134 :
    ∀ t,
      (2544424194189 / 32000000000000 : ℝ) ≤ t →
        t ≤ (5122478336699 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_135 V_134
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_135 :
    ∀ t,
      (5122478336699 / 64000000000000 : ℝ) ≤ t →
        t ≤ (257805414251 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_136 V_135
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_136 :
    ∀ t,
      (257805414251 / 3200000000000 : ℝ) ≤ t →
        t ≤ (2611684090831 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_137 V_136
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_137 :
    ∀ t,
      (2611684090831 / 32000000000000 : ℝ) ≤ t →
        t ≤ (165332127447 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_138 V_137
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_138 :
    ∀ t,
      (165332127447 / 2000000000000 : ℝ) ≤ t →
        t ≤ (2678943987473 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_139 V_138
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_139 :
    ∀ t,
      (2678943987473 / 32000000000000 : ℝ) ≤ t →
        t ≤ (1356286967897 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_140 V_139
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_140 :
    ∀ t,
      (1356286967897 / 16000000000000 : ℝ) ≤ t →
        t ≤ (694958458109 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_141 V_140
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_141 :
    ∀ t,
      (694958458109 / 8000000000000 : ℝ) ≤ t →
        t ≤ (1423546864539 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_142 V_141
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_142 :
    ∀ t,
      (1423546864539 / 16000000000000 : ℝ) ≤ t →
        t ≤ (72858840643 / 800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_143 V_142
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_143 :
    ∀ t,
      (72858840643 / 800000000000 : ℝ) ≤ t →
        t ≤ (762218354751 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_144 V_143
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_144 :
    ∀ t,
      (762218354751 / 8000000000000 : ℝ) ≤ t →
        t ≤ (24870259471 / 250000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_145 V_144
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_145 :
    ∀ t,
      (24870259471 / 250000000000 : ℝ) ≤ t →
        t ≤ (1614118950931 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_146 V_145
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_146 :
    ∀ t,
      (1614118950931 / 16000000000000 : ℝ) ≤ t →
        t ≤ (818270647859 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_147 V_146
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_147 :
    ∀ t,
      (818270647859 / 8000000000000 : ℝ) ≤ t →
        t ≤ (331792728101 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_148 V_147
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_148 :
    ∀ t,
      (331792728101 / 3200000000000 : ℝ) ≤ t →
        t ≤ (3340349625797 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_149 V_148
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_149 :
    ∀ t,
      (3340349625797 / 32000000000000 : ℝ) ≤ t →
        t ≤ (420346496323 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_150 V_149
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_150 :
    ∀ t,
      (420346496323 / 4000000000000 : ℝ) ≤ t →
        t ≤ (3385194315371 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_151 V_150
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_151 :
    ∀ t,
      (3385194315371 / 32000000000000 : ℝ) ≤ t →
        t ≤ (1703808330079 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_152 V_151
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_152 :
    ∀ t,
      (1703808330079 / 16000000000000 : ℝ) ≤ t →
        t ≤ (686007800989 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_153 V_152
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_153 :
    ∀ t,
      (686007800989 / 6400000000000 : ℝ) ≤ t →
        t ≤ (863115337433 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_154 V_153
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_154 :
    ∀ t,
      (863115337433 / 8000000000000 : ℝ) ≤ t →
        t ≤ (6927345044251 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_155 V_154
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_155 :
    ∀ t,
      (6927345044251 / 64000000000000 : ℝ) ≤ t →
        t ≤ (3474883694519 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_156 V_155
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_156 :
    ∀ t,
      (3474883694519 / 32000000000000 : ℝ) ≤ t →
        t ≤ (278887589353 / 2560000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_157 V_156
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_157 :
    ∀ t,
      (278887589353 / 2560000000000 : ℝ) ≤ t →
        t ≤ (1748653019653 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_158 V_157
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_158 :
    ∀ t,
      (1748653019653 / 16000000000000 : ℝ) ≤ t →
        t ≤ (7017034423399 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_159 V_158
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_159 :
    ∀ t,
      (7017034423399 / 64000000000000 : ℝ) ≤ t →
        t ≤ (3519728384093 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_160 V_159
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_160 :
    ∀ t,
      (3519728384093 / 32000000000000 : ℝ) ≤ t →
        t ≤ (7061879112973 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_161 V_160
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_161 :
    ∀ t,
      (7061879112973 / 64000000000000 : ℝ) ≤ t →
        t ≤ (44276884111 / 400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_162 V_161
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_162 :
    ∀ t,
      (44276884111 / 400000000000 : ℝ) ≤ t →
        t ≤ (7106723802547 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_163 V_162
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_163 :
    ∀ t,
      (7106723802547 / 64000000000000 : ℝ) ≤ t →
        t ≤ (3564573073667 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_164 V_163
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_164 :
    ∀ t,
      (3564573073667 / 32000000000000 : ℝ) ≤ t →
        t ≤ (7151568492121 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_165 V_164
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_165 :
    ∀ t,
      (7151568492121 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1793497709227 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_166 V_165
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_166 :
    ∀ t,
      (1793497709227 / 16000000000000 : ℝ) ≤ t →
        t ≤ (1439282636339 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_167 V_166
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_167 :
    ∀ t,
      (1439282636339 / 12800000000000 : ℝ) ≤ t →
        t ≤ (3609417763241 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_168 V_167
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_168 :
    ∀ t,
      (3609417763241 / 32000000000000 : ℝ) ≤ t →
        t ≤ (7241257871269 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_169 V_168
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_169 :
    ∀ t,
      (7241257871269 / 64000000000000 : ℝ) ≤ t →
        t ≤ (907960027007 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_170 V_169
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_170 :
    ∀ t,
      (907960027007 / 8000000000000 : ℝ) ≤ t →
        t ≤ (7286102560843 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_171 V_170
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

end Zeta5Irrational
