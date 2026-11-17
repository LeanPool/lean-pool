/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Real.Pi.Bounds
import LeanPool.Zeta5Irrational.Table.U28
import LeanPool.Zeta5Irrational.Table.U29
import LeanPool.Zeta5Irrational.Table.U30
import LeanPool.Zeta5Irrational.Table.U31
import LeanPool.Zeta5Irrational.Table.U32
import LeanPool.Zeta5Irrational.Table.U33
import LeanPool.Zeta5Irrational.Table.U34
import LeanPool.Zeta5Irrational.Table.U35
import LeanPool.Zeta5Irrational.Table.U36
import LeanPool.Zeta5Irrational.Table.U37
import LeanPool.Zeta5Irrational.Table.U38
import LeanPool.Zeta5Irrational.Table.U39
import LeanPool.Zeta5Irrational.Table.U40
import LeanPool.Zeta5Irrational.Table.U41
import LeanPool.Zeta5Irrational.Table.U42
import LeanPool.Zeta5Irrational.Table.V28
import LeanPool.Zeta5Irrational.Table.V29
import LeanPool.Zeta5Irrational.Table.V30
import LeanPool.Zeta5Irrational.Table.V31
import LeanPool.Zeta5Irrational.Table.V32
import LeanPool.Zeta5Irrational.Table.V33
import LeanPool.Zeta5Irrational.Table.V34
import LeanPool.Zeta5Irrational.Table.V35
import LeanPool.Zeta5Irrational.Table.V36
import LeanPool.Zeta5Irrational.Table.V37
import LeanPool.Zeta5Irrational.Table.V38
import LeanPool.Zeta5Irrational.Table.V39
import LeanPool.Zeta5Irrational.Table.V40
import LeanPool.Zeta5Irrational.Table.V41
import LeanPool.Zeta5Irrational.Table.V42

/-! # Interval certificates 342 through 512

These independent endpoint checks use only the corresponding upper and lower table bounds.
The covering argument is assembled in `LeanPool.Zeta5Irrational.Table.Intervals`.
-/

@[expose] public section

open Finset

namespace Zeta5Irrational

lemma tc_342 :
    ∀ t,
      (2543485761489 / 8000000000000 : ℝ) ≤ t →
        t ≤ (10251686603209 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_343 V_342
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_343 :
    ∀ t,
      (10251686603209 / 32000000000000 : ℝ) ≤ t →
        t ≤ (5164715080231 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_344 V_343
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_344 :
    ∀ t,
      (5164715080231 / 16000000000000 : ℝ) ≤ t →
        t ≤ (1310614659371 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_345 V_344
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_345 :
    ∀ t,
      (1310614659371 / 4000000000000 : ℝ) ≤ t →
        t ≤ (5320202194737 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_346 V_345
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_346 :
    ∀ t,
      (5320202194737 / 16000000000000 : ℝ) ≤ t →
        t ≤ (539794575199 / 1600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_347 V_346
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_347 :
    ∀ t,
      (539794575199 / 1600000000000 : ℝ) ≤ t →
        t ≤ (5475689309243 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_348 V_347
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_348 :
    ∀ t,
      (5475689309243 / 16000000000000 : ℝ) ≤ t →
        t ≤ (86772388539 / 250000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_349 V_348
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_349 :
    ∀ t,
      (86772388539 / 250000000000 : ℝ) ≤ t →
        t ≤ (11190582883251 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_350 V_349
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_350 :
    ∀ t,
      (11190582883251 / 32000000000000 : ℝ) ≤ t →
        t ≤ (1127430003351 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_351 V_350
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_351 :
    ∀ t,
      (1127430003351 / 3200000000000 : ℝ) ≤ t →
        t ≤ (11358017183769 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_352 V_351
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_352 :
    ∀ t,
      (11358017183769 / 32000000000000 : ℝ) ≤ t →
        t ≤ (22799751517797 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_353 V_352
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_353 :
    ∀ t,
      (22799751517797 / 64000000000000 : ℝ) ≤ t →
        t ≤ (2860433583507 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_354 V_353
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_354 :
    ∀ t,
      (2860433583507 / 8000000000000 : ℝ) ≤ t →
        t ≤ (4593437163663 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_355 V_354
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_355 :
    ∀ t,
      (4593437163663 / 12800000000000 : ℝ) ≤ t →
        t ≤ (11525451484287 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_356 V_355
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_356 :
    ∀ t,
      (11525451484287 / 32000000000000 : ℝ) ≤ t →
        t ≤ (23134620118833 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_357 V_356
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_357 :
    ∀ t,
      (23134620118833 / 64000000000000 : ℝ) ≤ t →
        t ≤ (5804584317273 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_358 V_357
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_358 :
    ∀ t,
      (5804584317273 / 16000000000000 : ℝ) ≤ t →
        t ≤ (46520391688443 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_359 V_358
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_359 :
    ∀ t,
      (46520391688443 / 128000000000000 : ℝ) ≤ t →
        t ≤ (23302054419351 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_360 V_359
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_360 :
    ∀ t,
      (23302054419351 / 64000000000000 : ℝ) ≤ t →
        t ≤ (46687825988961 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_361 V_360
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_361 :
    ∀ t,
      (46687825988961 / 128000000000000 : ℝ) ≤ t →
        t ≤ (2338577156961 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_362 V_361
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_362 :
    ∀ t,
      (2338577156961 / 6400000000000 : ℝ) ≤ t →
        t ≤ (46855260289479 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_363 V_362
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_363 :
    ∀ t,
      (46855260289479 / 128000000000000 : ℝ) ≤ t →
        t ≤ (23469488719869 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_364 V_363
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_364 :
    ∀ t,
      (23469488719869 / 64000000000000 : ℝ) ≤ t →
        t ≤ (47022694589997 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_365 V_364
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_365 :
    ∀ t,
      (47022694589997 / 128000000000000 : ℝ) ≤ t →
        t ≤ (1472075366883 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_366 V_365
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_366 :
    ∀ t,
      (1472075366883 / 4000000000000 : ℝ) ≤ t →
        t ≤ (9438025778103 / 25600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_367 V_366
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_367 :
    ∀ t,
      (9438025778103 / 25600000000000 : ℝ) ≤ t →
        t ≤ (23636923020387 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_368 V_367
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_368 :
    ∀ t,
      (23636923020387 / 64000000000000 : ℝ) ≤ t →
        t ≤ (47357563191033 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_369 V_368
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_369 :
    ∀ t,
      (47357563191033 / 128000000000000 : ℝ) ≤ t →
        t ≤ (11860320085323 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_370 V_369
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_370 :
    ∀ t,
      (11860320085323 / 32000000000000 : ℝ) ≤ t →
        t ≤ (47524997491551 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_371 V_370
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_371 :
    ∀ t,
      (47524997491551 / 128000000000000 : ℝ) ≤ t →
        t ≤ (4760871464181 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_372 V_371
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_372 :
    ∀ t,
      (4760871464181 / 12800000000000 : ℝ) ≤ t →
        t ≤ (47692431792069 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_373 V_372
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_373 :
    ∀ t,
      (47692431792069 / 128000000000000 : ℝ) ≤ t →
        t ≤ (5972018617791 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_374 V_373
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_374 :
    ∀ t,
      (5972018617791 / 16000000000000 : ℝ) ≤ t →
        t ≤ (47859866092587 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_375 V_374
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_375 :
    ∀ t,
      (47859866092587 / 128000000000000 : ℝ) ≤ t →
        t ≤ (23971791621423 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_376 V_375
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_376 :
    ∀ t,
      (23971791621423 / 64000000000000 : ℝ) ≤ t →
        t ≤ (9605460078621 / 25600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_377 V_376
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_377 :
    ∀ t,
      (9605460078621 / 25600000000000 : ℝ) ≤ t →
        t ≤ (12027754385841 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_378 V_377
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_378 :
    ∀ t,
      (12027754385841 / 32000000000000 : ℝ) ≤ t →
        t ≤ (48194734693623 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_379 V_378
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_379 :
    ∀ t,
      (48194734693623 / 128000000000000 : ℝ) ≤ t →
        t ≤ (24139225921941 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_380 V_379
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_380 :
    ∀ t,
      (24139225921941 / 64000000000000 : ℝ) ≤ t →
        t ≤ (48362168994141 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_381 V_380
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_381 :
    ∀ t,
      (48362168994141 / 128000000000000 : ℝ) ≤ t →
        t ≤ (121114715361 / 320000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_382 V_381
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_382 :
    ∀ t,
      (121114715361 / 320000000000 : ℝ) ≤ t →
        t ≤ (48529603294659 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_383 V_382
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_383 :
    ∀ t,
      (48529603294659 / 128000000000000 : ℝ) ≤ t →
        t ≤ (24306660222459 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_384 V_383
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_384 :
    ∀ t,
      (24306660222459 / 64000000000000 : ℝ) ≤ t →
        t ≤ (48697037595177 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_385 V_384
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_385 :
    ∀ t,
      (48697037595177 / 128000000000000 : ℝ) ≤ t →
        t ≤ (12195188686359 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_386 V_385
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_386 :
    ∀ t,
      (12195188686359 / 32000000000000 : ℝ) ≤ t →
        t ≤ (9772894379139 / 25600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_387 V_386
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_387 :
    ∀ t,
      (9772894379139 / 25600000000000 : ℝ) ≤ t →
        t ≤ (24474094522977 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_388 V_387
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_388 :
    ∀ t,
      (24474094522977 / 64000000000000 : ℝ) ≤ t →
        t ≤ (6139452918309 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_389 V_388
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_389 :
    ∀ t,
      (6139452918309 / 16000000000000 : ℝ) ≤ t →
        t ≤ (4928305764699 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_390 V_389
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_390 :
    ∀ t,
      (4928305764699 / 12800000000000 : ℝ) ≤ t →
        t ≤ (12362622986877 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_391 V_390
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_391 :
    ∀ t,
      (12362622986877 / 32000000000000 : ℝ) ≤ t →
        t ≤ (24808963124013 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_392 V_391
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_392 :
    ∀ t,
      (24808963124013 / 64000000000000 : ℝ) ≤ t →
        t ≤ (777896258571 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_393 V_392
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_393 :
    ∀ t,
      (777896258571 / 2000000000000 : ℝ) ≤ t →
        t ≤ (24976397424531 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_394 V_393
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_394 :
    ∀ t,
      (24976397424531 / 64000000000000 : ℝ) ≤ t →
        t ≤ (2506011457479 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_395 V_394
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_395 :
    ∀ t,
      (2506011457479 / 6400000000000 : ℝ) ≤ t →
        t ≤ (25143831725049 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_396 V_395
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_396 :
    ∀ t,
      (25143831725049 / 64000000000000 : ℝ) ≤ t →
        t ≤ (6306887218827 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_397 V_396
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_397 :
    ∀ t,
      (6306887218827 / 16000000000000 : ℝ) ≤ t →
        t ≤ (12697491587913 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_398 V_397
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_398 :
    ∀ t,
      (12697491587913 / 32000000000000 : ℝ) ≤ t →
        t ≤ (3195302184543 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_399 V_398
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_399 :
    ∀ t,
      (3195302184543 / 8000000000000 : ℝ) ≤ t →
        t ≤ (12864925888431 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_400 V_399
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_400 :
    ∀ t,
      (12864925888431 / 32000000000000 : ℝ) ≤ t →
        t ≤ (1294864303869 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_401 V_400
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_401 :
    ∀ t,
      (1294864303869 / 3200000000000 : ℝ) ≤ t →
        t ≤ (13032360188949 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_402 V_401
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_402 :
    ∀ t,
      (13032360188949 / 32000000000000 : ℝ) ≤ t →
        t ≤ (1639509667401 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_403 V_402
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_403 :
    ∀ t,
      (1639509667401 / 4000000000000 : ℝ) ≤ t →
        t ≤ (6641755819863 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_404 V_403
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_404 :
    ∀ t,
      (6641755819863 / 16000000000000 : ℝ) ≤ t →
        t ≤ (3362736485061 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_405 V_404
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_405 :
    ∀ t,
      (3362736485061 / 8000000000000 : ℝ) ≤ t →
        t ≤ (6809190120381 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_406 V_405
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_406 :
    ∀ t,
      (6809190120381 / 16000000000000 : ℝ) ≤ t →
        t ≤ (86161340883 / 200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_407 V_406
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_407 :
    ∀ t,
      (86161340883 / 200000000000 : ℝ) ≤ t →
        t ≤ (54181913021 / 125000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_408 V_407
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_408 :
    ∀ t,
      (54181913021 / 125000000000 : ℝ) ≤ t →
        t ≤ (436103903921 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_409 V_408
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_409 :
    ∀ t,
      (436103903921 / 1000000000000 : ℝ) ≤ t →
        t ≤ (219376251837 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_410 V_409
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_410 :
    ∀ t,
      (219376251837 / 500000000000 : ℝ) ≤ t →
        t ≤ (880153607101 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_411 V_410
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_411 :
    ∀ t,
      (880153607101 / 2000000000000 : ℝ) ≤ t →
        t ≤ (441401103427 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_412 V_411
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_412 :
    ∀ t,
      (441401103427 / 1000000000000 : ℝ) ≤ t →
        t ≤ (885450806607 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_413 V_412
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_413 :
    ∀ t,
      (885450806607 / 2000000000000 : ℝ) ≤ t →
        t ≤ (22202485159 / 50000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_414 V_413
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_414 :
    ∀ t,
      (22202485159 / 50000000000 : ℝ) ≤ t →
        t ≤ (890748006113 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_415 V_414
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_415 :
    ∀ t,
      (890748006113 / 2000000000000 : ℝ) ≤ t →
        t ≤ (446698302933 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_416 V_415
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_416 :
    ∀ t,
      (446698302933 / 1000000000000 : ℝ) ≤ t →
        t ≤ (896045205619 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_417 V_416
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_417 :
    ∀ t,
      (896045205619 / 2000000000000 : ℝ) ≤ t →
        t ≤ (1794739010991 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_418 V_417
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_418 :
    ∀ t,
      (1794739010991 / 4000000000000 : ℝ) ≤ t →
        t ≤ (224673451343 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_419 V_418
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_419 :
    ∀ t,
      (224673451343 / 500000000000 : ℝ) ≤ t →
        t ≤ (1800036210497 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_420 V_419
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_420 :
    ∀ t,
      (1800036210497 / 4000000000000 : ℝ) ≤ t →
        t ≤ (7210739241 / 16000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_421 V_420
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_421 :
    ∀ t,
      (7210739241 / 16000000000 : ℝ) ≤ t →
        t ≤ (1805333410003 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_422 V_421
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_422 :
    ∀ t,
      (1805333410003 / 4000000000000 : ℝ) ≤ t →
        t ≤ (451995502439 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_423 V_422
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_423 :
    ∀ t,
      (451995502439 / 1000000000000 : ℝ) ≤ t →
        t ≤ (1810630609509 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_424 V_423
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_424 :
    ∀ t,
      (1810630609509 / 4000000000000 : ℝ) ≤ t →
        t ≤ (906639604631 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_425 V_424
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_425 :
    ∀ t,
      (906639604631 / 2000000000000 : ℝ) ≤ t →
        t ≤ (363185561803 / 800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_426 V_425
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_426 :
    ∀ t,
      (363185561803 / 800000000000 : ℝ) ≤ t →
        t ≤ (28415256387 / 62500000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_427 V_426
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_427 :
    ∀ t,
      (28415256387 / 62500000000 : ℝ) ≤ t →
        t ≤ (1821225008521 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_428 V_427
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_428 :
    ∀ t,
      (1821225008521 / 4000000000000 : ℝ) ≤ t →
        t ≤ (911936804137 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_429 V_428
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_429 :
    ∀ t,
      (911936804137 / 2000000000000 : ℝ) ≤ t →
        t ≤ (1826522208027 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_430 V_429
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_430 :
    ∀ t,
      (1826522208027 / 4000000000000 : ℝ) ≤ t →
        t ≤ (91458540389 / 200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_431 V_430
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_431 :
    ∀ t,
      (91458540389 / 200000000000 : ℝ) ≤ t →
        t ≤ (1831819407533 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_432 V_431
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_432 :
    ∀ t,
      (1831819407533 / 4000000000000 : ℝ) ≤ t →
        t ≤ (917234003643 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_433 V_432
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_433 :
    ∀ t,
      (917234003643 / 2000000000000 : ℝ) ≤ t →
        t ≤ (1837116607039 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_434 V_433
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_434 :
    ∀ t,
      (1837116607039 / 4000000000000 : ℝ) ≤ t →
        t ≤ (229970650849 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_435 V_434
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_435 :
    ∀ t,
      (229970650849 / 500000000000 : ℝ) ≤ t →
        t ≤ (368482761309 / 800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_436 V_435
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_436 :
    ∀ t,
      (368482761309 / 800000000000 : ℝ) ≤ t →
        t ≤ (922531203149 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_437 V_436
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_437 :
    ∀ t,
      (922531203149 / 2000000000000 : ℝ) ≤ t →
        t ≤ (1847711006051 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_438 V_437
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_438 :
    ∀ t,
      (1847711006051 / 4000000000000 : ℝ) ≤ t →
        t ≤ (462589901451 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_439 V_438
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_439 :
    ∀ t,
      (462589901451 / 1000000000000 : ℝ) ≤ t →
        t ≤ (1853008205557 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_440 V_439
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_440 :
    ∀ t,
      (1853008205557 / 4000000000000 : ℝ) ≤ t →
        t ≤ (185565680531 / 400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_441 V_440
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_441 :
    ∀ t,
      (185565680531 / 400000000000 : ℝ) ≤ t →
        t ≤ (1858305405063 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_442 V_441
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_442 :
    ∀ t,
      (1858305405063 / 4000000000000 : ℝ) ≤ t →
        t ≤ (116309625301 / 250000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_443 V_442
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_443 :
    ∀ t,
      (116309625301 / 250000000000 : ℝ) ≤ t →
        t ≤ (1863602604569 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_444 V_443
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_444 :
    ∀ t,
      (1863602604569 / 4000000000000 : ℝ) ≤ t →
        t ≤ (933125602161 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_445 V_444
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_445 :
    ∀ t,
      (933125602161 / 2000000000000 : ℝ) ≤ t →
        t ≤ (467887100957 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_446 V_445
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_446 :
    ∀ t,
      (467887100957 / 1000000000000 : ℝ) ≤ t →
        t ≤ (938422801667 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_447 V_446
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_447 :
    ∀ t,
      (938422801667 / 2000000000000 : ℝ) ≤ t →
        t ≤ (47053570071 / 100000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_448 V_447
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_448 :
    ∀ t,
      (47053570071 / 100000000000 : ℝ) ≤ t →
        t ≤ (943720001173 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_449 V_448
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_449 :
    ∀ t,
      (943720001173 / 2000000000000 : ℝ) ≤ t →
        t ≤ (473184300463 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_450 V_449
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_450 :
    ∀ t,
      (473184300463 / 1000000000000 : ℝ) ≤ t →
        t ≤ (949017200679 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_451 V_450
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_451 :
    ∀ t,
      (949017200679 / 2000000000000 : ℝ) ≤ t →
        t ≤ (59479112527 / 125000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_452 V_451
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_452 :
    ∀ t,
      (59479112527 / 125000000000 : ℝ) ≤ t →
        t ≤ (190862880037 / 400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_453 V_452
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_453 :
    ∀ t,
      (190862880037 / 400000000000 : ℝ) ≤ t →
        t ≤ (478481499969 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_454 V_453
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_454 :
    ∀ t,
      (478481499969 / 1000000000000 : ℝ) ≤ t →
        t ≤ (959611599691 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_455 V_454
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_455 :
    ∀ t,
      (959611599691 / 2000000000000 : ℝ) ≤ t →
        t ≤ (240565049861 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_456 V_455
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_456 :
    ∀ t,
      (240565049861 / 500000000000 : ℝ) ≤ t →
        t ≤ (19351147979 / 40000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_457 V_456
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_457 :
    ∀ t,
      (19351147979 / 40000000000 : ℝ) ≤ t →
        t ≤ (121606824807 / 250000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_458 V_457
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_458 :
    ∀ t,
      (121606824807 / 250000000000 : ℝ) ≤ t →
        t ≤ (489075898981 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_459 V_458
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_459 :
    ∀ t,
      (489075898981 / 1000000000000 : ℝ) ≤ t →
        t ≤ (245862249367 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_460 V_459
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_460 :
    ∀ t,
      (245862249367 / 500000000000 : ℝ) ≤ t →
        t ≤ (494373098487 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_461 V_460
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_461 :
    ∀ t,
      (494373098487 / 1000000000000 : ℝ) ≤ t →
        t ≤ (1553192807 / 3125000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_462 V_461
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_462 :
    ∀ t,
      (1553192807 / 3125000000 : ℝ) ≤ t →
        t ≤ (499670297993 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_463 V_462
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_463 :
    ∀ t,
      (499670297993 / 1000000000000 : ℝ) ≤ t →
        t ≤ (504967497499 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_464 V_463
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_464 :
    ∀ t,
      (504967497499 / 1000000000000 : ℝ) ≤ t →
        t ≤ (102052939401 / 200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_465 V_464
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_465 :
    ∀ t,
      (102052939401 / 200000000000 : ℝ) ≤ t →
        t ≤ (515561896511 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_466 V_465
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_466 :
    ∀ t,
      (515561896511 / 1000000000000 : ℝ) ≤ t →
        t ≤ (16577867570387 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_467 V_466
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_467 :
    ∀ t,
      (16577867570387 / 32000000000000 : ℝ) ≤ t →
        t ≤ (8328877226211 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_468 V_467
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_468 :
    ∀ t,
      (8328877226211 / 16000000000000 : ℝ) ≤ t →
        t ≤ (16737641334457 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_469 V_468
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_469 :
    ∀ t,
      (16737641334457 / 32000000000000 : ℝ) ≤ t →
        t ≤ (33555169550949 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_470 V_469
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_470 :
    ∀ t,
      (33555169550949 / 64000000000000 : ℝ) ≤ t →
        t ≤ (4204382054123 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_471 V_470
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_471 :
    ∀ t,
      (4204382054123 / 8000000000000 : ℝ) ≤ t →
        t ≤ (33714943315019 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_472 V_471
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_472 :
    ∀ t,
      (33714943315019 / 64000000000000 : ℝ) ≤ t →
        t ≤ (16897415098527 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_473 V_472
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_473 :
    ∀ t,
      (16897415098527 / 32000000000000 : ℝ) ≤ t →
        t ≤ (33874717079089 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_474 V_473
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_474 :
    ∀ t,
      (33874717079089 / 64000000000000 : ℝ) ≤ t →
        t ≤ (8488650990281 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_475 V_474
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_475 :
    ∀ t,
      (8488650990281 / 16000000000000 : ℝ) ≤ t →
        t ≤ (34034490843159 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_476 V_475
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_476 :
    ∀ t,
      (34034490843159 / 64000000000000 : ℝ) ≤ t →
        t ≤ (17057188862597 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_477 V_476
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_477 :
    ∀ t,
      (17057188862597 / 32000000000000 : ℝ) ≤ t →
        t ≤ (34194264607229 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_478 V_477
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_478 :
    ∀ t,
      (34194264607229 / 64000000000000 : ℝ) ≤ t →
        t ≤ (68468416096493 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_479 V_478
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_479 :
    ∀ t,
      (68468416096493 / 128000000000000 : ℝ) ≤ t →
        t ≤ (2142134468079 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_480 V_479
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_480 :
    ∀ t,
      (2142134468079 / 4000000000000 : ℝ) ≤ t →
        t ≤ (68628189860563 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_481 V_480
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_481 :
    ∀ t,
      (68628189860563 / 128000000000000 : ℝ) ≤ t →
        t ≤ (34354038371299 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_482 V_481
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_482 :
    ∀ t,
      (34354038371299 / 64000000000000 : ℝ) ≤ t →
        t ≤ (68787963624633 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_483 V_482
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_483 :
    ∀ t,
      (68787963624633 / 128000000000000 : ℝ) ≤ t →
        t ≤ (17216962626667 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_484 V_483
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_484 :
    ∀ t,
      (17216962626667 / 32000000000000 : ℝ) ≤ t →
        t ≤ (68947737388703 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_485 V_484
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_485 :
    ∀ t,
      (68947737388703 / 128000000000000 : ℝ) ≤ t →
        t ≤ (34513812135369 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_486 V_485
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_486 :
    ∀ t,
      (34513812135369 / 64000000000000 : ℝ) ≤ t →
        t ≤ (69107511152773 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_487 V_486
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_487 :
    ∀ t,
      (69107511152773 / 128000000000000 : ℝ) ≤ t →
        t ≤ (8648424754351 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_488 V_487
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_488 :
    ∀ t,
      (8648424754351 / 16000000000000 : ℝ) ≤ t →
        t ≤ (69267284916843 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_489 V_488
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_489 :
    ∀ t,
      (69267284916843 / 128000000000000 : ℝ) ≤ t →
        t ≤ (34673585899439 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_490 V_489
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_490 :
    ∀ t,
      (34673585899439 / 64000000000000 : ℝ) ≤ t →
        t ≤ (69427058680913 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_491 V_490
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_491 :
    ∀ t,
      (69427058680913 / 128000000000000 : ℝ) ≤ t →
        t ≤ (17376736390737 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_492 V_491
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_492 :
    ∀ t,
      (17376736390737 / 32000000000000 : ℝ) ≤ t →
        t ≤ (69586832444983 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_493 V_492
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_493 :
    ∀ t,
      (69586832444983 / 128000000000000 : ℝ) ≤ t →
        t ≤ (34833359663509 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_494 V_493
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_494 :
    ∀ t,
      (34833359663509 / 64000000000000 : ℝ) ≤ t →
        t ≤ (69746606209053 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_495 V_494
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_495 :
    ∀ t,
      (69746606209053 / 128000000000000 : ℝ) ≤ t →
        t ≤ (4364155818193 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_496 V_495
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_496 :
    ∀ t,
      (4364155818193 / 8000000000000 : ℝ) ≤ t →
        t ≤ (69906379973123 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_497 V_496
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_497 :
    ∀ t,
      (69906379973123 / 128000000000000 : ℝ) ≤ t →
        t ≤ (34993133427579 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_498 V_497
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_498 :
    ∀ t,
      (34993133427579 / 64000000000000 : ℝ) ≤ t →
        t ≤ (70066153737193 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_499 V_498
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_499 :
    ∀ t,
      (70066153737193 / 128000000000000 : ℝ) ≤ t →
        t ≤ (17536510154807 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_500 V_499
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_500 :
    ∀ t,
      (17536510154807 / 32000000000000 : ℝ) ≤ t →
        t ≤ (35152907191649 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_501 V_500
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_501 :
    ∀ t,
      (35152907191649 / 64000000000000 : ℝ) ≤ t →
        t ≤ (8808198518421 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_502 V_501
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_502 :
    ∀ t,
      (8808198518421 / 16000000000000 : ℝ) ≤ t →
        t ≤ (35312680955719 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_503 V_502
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_503 :
    ∀ t,
      (35312680955719 / 64000000000000 : ℝ) ≤ t →
        t ≤ (17696283918877 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_504 V_503
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_504 :
    ∀ t,
      (17696283918877 / 32000000000000 : ℝ) ≤ t →
        t ≤ (35472454719789 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_505 V_504
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_505 :
    ∀ t,
      (35472454719789 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1111010675057 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_506 V_505
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_506 :
    ∀ t,
      (1111010675057 / 2000000000000 : ℝ) ≤ t →
        t ≤ (35632228483859 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_507 V_506
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_507 :
    ∀ t,
      (35632228483859 / 64000000000000 : ℝ) ≤ t →
        t ≤ (17856057682947 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_508 V_507
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_508 :
    ∀ t,
      (17856057682947 / 32000000000000 : ℝ) ≤ t →
        t ≤ (35792002247929 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_509 V_508
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_509 :
    ∀ t,
      (35792002247929 / 64000000000000 : ℝ) ≤ t →
        t ≤ (8967972282491 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_510 V_509
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_510 :
    ∀ t,
      (8967972282491 / 16000000000000 : ℝ) ≤ t →
        t ≤ (35951776011999 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_511 V_510
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_511 :
    ∀ t,
      (35951776011999 / 64000000000000 : ℝ) ≤ t →
        t ≤ (18015831447017 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_512 V_511
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_512 :
    ∀ t,
      (18015831447017 / 32000000000000 : ℝ) ≤ t →
        t ≤ (36111549776069 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_513 V_512
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

end Zeta5Irrational
