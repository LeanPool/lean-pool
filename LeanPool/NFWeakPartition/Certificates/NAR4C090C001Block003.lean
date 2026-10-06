/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part010`. -/


section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb090_distinct_392 (u : Var) :
    (nb090AlphaDummy308 u) ≠ (nb090AlphaDummy310 u) := by
  simpa only [nb090AlphaDummy308, nb090AlphaDummy310] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_393 (u : Var) :
    (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy310 u) := by
  simpa only [nb090AlphaDummy309, nb090AlphaDummy310] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_394 (A : Class) :
    (nb090AlphaDummy317 A) ∉
      (((Class.cv (nb090AlphaDummy306 A))).fv ∪ ((Class.cv (nb090AlphaDummy306 A))).fv) :=
  by
  simpa only [nb090AlphaDummy317] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy306 A))).fv ∪ ((Class.cv (nb090AlphaDummy306 A))).fv)
      0

theorem nb090_fresh_395 (A : Class) :
    (nb090AlphaDummy313 A) ∉
      (((Class.cv (nb090AlphaDummy306 A))).fv ∪ ((Class.cv (nb090AlphaDummy307 A))).fv) :=
  by
  simpa only [nb090AlphaDummy313] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy306 A))).fv ∪ ((Class.cv (nb090AlphaDummy307 A))).fv)
      0

theorem nb090_fresh_396 (A : Class) :
    (nb090AlphaDummy319 A) ∉
      (((Class.cv (nb090AlphaDummy307 A))).fv ∪ ((Class.cv (nb090AlphaDummy307 A))).fv) :=
  by
  simpa only [nb090AlphaDummy319] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy307 A))).fv ∪ ((Class.cv (nb090AlphaDummy307 A))).fv)
      0

theorem nb090_fresh_397 (u : Var) :
    (nb090AlphaDummy318 u) ∉
      (((Class.cv (nb090AlphaDummy309 u))).fv ∪ ((Class.cv (nb090AlphaDummy309 u))).fv) :=
  by
  simpa only [nb090AlphaDummy318] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy309 u))).fv ∪ ((Class.cv (nb090AlphaDummy309 u))).fv)
      0

theorem nb090_fresh_398 (u : Var) :
    (nb090AlphaDummy314 u) ∉
      (((Class.cv (nb090AlphaDummy309 u))).fv ∪ ((Class.cv (nb090AlphaDummy310 u))).fv) :=
  by
  simpa only [nb090AlphaDummy314] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy309 u))).fv ∪ ((Class.cv (nb090AlphaDummy310 u))).fv)
      0

theorem nb090_fresh_399 (u : Var) :
    (nb090AlphaDummy320 u) ∉
      (((Class.cv (nb090AlphaDummy310 u))).fv ∪ ((Class.cv (nb090AlphaDummy310 u))).fv) :=
  by
  simpa only [nb090AlphaDummy320] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy310 u))).fv ∪ ((Class.cv (nb090AlphaDummy310 u))).fv)
      0

theorem nb090_fresh_400 (A : Class) :
    (nb090AlphaDummy337 A) ∉
      (((Class.cv (nb090AlphaDummy334 A))).fv ∪ ((Class.cv (nb090AlphaDummy333 A))).fv) :=
  by
  simpa only [nb090AlphaDummy337] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy334 A))).fv ∪ ((Class.cv (nb090AlphaDummy333 A))).fv)
      0

theorem nb090_fresh_401 (A : Class) :
    (nb090AlphaDummy338 A) ∉
      (((Class.cv (nb090AlphaDummy334 A))).fv ∪ ((Class.cv (nb090AlphaDummy333 A))).fv) :=
  by
  simpa only [nb090AlphaDummy338] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy334 A))).fv ∪ ((Class.cv (nb090AlphaDummy333 A))).fv)
      1

theorem nb090_distinct_402 (A : Class) :
    (nb090AlphaDummy337 A) ≠ (nb090AlphaDummy338 A) := by
  simpa only [nb090AlphaDummy337, nb090AlphaDummy338] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy334 A))).fv ∪
        ((Class.cv (nb090AlphaDummy333 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_403 (h : Var) :
    (nb090AlphaDummy339 h) ∉
      (((Class.cv (nb090AlphaDummy336 h))).fv ∪ ((Class.cv (nb090AlphaDummy335 h))).fv) :=
  by
  simpa only [nb090AlphaDummy339] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy336 h))).fv ∪ ((Class.cv (nb090AlphaDummy335 h))).fv)
      0

theorem nb090_fresh_404 (h : Var) :
    (nb090AlphaDummy340 h) ∉
      (((Class.cv (nb090AlphaDummy336 h))).fv ∪ ((Class.cv (nb090AlphaDummy335 h))).fv) :=
  by
  simpa only [nb090AlphaDummy340] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy336 h))).fv ∪ ((Class.cv (nb090AlphaDummy335 h))).fv)
      1

theorem nb090_distinct_405 (h : Var) :
    (nb090AlphaDummy339 h) ≠ (nb090AlphaDummy340 h) := by
  simpa only [nb090AlphaDummy339, nb090AlphaDummy340] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy336 h))).fv ∪
        ((Class.cv (nb090AlphaDummy335 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_406 (A : Class) :
    (nb090AlphaDummy345 A) ∉ (((Class.cv (nb090AlphaDummy338 A))).fv) := by
  simpa only [nb090AlphaDummy345] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy338 A))).fv) 0

theorem nb090_fresh_407 (A : Class) :
    (nb090AlphaDummy346 A) ∉ (((Class.cv (nb090AlphaDummy338 A))).fv) := by
  simpa only [nb090AlphaDummy346] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy338 A))).fv) 1

theorem nb090_distinct_408 (A : Class) :
    (nb090AlphaDummy345 A) ≠ (nb090AlphaDummy346 A) := by
  simpa only [nb090AlphaDummy345, nb090AlphaDummy346] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy338 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_409 (h : Var) :
    (nb090AlphaDummy347 h) ∉ (((Class.cv (nb090AlphaDummy340 h))).fv) := by
  simpa only [nb090AlphaDummy347] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy340 h))).fv) 0

theorem nb090_fresh_410 (h : Var) :
    (nb090AlphaDummy348 h) ∉ (((Class.cv (nb090AlphaDummy340 h))).fv) := by
  simpa only [nb090AlphaDummy348] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy340 h))).fv) 1

theorem nb090_distinct_411 (h : Var) :
    (nb090AlphaDummy347 h) ≠ (nb090AlphaDummy348 h) := by
  simpa only [nb090AlphaDummy347, nb090AlphaDummy348] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy340 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_412 (A : Class) :
    (nb090AlphaDummy351 A) ∉
      (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy351] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_413 (A : Class) :
    (nb090AlphaDummy352 A) ∉
      (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy352] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_414 (A : Class) :
    (nb090AlphaDummy353 A) ∉
      (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy353] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_415 (A : Class) :
    (nb090AlphaDummy351 A) ≠ (nb090AlphaDummy352 A) := by
  simpa only [nb090AlphaDummy351, nb090AlphaDummy352] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_416 (A : Class) :
    (nb090AlphaDummy351 A) ≠ (nb090AlphaDummy353 A) := by
  simpa only [nb090AlphaDummy351, nb090AlphaDummy353] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_417 (A : Class) :
    (nb090AlphaDummy352 A) ≠ (nb090AlphaDummy353 A) := by
  simpa only [nb090AlphaDummy352, nb090AlphaDummy353] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_418 (h : Var) :
    (nb090AlphaDummy354 h) ∉
      (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy354] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_419 (h : Var) :
    (nb090AlphaDummy355 h) ∉
      (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy355] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_420 (h : Var) :
    (nb090AlphaDummy356 h) ∉
      (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy356] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_421 (h : Var) :
    (nb090AlphaDummy354 h) ≠ (nb090AlphaDummy355 h) := by
  simpa only [nb090AlphaDummy354, nb090AlphaDummy355] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_422 (h : Var) :
    (nb090AlphaDummy354 h) ≠ (nb090AlphaDummy356 h) := by
  simpa only [nb090AlphaDummy354, nb090AlphaDummy356] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_423 (h : Var) :
    (nb090AlphaDummy355 h) ≠ (nb090AlphaDummy356 h) := by
  simpa only [nb090AlphaDummy355, nb090AlphaDummy356] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_424 (A : Class) :
    (nb090AlphaDummy363 A) ∉
      (((Class.cv (nb090AlphaDummy352 A))).fv ∪ ((Class.cv (nb090AlphaDummy352 A))).fv) :=
  by
  simpa only [nb090AlphaDummy363] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy352 A))).fv ∪ ((Class.cv (nb090AlphaDummy352 A))).fv)
      0

theorem nb090_fresh_425 (A : Class) :
    (nb090AlphaDummy359 A) ∉
      (((Class.cv (nb090AlphaDummy352 A))).fv ∪ ((Class.cv (nb090AlphaDummy353 A))).fv) :=
  by
  simpa only [nb090AlphaDummy359] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy352 A))).fv ∪ ((Class.cv (nb090AlphaDummy353 A))).fv)
      0

theorem nb090_fresh_426 (A : Class) :
    (nb090AlphaDummy365 A) ∉
      (((Class.cv (nb090AlphaDummy353 A))).fv ∪ ((Class.cv (nb090AlphaDummy353 A))).fv) :=
  by
  simpa only [nb090AlphaDummy365] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy353 A))).fv ∪ ((Class.cv (nb090AlphaDummy353 A))).fv)
      0

theorem nb090_fresh_427 (h : Var) :
    (nb090AlphaDummy364 h) ∉
      (((Class.cv (nb090AlphaDummy355 h))).fv ∪ ((Class.cv (nb090AlphaDummy355 h))).fv) :=
  by
  simpa only [nb090AlphaDummy364] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy355 h))).fv ∪ ((Class.cv (nb090AlphaDummy355 h))).fv)
      0

theorem nb090_fresh_428 (h : Var) :
    (nb090AlphaDummy360 h) ∉
      (((Class.cv (nb090AlphaDummy355 h))).fv ∪ ((Class.cv (nb090AlphaDummy356 h))).fv) :=
  by
  simpa only [nb090AlphaDummy360] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy355 h))).fv ∪ ((Class.cv (nb090AlphaDummy356 h))).fv)
      0

theorem nb090_fresh_429 (h : Var) :
    (nb090AlphaDummy366 h) ∉
      (((Class.cv (nb090AlphaDummy356 h))).fv ∪ ((Class.cv (nb090AlphaDummy356 h))).fv) :=
  by
  simpa only [nb090AlphaDummy366] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy356 h))).fv ∪ ((Class.cv (nb090AlphaDummy356 h))).fv)
      0

theorem nb090_fresh_430 (A : Class) :
    (nb090AlphaDummy417 A) ∉ (((Class.cv (nb090AlphaDummy375 A))).fv) := by
  simpa only [nb090AlphaDummy417] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy375 A))).fv) 0

theorem nb090_fresh_431 (v : Var) :
    (nb090AlphaDummy418 v) ∉ (((Class.cv (nb090AlphaDummy376 v))).fv) := by
  simpa only [nb090AlphaDummy418] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy376 v))).fv) 0

theorem nb090_fresh_432 (A : Class) :
    (nb090AlphaDummy389 A) ∉ (((Class.cv (nb090AlphaDummy382 A))).fv) := by
  simpa only [nb090AlphaDummy389] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy382 A))).fv) 0

theorem nb090_fresh_433 (A : Class) :
    (nb090AlphaDummy390 A) ∉ (((Class.cv (nb090AlphaDummy382 A))).fv) := by
  simpa only [nb090AlphaDummy390] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy382 A))).fv) 1

theorem nb090_distinct_434 (A : Class) :
    (nb090AlphaDummy389 A) ≠ (nb090AlphaDummy390 A) := by
  simpa only [nb090AlphaDummy389, nb090AlphaDummy390] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy382 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_435 (v : Var) :
    (nb090AlphaDummy391 v) ∉ (((Class.cv (nb090AlphaDummy384 v))).fv) := by
  simpa only [nb090AlphaDummy391] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy384 v))).fv) 0

theorem nb090_fresh_436 (v : Var) :
    (nb090AlphaDummy392 v) ∉ (((Class.cv (nb090AlphaDummy384 v))).fv) := by
  simpa only [nb090AlphaDummy392] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy384 v))).fv) 1

theorem nb090_distinct_437 (v : Var) :
    (nb090AlphaDummy391 v) ≠ (nb090AlphaDummy392 v) := by
  simpa only [nb090AlphaDummy391, nb090AlphaDummy392] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy384 v))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_438 (A : Class) :
    (nb090AlphaDummy395 A) ∉
      (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy395] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_439 (A : Class) :
    (nb090AlphaDummy396 A) ∉
      (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy396] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_440 (A : Class) :
    (nb090AlphaDummy397 A) ∉
      (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy397] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_441 (A : Class) :
    (nb090AlphaDummy395 A) ≠ (nb090AlphaDummy396 A) := by
  simpa only [nb090AlphaDummy395, nb090AlphaDummy396] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_442 (A : Class) :
    (nb090AlphaDummy395 A) ≠ (nb090AlphaDummy397 A) := by
  simpa only [nb090AlphaDummy395, nb090AlphaDummy397] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_443 (A : Class) :
    (nb090AlphaDummy396 A) ≠ (nb090AlphaDummy397 A) := by
  simpa only [nb090AlphaDummy396, nb090AlphaDummy397] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_444 (v : Var) :
    (nb090AlphaDummy398 v) ∉
      (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy398] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_445 (v : Var) :
    (nb090AlphaDummy399 v) ∉
      (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy399] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_446 (v : Var) :
    (nb090AlphaDummy400 v) ∉
      (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy400] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_447 (v : Var) :
    (nb090AlphaDummy398 v) ≠ (nb090AlphaDummy399 v) := by
  simpa only [nb090AlphaDummy398, nb090AlphaDummy399] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_448 (v : Var) :
    (nb090AlphaDummy398 v) ≠ (nb090AlphaDummy400 v) := by
  simpa only [nb090AlphaDummy398, nb090AlphaDummy400] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_449 (v : Var) :
    (nb090AlphaDummy399 v) ≠ (nb090AlphaDummy400 v) := by
  simpa only [nb090AlphaDummy399, nb090AlphaDummy400] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_450 (A : Class) :
    (nb090AlphaDummy407 A) ∉
      (((Class.cv (nb090AlphaDummy396 A))).fv ∪ ((Class.cv (nb090AlphaDummy396 A))).fv) :=
  by
  simpa only [nb090AlphaDummy407] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy396 A))).fv ∪ ((Class.cv (nb090AlphaDummy396 A))).fv)
      0

theorem nb090_fresh_451 (A : Class) :
    (nb090AlphaDummy403 A) ∉
      (((Class.cv (nb090AlphaDummy396 A))).fv ∪ ((Class.cv (nb090AlphaDummy397 A))).fv) :=
  by
  simpa only [nb090AlphaDummy403] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy396 A))).fv ∪ ((Class.cv (nb090AlphaDummy397 A))).fv)
      0

theorem nb090_fresh_452 (A : Class) :
    (nb090AlphaDummy409 A) ∉
      (((Class.cv (nb090AlphaDummy397 A))).fv ∪ ((Class.cv (nb090AlphaDummy397 A))).fv) :=
  by
  simpa only [nb090AlphaDummy409] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy397 A))).fv ∪ ((Class.cv (nb090AlphaDummy397 A))).fv)
      0

theorem nb090_fresh_453 (v : Var) :
    (nb090AlphaDummy408 v) ∉
      (((Class.cv (nb090AlphaDummy399 v))).fv ∪ ((Class.cv (nb090AlphaDummy399 v))).fv) :=
  by
  simpa only [nb090AlphaDummy408] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy399 v))).fv ∪ ((Class.cv (nb090AlphaDummy399 v))).fv)
      0

theorem nb090_fresh_454 (v : Var) :
    (nb090AlphaDummy404 v) ∉
      (((Class.cv (nb090AlphaDummy399 v))).fv ∪ ((Class.cv (nb090AlphaDummy400 v))).fv) :=
  by
  simpa only [nb090AlphaDummy404] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy399 v))).fv ∪ ((Class.cv (nb090AlphaDummy400 v))).fv)
      0

theorem nb090_fresh_455 (v : Var) :
    (nb090AlphaDummy410 v) ∉
      (((Class.cv (nb090AlphaDummy400 v))).fv ∪ ((Class.cv (nb090AlphaDummy400 v))).fv) :=
  by
  simpa only [nb090AlphaDummy410] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy400 v))).fv ∪ ((Class.cv (nb090AlphaDummy400 v))).fv)
      0

theorem nb090_fresh_456 (A : Class) :
    (nb090AlphaDummy431 A) ∉
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv) :=
  by
  simpa only [nb090AlphaDummy431] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv)
      0

theorem nb090_fresh_457 (A : Class) :
    (nb090AlphaDummy432 A) ∉
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv) :=
  by
  simpa only [nb090AlphaDummy432] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv)
      1

theorem nb090_distinct_458 (A : Class) :
    (nb090AlphaDummy431 A) ≠ (nb090AlphaDummy432 A) := by
  simpa only [nb090AlphaDummy431, nb090AlphaDummy432] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy423 A))).fv ∪
        ((Class.cv (nb090AlphaDummy424 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_459 (A : Class) :
    (nb090AlphaDummy467 A) ∉
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy425 A))).fv) :=
  by
  simpa only [nb090AlphaDummy467] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy425 A))).fv)
      0

theorem nb090_fresh_460 (A : Class) :
    (nb090AlphaDummy468 A) ∉
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy425 A))).fv) :=
  by
  simpa only [nb090AlphaDummy468] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy425 A))).fv)
      1

theorem nb090_distinct_461 (A : Class) :
    (nb090AlphaDummy467 A) ≠ (nb090AlphaDummy468 A) := by
  simpa only [nb090AlphaDummy467, nb090AlphaDummy468] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy423 A))).fv ∪
        ((Class.cv (nb090AlphaDummy425 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_462 (A : Class) :
    (nb090AlphaDummy581 A) ∉
      (((Class.cv (nb090AlphaDummy425 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv) :=
  by
  simpa only [nb090AlphaDummy581] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy425 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv)
      0

theorem nb090_fresh_463 (A : Class) :
    (nb090AlphaDummy582 A) ∉
      (((Class.cv (nb090AlphaDummy425 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv) :=
  by
  simpa only [nb090AlphaDummy582] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy425 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv)
      1

theorem nb090_distinct_464 (A : Class) :
    (nb090AlphaDummy581 A) ≠ (nb090AlphaDummy582 A) := by
  simpa only [nb090AlphaDummy581, nb090AlphaDummy582] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy425 A))).fv ∪
        ((Class.cv (nb090AlphaDummy424 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_465 (h : Var) :
    (nb090AlphaDummy433 h) ∉
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv) :=
  by
  simpa only [nb090AlphaDummy433] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv)
      0

theorem nb090_fresh_466 (h : Var) :
    (nb090AlphaDummy434 h) ∉
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv) :=
  by
  simpa only [nb090AlphaDummy434] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv)
      1

theorem nb090_distinct_467 (h : Var) :
    (nb090AlphaDummy433 h) ≠ (nb090AlphaDummy434 h) := by
  simpa only [nb090AlphaDummy433, nb090AlphaDummy434] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy426 h))).fv ∪
        ((Class.cv (nb090AlphaDummy427 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_468 (h : Var) :
    (nb090AlphaDummy469 h) ∉
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy428 h))).fv) :=
  by
  simpa only [nb090AlphaDummy469] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy428 h))).fv)
      0

theorem nb090_fresh_469 (h : Var) :
    (nb090AlphaDummy470 h) ∉
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy428 h))).fv) :=
  by
  simpa only [nb090AlphaDummy470] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy428 h))).fv)
      1

theorem nb090_distinct_470 (h : Var) :
    (nb090AlphaDummy469 h) ≠ (nb090AlphaDummy470 h) := by
  simpa only [nb090AlphaDummy469, nb090AlphaDummy470] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy426 h))).fv ∪
        ((Class.cv (nb090AlphaDummy428 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_471 (h : Var) :
    (nb090AlphaDummy583 h) ∉
      (((Class.cv (nb090AlphaDummy428 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv) :=
  by
  simpa only [nb090AlphaDummy583] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy428 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv)
      0

theorem nb090_fresh_472 (h : Var) :
    (nb090AlphaDummy584 h) ∉
      (((Class.cv (nb090AlphaDummy428 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv) :=
  by
  simpa only [nb090AlphaDummy584] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy428 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv)
      1

theorem nb090_distinct_473 (h : Var) :
    (nb090AlphaDummy583 h) ≠ (nb090AlphaDummy584 h) := by
  simpa only [nb090AlphaDummy583, nb090AlphaDummy584] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy428 h))).fv ∪
        ((Class.cv (nb090AlphaDummy427 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_474 (A : Class) :
    (nb090AlphaDummy439 A) ∉ (((Class.cv (nb090AlphaDummy432 A))).fv) := by
  simpa only [nb090AlphaDummy439] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy432 A))).fv) 0

theorem nb090_fresh_475 (A : Class) :
    (nb090AlphaDummy440 A) ∉ (((Class.cv (nb090AlphaDummy432 A))).fv) := by
  simpa only [nb090AlphaDummy440] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy432 A))).fv) 1

theorem nb090_distinct_476 (A : Class) :
    (nb090AlphaDummy439 A) ≠ (nb090AlphaDummy440 A) := by
  simpa only [nb090AlphaDummy439, nb090AlphaDummy440] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy432 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_477 (h : Var) :
    (nb090AlphaDummy441 h) ∉ (((Class.cv (nb090AlphaDummy434 h))).fv) := by
  simpa only [nb090AlphaDummy441] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy434 h))).fv) 0

theorem nb090_fresh_478 (h : Var) :
    (nb090AlphaDummy442 h) ∉ (((Class.cv (nb090AlphaDummy434 h))).fv) := by
  simpa only [nb090AlphaDummy442] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy434 h))).fv) 1

theorem nb090_distinct_479 (h : Var) :
    (nb090AlphaDummy441 h) ≠ (nb090AlphaDummy442 h) := by
  simpa only [nb090AlphaDummy441, nb090AlphaDummy442] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy434 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_480 (A : Class) :
    (nb090AlphaDummy445 A) ∉
      (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy445] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_481 (A : Class) :
    (nb090AlphaDummy446 A) ∉
      (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy446] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_482 (A : Class) :
    (nb090AlphaDummy447 A) ∉
      (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy447] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_483 (A : Class) :
    (nb090AlphaDummy445 A) ≠ (nb090AlphaDummy446 A) := by
  simpa only [nb090AlphaDummy445, nb090AlphaDummy446] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_484 (A : Class) :
    (nb090AlphaDummy445 A) ≠ (nb090AlphaDummy447 A) := by
  simpa only [nb090AlphaDummy445, nb090AlphaDummy447] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_485 (A : Class) :
    (nb090AlphaDummy446 A) ≠ (nb090AlphaDummy447 A) := by
  simpa only [nb090AlphaDummy446, nb090AlphaDummy447] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_486 (h : Var) :
    (nb090AlphaDummy448 h) ∉
      (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy448] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_487 (h : Var) :
    (nb090AlphaDummy449 h) ∉
      (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy449] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_488 (h : Var) :
    (nb090AlphaDummy450 h) ∉
      (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy450] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_489 (h : Var) :
    (nb090AlphaDummy448 h) ≠ (nb090AlphaDummy449 h) := by
  simpa only [nb090AlphaDummy448, nb090AlphaDummy449] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_490 (h : Var) :
    (nb090AlphaDummy448 h) ≠ (nb090AlphaDummy450 h) := by
  simpa only [nb090AlphaDummy448, nb090AlphaDummy450] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_491 (h : Var) :
    (nb090AlphaDummy449 h) ≠ (nb090AlphaDummy450 h) := by
  simpa only [nb090AlphaDummy449, nb090AlphaDummy450] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_492 (A : Class) :
    (nb090AlphaDummy457 A) ∉
      (((Class.cv (nb090AlphaDummy446 A))).fv ∪ ((Class.cv (nb090AlphaDummy446 A))).fv) :=
  by
  simpa only [nb090AlphaDummy457] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy446 A))).fv ∪ ((Class.cv (nb090AlphaDummy446 A))).fv)
      0

theorem nb090_fresh_493 (A : Class) :
    (nb090AlphaDummy453 A) ∉
      (((Class.cv (nb090AlphaDummy446 A))).fv ∪ ((Class.cv (nb090AlphaDummy447 A))).fv) :=
  by
  simpa only [nb090AlphaDummy453] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy446 A))).fv ∪ ((Class.cv (nb090AlphaDummy447 A))).fv)
      0

theorem nb090_fresh_494 (A : Class) :
    (nb090AlphaDummy459 A) ∉
      (((Class.cv (nb090AlphaDummy447 A))).fv ∪ ((Class.cv (nb090AlphaDummy447 A))).fv) :=
  by
  simpa only [nb090AlphaDummy459] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy447 A))).fv ∪ ((Class.cv (nb090AlphaDummy447 A))).fv)
      0

theorem nb090_fresh_495 (h : Var) :
    (nb090AlphaDummy458 h) ∉
      (((Class.cv (nb090AlphaDummy449 h))).fv ∪ ((Class.cv (nb090AlphaDummy449 h))).fv) :=
  by
  simpa only [nb090AlphaDummy458] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy449 h))).fv ∪ ((Class.cv (nb090AlphaDummy449 h))).fv)
      0

theorem nb090_fresh_496 (h : Var) :
    (nb090AlphaDummy454 h) ∉
      (((Class.cv (nb090AlphaDummy449 h))).fv ∪ ((Class.cv (nb090AlphaDummy450 h))).fv) :=
  by
  simpa only [nb090AlphaDummy454] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy449 h))).fv ∪ ((Class.cv (nb090AlphaDummy450 h))).fv)
      0

theorem nb090_fresh_497 (h : Var) :
    (nb090AlphaDummy460 h) ∉
      (((Class.cv (nb090AlphaDummy450 h))).fv ∪ ((Class.cv (nb090AlphaDummy450 h))).fv) :=
  by
  simpa only [nb090AlphaDummy460] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy450 h))).fv ∪ ((Class.cv (nb090AlphaDummy450 h))).fv)
      0

theorem nb090_fresh_498 (A : Class) :
    (nb090AlphaDummy475 A) ∉ (((Class.cv (nb090AlphaDummy468 A))).fv) := by
  simpa only [nb090AlphaDummy475] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy468 A))).fv) 0

theorem nb090_fresh_499 (A : Class) :
    (nb090AlphaDummy476 A) ∉ (((Class.cv (nb090AlphaDummy468 A))).fv) := by
  simpa only [nb090AlphaDummy476] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy468 A))).fv) 1

theorem nb090_distinct_500 (A : Class) :
    (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy476 A) := by
  simpa only [nb090AlphaDummy475, nb090AlphaDummy476] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy468 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_501 (h : Var) :
    (nb090AlphaDummy477 h) ∉ (((Class.cv (nb090AlphaDummy470 h))).fv) := by
  simpa only [nb090AlphaDummy477] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy470 h))).fv) 0

theorem nb090_fresh_502 (h : Var) :
    (nb090AlphaDummy478 h) ∉ (((Class.cv (nb090AlphaDummy470 h))).fv) := by
  simpa only [nb090AlphaDummy478] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy470 h))).fv) 1

theorem nb090_distinct_503 (h : Var) :
    (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy478 h) := by
  simpa only [nb090AlphaDummy477, nb090AlphaDummy478] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy470 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_504 (A : Class) :
    (nb090AlphaDummy481 A) ∉
      (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy481] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_505 (A : Class) :
    (nb090AlphaDummy482 A) ∉
      (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy482] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_506 (A : Class) :
    (nb090AlphaDummy483 A) ∉
      (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy483] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_507 (A : Class) :
    (nb090AlphaDummy481 A) ≠ (nb090AlphaDummy482 A) := by
  simpa only [nb090AlphaDummy481, nb090AlphaDummy482] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_508 (A : Class) :
    (nb090AlphaDummy481 A) ≠ (nb090AlphaDummy483 A) := by
  simpa only [nb090AlphaDummy481, nb090AlphaDummy483] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_509 (A : Class) :
    (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy483 A) := by
  simpa only [nb090AlphaDummy482, nb090AlphaDummy483] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_510 (h : Var) :
    (nb090AlphaDummy484 h) ∉
      (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy484] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_511 (h : Var) :
    (nb090AlphaDummy485 h) ∉
      (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy485] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_512 (h : Var) :
    (nb090AlphaDummy486 h) ∉
      (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy486] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_513 (h : Var) :
    (nb090AlphaDummy484 h) ≠ (nb090AlphaDummy485 h) := by
  simpa only [nb090AlphaDummy484, nb090AlphaDummy485] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_514 (h : Var) :
    (nb090AlphaDummy484 h) ≠ (nb090AlphaDummy486 h) := by
  simpa only [nb090AlphaDummy484, nb090AlphaDummy486] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_515 (h : Var) :
    (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy486 h) := by
  simpa only [nb090AlphaDummy485, nb090AlphaDummy486] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_516 (A : Class) :
    (nb090AlphaDummy493 A) ∉
      (((Class.cv (nb090AlphaDummy482 A))).fv ∪ ((Class.cv (nb090AlphaDummy482 A))).fv) :=
  by
  simpa only [nb090AlphaDummy493] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy482 A))).fv ∪ ((Class.cv (nb090AlphaDummy482 A))).fv)
      0

theorem nb090_fresh_517 (A : Class) :
    (nb090AlphaDummy489 A) ∉
      (((Class.cv (nb090AlphaDummy482 A))).fv ∪ ((Class.cv (nb090AlphaDummy483 A))).fv) :=
  by
  simpa only [nb090AlphaDummy489] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy482 A))).fv ∪ ((Class.cv (nb090AlphaDummy483 A))).fv)
      0

theorem nb090_fresh_518 (A : Class) :
    (nb090AlphaDummy495 A) ∉
      (((Class.cv (nb090AlphaDummy483 A))).fv ∪ ((Class.cv (nb090AlphaDummy483 A))).fv) :=
  by
  simpa only [nb090AlphaDummy495] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy483 A))).fv ∪ ((Class.cv (nb090AlphaDummy483 A))).fv)
      0

theorem nb090_fresh_519 (h : Var) :
    (nb090AlphaDummy494 h) ∉
      (((Class.cv (nb090AlphaDummy485 h))).fv ∪ ((Class.cv (nb090AlphaDummy485 h))).fv) :=
  by
  simpa only [nb090AlphaDummy494] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy485 h))).fv ∪ ((Class.cv (nb090AlphaDummy485 h))).fv)
      0

theorem nb090_fresh_520 (h : Var) :
    (nb090AlphaDummy490 h) ∉
      (((Class.cv (nb090AlphaDummy485 h))).fv ∪ ((Class.cv (nb090AlphaDummy486 h))).fv) :=
  by
  simpa only [nb090AlphaDummy490] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy485 h))).fv ∪ ((Class.cv (nb090AlphaDummy486 h))).fv)
      0

theorem nb090_fresh_521 (h : Var) :
    (nb090AlphaDummy496 h) ∉
      (((Class.cv (nb090AlphaDummy486 h))).fv ∪ ((Class.cv (nb090AlphaDummy486 h))).fv) :=
  by
  simpa only [nb090AlphaDummy496] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy486 h))).fv ∪ ((Class.cv (nb090AlphaDummy486 h))).fv)
      0

theorem nb090_fresh_522 (A : Class) :
    (nb090AlphaDummy509 A) ∉
      (((Class.cv (nb090AlphaDummy503 A))).fv ∪ ((Class.cv (nb090AlphaDummy504 A))).fv) :=
  by
  simpa only [nb090AlphaDummy509] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy503 A))).fv ∪ ((Class.cv (nb090AlphaDummy504 A))).fv)
      0

theorem nb090_fresh_523 (A : Class) :
    (nb090AlphaDummy510 A) ∉
      (((Class.cv (nb090AlphaDummy503 A))).fv ∪ ((Class.cv (nb090AlphaDummy504 A))).fv) :=
  by
  simpa only [nb090AlphaDummy510] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy503 A))).fv ∪ ((Class.cv (nb090AlphaDummy504 A))).fv)
      1

theorem nb090_distinct_524 (A : Class) :
    (nb090AlphaDummy509 A) ≠ (nb090AlphaDummy510 A) := by
  simpa only [nb090AlphaDummy509, nb090AlphaDummy510] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy503 A))).fv ∪
        ((Class.cv (nb090AlphaDummy504 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_525 (A : Class) :
    (nb090AlphaDummy545 A) ∉
      (((Class.cv (nb090AlphaDummy504 A))).fv ∪ ((Class.cv (nb090AlphaDummy503 A))).fv) :=
  by
  simpa only [nb090AlphaDummy545] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy504 A))).fv ∪ ((Class.cv (nb090AlphaDummy503 A))).fv)
      0

theorem nb090_fresh_526 (A : Class) :
    (nb090AlphaDummy546 A) ∉
      (((Class.cv (nb090AlphaDummy504 A))).fv ∪ ((Class.cv (nb090AlphaDummy503 A))).fv) :=
  by
  simpa only [nb090AlphaDummy546] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy504 A))).fv ∪ ((Class.cv (nb090AlphaDummy503 A))).fv)
      1

theorem nb090_distinct_527 (A : Class) :
    (nb090AlphaDummy545 A) ≠ (nb090AlphaDummy546 A) := by
  simpa only [nb090AlphaDummy545, nb090AlphaDummy546] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy504 A))).fv ∪
        ((Class.cv (nb090AlphaDummy503 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_528 (h : Var) :
    (nb090AlphaDummy511 h) ∉
      (((Class.cv (nb090AlphaDummy505 h))).fv ∪ ((Class.cv (nb090AlphaDummy506 h))).fv) :=
  by
  simpa only [nb090AlphaDummy511] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy505 h))).fv ∪ ((Class.cv (nb090AlphaDummy506 h))).fv)
      0

theorem nb090_fresh_529 (h : Var) :
    (nb090AlphaDummy512 h) ∉
      (((Class.cv (nb090AlphaDummy505 h))).fv ∪ ((Class.cv (nb090AlphaDummy506 h))).fv) :=
  by
  simpa only [nb090AlphaDummy512] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy505 h))).fv ∪ ((Class.cv (nb090AlphaDummy506 h))).fv)
      1

theorem nb090_distinct_530 (h : Var) :
    (nb090AlphaDummy511 h) ≠ (nb090AlphaDummy512 h) := by
  simpa only [nb090AlphaDummy511, nb090AlphaDummy512] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy505 h))).fv ∪
        ((Class.cv (nb090AlphaDummy506 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_531 (h : Var) :
    (nb090AlphaDummy547 h) ∉
      (((Class.cv (nb090AlphaDummy506 h))).fv ∪ ((Class.cv (nb090AlphaDummy505 h))).fv) :=
  by
  simpa only [nb090AlphaDummy547] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy506 h))).fv ∪ ((Class.cv (nb090AlphaDummy505 h))).fv)
      0

theorem nb090_fresh_532 (h : Var) :
    (nb090AlphaDummy548 h) ∉
      (((Class.cv (nb090AlphaDummy506 h))).fv ∪ ((Class.cv (nb090AlphaDummy505 h))).fv) :=
  by
  simpa only [nb090AlphaDummy548] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy506 h))).fv ∪ ((Class.cv (nb090AlphaDummy505 h))).fv)
      1

theorem nb090_distinct_533 (h : Var) :
    (nb090AlphaDummy547 h) ≠ (nb090AlphaDummy548 h) := by
  simpa only [nb090AlphaDummy547, nb090AlphaDummy548] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy506 h))).fv ∪
        ((Class.cv (nb090AlphaDummy505 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_534 (A : Class) :
    (nb090AlphaDummy517 A) ∉ (((Class.cv (nb090AlphaDummy510 A))).fv) := by
  simpa only [nb090AlphaDummy517] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy510 A))).fv) 0

theorem nb090_fresh_535 (A : Class) :
    (nb090AlphaDummy518 A) ∉ (((Class.cv (nb090AlphaDummy510 A))).fv) := by
  simpa only [nb090AlphaDummy518] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy510 A))).fv) 1

theorem nb090_distinct_536 (A : Class) :
    (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy518 A) := by
  simpa only [nb090AlphaDummy517, nb090AlphaDummy518] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy510 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_537 (h : Var) :
    (nb090AlphaDummy519 h) ∉ (((Class.cv (nb090AlphaDummy512 h))).fv) := by
  simpa only [nb090AlphaDummy519] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy512 h))).fv) 0

theorem nb090_fresh_538 (h : Var) :
    (nb090AlphaDummy520 h) ∉ (((Class.cv (nb090AlphaDummy512 h))).fv) := by
  simpa only [nb090AlphaDummy520] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy512 h))).fv) 1

theorem nb090_distinct_539 (h : Var) :
    (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy520 h) := by
  simpa only [nb090AlphaDummy519, nb090AlphaDummy520] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy512 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_540 (A : Class) :
    (nb090AlphaDummy523 A) ∉
      (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy523] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_541 (A : Class) :
    (nb090AlphaDummy524 A) ∉
      (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy524] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part011`. -/


section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb090_fresh_542 (A : Class) :
    (nb090AlphaDummy525 A) ∉
      (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy525] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_543 (A : Class) :
    (nb090AlphaDummy523 A) ≠ (nb090AlphaDummy524 A) := by
  simpa only [nb090AlphaDummy523, nb090AlphaDummy524] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_544 (A : Class) :
    (nb090AlphaDummy523 A) ≠ (nb090AlphaDummy525 A) := by
  simpa only [nb090AlphaDummy523, nb090AlphaDummy525] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_545 (A : Class) :
    (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy525 A) := by
  simpa only [nb090AlphaDummy524, nb090AlphaDummy525] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_546 (h : Var) :
    (nb090AlphaDummy526 h) ∉
      (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy526] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_547 (h : Var) :
    (nb090AlphaDummy527 h) ∉
      (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy527] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_548 (h : Var) :
    (nb090AlphaDummy528 h) ∉
      (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy528] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_549 (h : Var) :
    (nb090AlphaDummy526 h) ≠ (nb090AlphaDummy527 h) := by
  simpa only [nb090AlphaDummy526, nb090AlphaDummy527] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_550 (h : Var) :
    (nb090AlphaDummy526 h) ≠ (nb090AlphaDummy528 h) := by
  simpa only [nb090AlphaDummy526, nb090AlphaDummy528] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_551 (h : Var) :
    (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy528 h) := by
  simpa only [nb090AlphaDummy527, nb090AlphaDummy528] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_552 (A : Class) :
    (nb090AlphaDummy535 A) ∉
      (((Class.cv (nb090AlphaDummy524 A))).fv ∪ ((Class.cv (nb090AlphaDummy524 A))).fv) :=
  by
  simpa only [nb090AlphaDummy535] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy524 A))).fv ∪ ((Class.cv (nb090AlphaDummy524 A))).fv)
      0

theorem nb090_fresh_553 (A : Class) :
    (nb090AlphaDummy531 A) ∉
      (((Class.cv (nb090AlphaDummy524 A))).fv ∪ ((Class.cv (nb090AlphaDummy525 A))).fv) :=
  by
  simpa only [nb090AlphaDummy531] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy524 A))).fv ∪ ((Class.cv (nb090AlphaDummy525 A))).fv)
      0

theorem nb090_fresh_554 (A : Class) :
    (nb090AlphaDummy537 A) ∉
      (((Class.cv (nb090AlphaDummy525 A))).fv ∪ ((Class.cv (nb090AlphaDummy525 A))).fv) :=
  by
  simpa only [nb090AlphaDummy537] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy525 A))).fv ∪ ((Class.cv (nb090AlphaDummy525 A))).fv)
      0

theorem nb090_fresh_555 (h : Var) :
    (nb090AlphaDummy536 h) ∉
      (((Class.cv (nb090AlphaDummy527 h))).fv ∪ ((Class.cv (nb090AlphaDummy527 h))).fv) :=
  by
  simpa only [nb090AlphaDummy536] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy527 h))).fv ∪ ((Class.cv (nb090AlphaDummy527 h))).fv)
      0

theorem nb090_fresh_556 (h : Var) :
    (nb090AlphaDummy532 h) ∉
      (((Class.cv (nb090AlphaDummy527 h))).fv ∪ ((Class.cv (nb090AlphaDummy528 h))).fv) :=
  by
  simpa only [nb090AlphaDummy532] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy527 h))).fv ∪ ((Class.cv (nb090AlphaDummy528 h))).fv)
      0

theorem nb090_fresh_557 (h : Var) :
    (nb090AlphaDummy538 h) ∉
      (((Class.cv (nb090AlphaDummy528 h))).fv ∪ ((Class.cv (nb090AlphaDummy528 h))).fv) :=
  by
  simpa only [nb090AlphaDummy538] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy528 h))).fv ∪ ((Class.cv (nb090AlphaDummy528 h))).fv)
      0

theorem nb090_fresh_558 (A : Class) :
    (nb090AlphaDummy553 A) ∉ (((Class.cv (nb090AlphaDummy546 A))).fv) := by
  simpa only [nb090AlphaDummy553] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy546 A))).fv) 0

theorem nb090_fresh_559 (A : Class) :
    (nb090AlphaDummy554 A) ∉ (((Class.cv (nb090AlphaDummy546 A))).fv) := by
  simpa only [nb090AlphaDummy554] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy546 A))).fv) 1

theorem nb090_distinct_560 (A : Class) :
    (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy554 A) := by
  simpa only [nb090AlphaDummy553, nb090AlphaDummy554] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy546 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_561 (h : Var) :
    (nb090AlphaDummy555 h) ∉ (((Class.cv (nb090AlphaDummy548 h))).fv) := by
  simpa only [nb090AlphaDummy555] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy548 h))).fv) 0

theorem nb090_fresh_562 (h : Var) :
    (nb090AlphaDummy556 h) ∉ (((Class.cv (nb090AlphaDummy548 h))).fv) := by
  simpa only [nb090AlphaDummy556] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy548 h))).fv) 1

theorem nb090_distinct_563 (h : Var) :
    (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy556 h) := by
  simpa only [nb090AlphaDummy555, nb090AlphaDummy556] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy548 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_564 (A : Class) :
    (nb090AlphaDummy559 A) ∉
      (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy559] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_565 (A : Class) :
    (nb090AlphaDummy560 A) ∉
      (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy560] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_566 (A : Class) :
    (nb090AlphaDummy561 A) ∉
      (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy561] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_567 (A : Class) :
    (nb090AlphaDummy559 A) ≠ (nb090AlphaDummy560 A) := by
  simpa only [nb090AlphaDummy559, nb090AlphaDummy560] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_568 (A : Class) :
    (nb090AlphaDummy559 A) ≠ (nb090AlphaDummy561 A) := by
  simpa only [nb090AlphaDummy559, nb090AlphaDummy561] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_569 (A : Class) :
    (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy561 A) := by
  simpa only [nb090AlphaDummy560, nb090AlphaDummy561] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_570 (h : Var) :
    (nb090AlphaDummy562 h) ∉
      (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy562] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_571 (h : Var) :
    (nb090AlphaDummy563 h) ∉
      (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy563] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_572 (h : Var) :
    (nb090AlphaDummy564 h) ∉
      (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy564] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_573 (h : Var) :
    (nb090AlphaDummy562 h) ≠ (nb090AlphaDummy563 h) := by
  simpa only [nb090AlphaDummy562, nb090AlphaDummy563] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_574 (h : Var) :
    (nb090AlphaDummy562 h) ≠ (nb090AlphaDummy564 h) := by
  simpa only [nb090AlphaDummy562, nb090AlphaDummy564] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_575 (h : Var) :
    (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy564 h) := by
  simpa only [nb090AlphaDummy563, nb090AlphaDummy564] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_576 (A : Class) :
    (nb090AlphaDummy571 A) ∉
      (((Class.cv (nb090AlphaDummy560 A))).fv ∪ ((Class.cv (nb090AlphaDummy560 A))).fv) :=
  by
  simpa only [nb090AlphaDummy571] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy560 A))).fv ∪ ((Class.cv (nb090AlphaDummy560 A))).fv)
      0

theorem nb090_fresh_577 (A : Class) :
    (nb090AlphaDummy567 A) ∉
      (((Class.cv (nb090AlphaDummy560 A))).fv ∪ ((Class.cv (nb090AlphaDummy561 A))).fv) :=
  by
  simpa only [nb090AlphaDummy567] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy560 A))).fv ∪ ((Class.cv (nb090AlphaDummy561 A))).fv)
      0

theorem nb090_fresh_578 (A : Class) :
    (nb090AlphaDummy573 A) ∉
      (((Class.cv (nb090AlphaDummy561 A))).fv ∪ ((Class.cv (nb090AlphaDummy561 A))).fv) :=
  by
  simpa only [nb090AlphaDummy573] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy561 A))).fv ∪ ((Class.cv (nb090AlphaDummy561 A))).fv)
      0

theorem nb090_fresh_579 (h : Var) :
    (nb090AlphaDummy572 h) ∉
      (((Class.cv (nb090AlphaDummy563 h))).fv ∪ ((Class.cv (nb090AlphaDummy563 h))).fv) :=
  by
  simpa only [nb090AlphaDummy572] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy563 h))).fv ∪ ((Class.cv (nb090AlphaDummy563 h))).fv)
      0

theorem nb090_fresh_580 (h : Var) :
    (nb090AlphaDummy568 h) ∉
      (((Class.cv (nb090AlphaDummy563 h))).fv ∪ ((Class.cv (nb090AlphaDummy564 h))).fv) :=
  by
  simpa only [nb090AlphaDummy568] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy563 h))).fv ∪ ((Class.cv (nb090AlphaDummy564 h))).fv)
      0

theorem nb090_fresh_581 (h : Var) :
    (nb090AlphaDummy574 h) ∉
      (((Class.cv (nb090AlphaDummy564 h))).fv ∪ ((Class.cv (nb090AlphaDummy564 h))).fv) :=
  by
  simpa only [nb090AlphaDummy574] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy564 h))).fv ∪ ((Class.cv (nb090AlphaDummy564 h))).fv)
      0

theorem nb090_fresh_582 (A : Class) :
    (nb090AlphaDummy589 A) ∉ (((Class.cv (nb090AlphaDummy582 A))).fv) := by
  simpa only [nb090AlphaDummy589] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy582 A))).fv) 0

theorem nb090_fresh_583 (A : Class) :
    (nb090AlphaDummy590 A) ∉ (((Class.cv (nb090AlphaDummy582 A))).fv) := by
  simpa only [nb090AlphaDummy590] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy582 A))).fv) 1

theorem nb090_distinct_584 (A : Class) :
    (nb090AlphaDummy589 A) ≠ (nb090AlphaDummy590 A) := by
  simpa only [nb090AlphaDummy589, nb090AlphaDummy590] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy582 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_585 (h : Var) :
    (nb090AlphaDummy591 h) ∉ (((Class.cv (nb090AlphaDummy584 h))).fv) := by
  simpa only [nb090AlphaDummy591] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy584 h))).fv) 0

theorem nb090_fresh_586 (h : Var) :
    (nb090AlphaDummy592 h) ∉ (((Class.cv (nb090AlphaDummy584 h))).fv) := by
  simpa only [nb090AlphaDummy592] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy584 h))).fv) 1

theorem nb090_distinct_587 (h : Var) :
    (nb090AlphaDummy591 h) ≠ (nb090AlphaDummy592 h) := by
  simpa only [nb090AlphaDummy591, nb090AlphaDummy592] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy584 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_588 (A : Class) :
    (nb090AlphaDummy595 A) ∉
      (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy595] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_589 (A : Class) :
    (nb090AlphaDummy596 A) ∉
      (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy596] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_590 (A : Class) :
    (nb090AlphaDummy597 A) ∉
      (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy597] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_591 (A : Class) :
    (nb090AlphaDummy595 A) ≠ (nb090AlphaDummy596 A) := by
  simpa only [nb090AlphaDummy595, nb090AlphaDummy596] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_592 (A : Class) :
    (nb090AlphaDummy595 A) ≠ (nb090AlphaDummy597 A) := by
  simpa only [nb090AlphaDummy595, nb090AlphaDummy597] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_593 (A : Class) :
    (nb090AlphaDummy596 A) ≠ (nb090AlphaDummy597 A) := by
  simpa only [nb090AlphaDummy596, nb090AlphaDummy597] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_594 (h : Var) :
    (nb090AlphaDummy598 h) ∉
      (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy598] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_595 (h : Var) :
    (nb090AlphaDummy599 h) ∉
      (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy599] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_596 (h : Var) :
    (nb090AlphaDummy600 h) ∉
      (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy600] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_597 (h : Var) :
    (nb090AlphaDummy598 h) ≠ (nb090AlphaDummy599 h) := by
  simpa only [nb090AlphaDummy598, nb090AlphaDummy599] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_598 (h : Var) :
    (nb090AlphaDummy598 h) ≠ (nb090AlphaDummy600 h) := by
  simpa only [nb090AlphaDummy598, nb090AlphaDummy600] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_599 (h : Var) :
    (nb090AlphaDummy599 h) ≠ (nb090AlphaDummy600 h) := by
  simpa only [nb090AlphaDummy599, nb090AlphaDummy600] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_600 (A : Class) :
    (nb090AlphaDummy607 A) ∉
      (((Class.cv (nb090AlphaDummy596 A))).fv ∪ ((Class.cv (nb090AlphaDummy596 A))).fv) :=
  by
  simpa only [nb090AlphaDummy607] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy596 A))).fv ∪ ((Class.cv (nb090AlphaDummy596 A))).fv)
      0

theorem nb090_fresh_601 (A : Class) :
    (nb090AlphaDummy603 A) ∉
      (((Class.cv (nb090AlphaDummy596 A))).fv ∪ ((Class.cv (nb090AlphaDummy597 A))).fv) :=
  by
  simpa only [nb090AlphaDummy603] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy596 A))).fv ∪ ((Class.cv (nb090AlphaDummy597 A))).fv)
      0

theorem nb090_fresh_602 (A : Class) :
    (nb090AlphaDummy609 A) ∉
      (((Class.cv (nb090AlphaDummy597 A))).fv ∪ ((Class.cv (nb090AlphaDummy597 A))).fv) :=
  by
  simpa only [nb090AlphaDummy609] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy597 A))).fv ∪ ((Class.cv (nb090AlphaDummy597 A))).fv)
      0

theorem nb090_fresh_603 (h : Var) :
    (nb090AlphaDummy608 h) ∉
      (((Class.cv (nb090AlphaDummy599 h))).fv ∪ ((Class.cv (nb090AlphaDummy599 h))).fv) :=
  by
  simpa only [nb090AlphaDummy608] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy599 h))).fv ∪ ((Class.cv (nb090AlphaDummy599 h))).fv)
      0

theorem nb090_fresh_604 (h : Var) :
    (nb090AlphaDummy604 h) ∉
      (((Class.cv (nb090AlphaDummy599 h))).fv ∪ ((Class.cv (nb090AlphaDummy600 h))).fv) :=
  by
  simpa only [nb090AlphaDummy604] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy599 h))).fv ∪ ((Class.cv (nb090AlphaDummy600 h))).fv)
      0

theorem nb090_fresh_605 (h : Var) :
    (nb090AlphaDummy610 h) ∉
      (((Class.cv (nb090AlphaDummy600 h))).fv ∪ ((Class.cv (nb090AlphaDummy600 h))).fv) :=
  by
  simpa only [nb090AlphaDummy610] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy600 h))).fv ∪ ((Class.cv (nb090AlphaDummy600 h))).fv)
      0

theorem nb090_fresh_606 (A : Class) :
    (nb090AlphaDummy625 A) ∉ (((Class.cv (nb090AlphaDummy618 A))).fv) := by
  simpa only [nb090AlphaDummy625] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy618 A))).fv) 0

theorem nb090_fresh_607 (A : Class) :
    (nb090AlphaDummy626 A) ∉ (((Class.cv (nb090AlphaDummy618 A))).fv) := by
  simpa only [nb090AlphaDummy626] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy618 A))).fv) 1

theorem nb090_distinct_608 (A : Class) :
    (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy626 A) := by
  simpa only [nb090AlphaDummy625, nb090AlphaDummy626] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy618 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_609 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy627 v u h) ∉ (((Class.cv (nb090AlphaDummy620 v u h))).fv) := by
  simpa only [nb090AlphaDummy627] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy620 v u h))).fv) 0

theorem nb090_fresh_610 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy628 v u h) ∉ (((Class.cv (nb090AlphaDummy620 v u h))).fv) := by
  simpa only [nb090AlphaDummy628] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy620 v u h))).fv) 1

theorem nb090_distinct_611 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy627 v u h) ≠ (nb090AlphaDummy628 v u h) := by
  simpa only [nb090AlphaDummy627, nb090AlphaDummy628] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy620 v u h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_612 (A : Class) :
    (nb090AlphaDummy631 A) ∉
      (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy631] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_613 (A : Class) :
    (nb090AlphaDummy632 A) ∉
      (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy632] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_614 (A : Class) :
    (nb090AlphaDummy633 A) ∉
      (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy633] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_615 (A : Class) :
    (nb090AlphaDummy631 A) ≠ (nb090AlphaDummy632 A) := by
  simpa only [nb090AlphaDummy631, nb090AlphaDummy632] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_616 (A : Class) :
    (nb090AlphaDummy631 A) ≠ (nb090AlphaDummy633 A) := by
  simpa only [nb090AlphaDummy631, nb090AlphaDummy633] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_617 (A : Class) :
    (nb090AlphaDummy632 A) ≠ (nb090AlphaDummy633 A) := by
  simpa only [nb090AlphaDummy632, nb090AlphaDummy633] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_618 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy634 v u h) ∉
      (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy634] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_619 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy635 v u h) ∉
      (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy635] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_620 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy636 v u h) ∉
      (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy636] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_621 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy634 v u h) ≠ (nb090AlphaDummy635 v u h) := by
  simpa only [nb090AlphaDummy634, nb090AlphaDummy635] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_622 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy634 v u h) ≠ (nb090AlphaDummy636 v u h) := by
  simpa only [nb090AlphaDummy634, nb090AlphaDummy636] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_623 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy636 v u h) := by
  simpa only [nb090AlphaDummy635, nb090AlphaDummy636] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_624 (A : Class) :
    (nb090AlphaDummy643 A) ∉
      (((Class.cv (nb090AlphaDummy632 A))).fv ∪ ((Class.cv (nb090AlphaDummy632 A))).fv) :=
  by
  simpa only [nb090AlphaDummy643] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy632 A))).fv ∪ ((Class.cv (nb090AlphaDummy632 A))).fv)
      0

theorem nb090_fresh_625 (A : Class) :
    (nb090AlphaDummy639 A) ∉
      (((Class.cv (nb090AlphaDummy632 A))).fv ∪ ((Class.cv (nb090AlphaDummy633 A))).fv) :=
  by
  simpa only [nb090AlphaDummy639] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy632 A))).fv ∪ ((Class.cv (nb090AlphaDummy633 A))).fv)
      0

theorem nb090_fresh_626 (A : Class) :
    (nb090AlphaDummy645 A) ∉
      (((Class.cv (nb090AlphaDummy633 A))).fv ∪ ((Class.cv (nb090AlphaDummy633 A))).fv) :=
  by
  simpa only [nb090AlphaDummy645] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy633 A))).fv ∪ ((Class.cv (nb090AlphaDummy633 A))).fv)
      0

theorem nb090_fresh_627 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy644 v u h) ∉
      (((Class.cv (nb090AlphaDummy635 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy635 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy644] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy635 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy635 v u h))).fv)
      0

theorem nb090_fresh_628 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy640 v u h) ∉
      (((Class.cv (nb090AlphaDummy635 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy636 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy640] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy635 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy636 v u h))).fv)
      0

theorem nb090_fresh_629 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy646 v u h) ∉
      (((Class.cv (nb090AlphaDummy636 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy636 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy646] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy636 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy636 v u h))).fv)
      0

theorem nb090_fresh_630 (A : Class) :
    (nb090AlphaDummy697 A) ∉ (((Class.cv (nb090AlphaDummy655 A))).fv) := by
  simpa only [nb090AlphaDummy697] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy655 A))).fv) 0

theorem nb090_fresh_631 (u : Var) :
    (nb090AlphaDummy698 u) ∉ (((Class.cv (nb090AlphaDummy656 u))).fv) := by
  simpa only [nb090AlphaDummy698] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy656 u))).fv) 0

theorem nb090_fresh_632 (A : Class) :
    (nb090AlphaDummy669 A) ∉ (((Class.cv (nb090AlphaDummy662 A))).fv) := by
  simpa only [nb090AlphaDummy669] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy662 A))).fv) 0

theorem nb090_fresh_633 (A : Class) :
    (nb090AlphaDummy670 A) ∉ (((Class.cv (nb090AlphaDummy662 A))).fv) := by
  simpa only [nb090AlphaDummy670] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy662 A))).fv) 1

theorem nb090_distinct_634 (A : Class) :
    (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy670 A) := by
  simpa only [nb090AlphaDummy669, nb090AlphaDummy670] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy662 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_635 (u : Var) :
    (nb090AlphaDummy671 u) ∉ (((Class.cv (nb090AlphaDummy664 u))).fv) := by
  simpa only [nb090AlphaDummy671] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy664 u))).fv) 0

theorem nb090_fresh_636 (u : Var) :
    (nb090AlphaDummy672 u) ∉ (((Class.cv (nb090AlphaDummy664 u))).fv) := by
  simpa only [nb090AlphaDummy672] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy664 u))).fv) 1

theorem nb090_distinct_637 (u : Var) :
    (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy672 u) := by
  simpa only [nb090AlphaDummy671, nb090AlphaDummy672] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy664 u))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_638 (A : Class) :
    (nb090AlphaDummy675 A) ∉
      (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy675] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_639 (A : Class) :
    (nb090AlphaDummy676 A) ∉
      (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy676] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_640 (A : Class) :
    (nb090AlphaDummy677 A) ∉
      (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy677] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_641 (A : Class) :
    (nb090AlphaDummy675 A) ≠ (nb090AlphaDummy676 A) := by
  simpa only [nb090AlphaDummy675, nb090AlphaDummy676] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_642 (A : Class) :
    (nb090AlphaDummy675 A) ≠ (nb090AlphaDummy677 A) := by
  simpa only [nb090AlphaDummy675, nb090AlphaDummy677] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_643 (A : Class) :
    (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy677 A) := by
  simpa only [nb090AlphaDummy676, nb090AlphaDummy677] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_644 (u : Var) :
    (nb090AlphaDummy678 u) ∉
      (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy678] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_645 (u : Var) :
    (nb090AlphaDummy679 u) ∉
      (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy679] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_646 (u : Var) :
    (nb090AlphaDummy680 u) ∉
      (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy680] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_647 (u : Var) :
    (nb090AlphaDummy678 u) ≠ (nb090AlphaDummy679 u) := by
  simpa only [nb090AlphaDummy678, nb090AlphaDummy679] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_648 (u : Var) :
    (nb090AlphaDummy678 u) ≠ (nb090AlphaDummy680 u) := by
  simpa only [nb090AlphaDummy678, nb090AlphaDummy680] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_649 (u : Var) :
    (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy680 u) := by
  simpa only [nb090AlphaDummy679, nb090AlphaDummy680] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_650 (A : Class) :
    (nb090AlphaDummy687 A) ∉
      (((Class.cv (nb090AlphaDummy676 A))).fv ∪ ((Class.cv (nb090AlphaDummy676 A))).fv) :=
  by
  simpa only [nb090AlphaDummy687] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy676 A))).fv ∪ ((Class.cv (nb090AlphaDummy676 A))).fv)
      0

theorem nb090_fresh_651 (A : Class) :
    (nb090AlphaDummy683 A) ∉
      (((Class.cv (nb090AlphaDummy676 A))).fv ∪ ((Class.cv (nb090AlphaDummy677 A))).fv) :=
  by
  simpa only [nb090AlphaDummy683] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy676 A))).fv ∪ ((Class.cv (nb090AlphaDummy677 A))).fv)
      0

theorem nb090_fresh_652 (A : Class) :
    (nb090AlphaDummy689 A) ∉
      (((Class.cv (nb090AlphaDummy677 A))).fv ∪ ((Class.cv (nb090AlphaDummy677 A))).fv) :=
  by
  simpa only [nb090AlphaDummy689] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy677 A))).fv ∪ ((Class.cv (nb090AlphaDummy677 A))).fv)
      0

theorem nb090_fresh_653 (u : Var) :
    (nb090AlphaDummy688 u) ∉
      (((Class.cv (nb090AlphaDummy679 u))).fv ∪ ((Class.cv (nb090AlphaDummy679 u))).fv) :=
  by
  simpa only [nb090AlphaDummy688] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy679 u))).fv ∪ ((Class.cv (nb090AlphaDummy679 u))).fv)
      0

theorem nb090_fresh_654 (u : Var) :
    (nb090AlphaDummy684 u) ∉
      (((Class.cv (nb090AlphaDummy679 u))).fv ∪ ((Class.cv (nb090AlphaDummy680 u))).fv) :=
  by
  simpa only [nb090AlphaDummy684] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy679 u))).fv ∪ ((Class.cv (nb090AlphaDummy680 u))).fv)
      0

theorem nb090_fresh_655 (u : Var) :
    (nb090AlphaDummy690 u) ∉
      (((Class.cv (nb090AlphaDummy680 u))).fv ∪ ((Class.cv (nb090AlphaDummy680 u))).fv) :=
  by
  simpa only [nb090AlphaDummy690] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy680 u))).fv ∪ ((Class.cv (nb090AlphaDummy680 u))).fv)
      0

theorem nb090_fresh_656 (A : Class) :
    (nb090AlphaDummy753 A) ∉ (((Class.cv (nb090AlphaDummy700 A))).fv) := by
  simpa only [nb090AlphaDummy753] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy700 A))).fv) 0

theorem nb090_fresh_657 (A : Class) :
    (nb090AlphaDummy754 A) ∉ (((Class.cv (nb090AlphaDummy700 A))).fv) := by
  simpa only [nb090AlphaDummy754] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy700 A))).fv) 1

theorem nb090_distinct_658 (A : Class) :
    (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy754 A) := by
  simpa only [nb090AlphaDummy753, nb090AlphaDummy754] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy700 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_659 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy755 v u h) ∉ (((Class.cv (nb090AlphaDummy702 v u h))).fv) := by
  simpa only [nb090AlphaDummy755] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy702 v u h))).fv) 0

theorem nb090_fresh_660 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy756 v u h) ∉ (((Class.cv (nb090AlphaDummy702 v u h))).fv) := by
  simpa only [nb090AlphaDummy756] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy702 v u h))).fv) 1

theorem nb090_distinct_661 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy755 v u h) ≠ (nb090AlphaDummy756 v u h) := by
  simpa only [nb090AlphaDummy755, nb090AlphaDummy756] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy702 v u h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_662 (A : Class) :
    (nb090AlphaDummy751 A) ∉ (((Class.cv (nb090AlphaDummy709 A))).fv) := by
  simpa only [nb090AlphaDummy751] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy709 A))).fv) 0

theorem nb090_fresh_663 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy752 v u h) ∉ (((Class.cv (nb090AlphaDummy710 v u h))).fv) := by
  simpa only [nb090AlphaDummy752] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy710 v u h))).fv) 0

theorem nb090_fresh_664 (A : Class) :
    (nb090AlphaDummy723 A) ∉ (((Class.cv (nb090AlphaDummy716 A))).fv) := by
  simpa only [nb090AlphaDummy723] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy716 A))).fv) 0

theorem nb090_fresh_665 (A : Class) :
    (nb090AlphaDummy724 A) ∉ (((Class.cv (nb090AlphaDummy716 A))).fv) := by
  simpa only [nb090AlphaDummy724] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy716 A))).fv) 1

theorem nb090_distinct_666 (A : Class) :
    (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy724 A) := by
  simpa only [nb090AlphaDummy723, nb090AlphaDummy724] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy716 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_667 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy725 v u h) ∉ (((Class.cv (nb090AlphaDummy718 v u h))).fv) := by
  simpa only [nb090AlphaDummy725] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy718 v u h))).fv) 0

theorem nb090_fresh_668 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy726 v u h) ∉ (((Class.cv (nb090AlphaDummy718 v u h))).fv) := by
  simpa only [nb090AlphaDummy726] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy718 v u h))).fv) 1

theorem nb090_distinct_669 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy725 v u h) ≠ (nb090AlphaDummy726 v u h) := by
  simpa only [nb090AlphaDummy725, nb090AlphaDummy726] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy718 v u h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_670 (A : Class) :
    (nb090AlphaDummy729 A) ∉
      (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy729] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_671 (A : Class) :
    (nb090AlphaDummy730 A) ∉
      (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy730] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_672 (A : Class) :
    (nb090AlphaDummy731 A) ∉
      (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy731] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_673 (A : Class) :
    (nb090AlphaDummy729 A) ≠ (nb090AlphaDummy730 A) := by
  simpa only [nb090AlphaDummy729, nb090AlphaDummy730] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_674 (A : Class) :
    (nb090AlphaDummy729 A) ≠ (nb090AlphaDummy731 A) := by
  simpa only [nb090AlphaDummy729, nb090AlphaDummy731] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_675 (A : Class) :
    (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy731 A) := by
  simpa only [nb090AlphaDummy730, nb090AlphaDummy731] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_676 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy732 v u h) ∉
      (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy732] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_677 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy733 v u h) ∉
      (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy733] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_678 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy734 v u h) ∉
      (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy734] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_679 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy732 v u h) ≠ (nb090AlphaDummy733 v u h) := by
  simpa only [nb090AlphaDummy732, nb090AlphaDummy733] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_680 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy732 v u h) ≠ (nb090AlphaDummy734 v u h) := by
  simpa only [nb090AlphaDummy732, nb090AlphaDummy734] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_681 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy734 v u h) := by
  simpa only [nb090AlphaDummy733, nb090AlphaDummy734] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_682 (A : Class) :
    (nb090AlphaDummy741 A) ∉
      (((Class.cv (nb090AlphaDummy730 A))).fv ∪ ((Class.cv (nb090AlphaDummy730 A))).fv) :=
  by
  simpa only [nb090AlphaDummy741] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy730 A))).fv ∪ ((Class.cv (nb090AlphaDummy730 A))).fv)
      0

theorem nb090_fresh_683 (A : Class) :
    (nb090AlphaDummy737 A) ∉
      (((Class.cv (nb090AlphaDummy730 A))).fv ∪ ((Class.cv (nb090AlphaDummy731 A))).fv) :=
  by
  simpa only [nb090AlphaDummy737] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy730 A))).fv ∪ ((Class.cv (nb090AlphaDummy731 A))).fv)
      0

theorem nb090_fresh_684 (A : Class) :
    (nb090AlphaDummy743 A) ∉
      (((Class.cv (nb090AlphaDummy731 A))).fv ∪ ((Class.cv (nb090AlphaDummy731 A))).fv) :=
  by
  simpa only [nb090AlphaDummy743] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy731 A))).fv ∪ ((Class.cv (nb090AlphaDummy731 A))).fv)
      0

theorem nb090_fresh_685 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy742 v u h) ∉
      (((Class.cv (nb090AlphaDummy733 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy733 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy742] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy733 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy733 v u h))).fv)
      0

theorem nb090_fresh_686 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy738 v u h) ∉
      (((Class.cv (nb090AlphaDummy733 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy734 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy738] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy733 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy734 v u h))).fv)
      0

theorem nb090_fresh_687 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy744 v u h) ∉
      (((Class.cv (nb090AlphaDummy734 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy734 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy744] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy734 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy734 v u h))).fv)
      0

theorem nb090_fresh_688 (A : Class) :
    (nb090AlphaDummy759 A) ∉
      (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy759] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_689 (A : Class) :
    (nb090AlphaDummy760 A) ∉
      (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy760] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_690 (A : Class) :
    (nb090AlphaDummy761 A) ∉
      (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy761] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_691 (A : Class) :
    (nb090AlphaDummy759 A) ≠ (nb090AlphaDummy760 A) := by
  simpa only [nb090AlphaDummy759, nb090AlphaDummy760] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part012`. -/


section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb090_distinct_692 (A : Class) :
    (nb090AlphaDummy759 A) ≠ (nb090AlphaDummy761 A) := by
  simpa only [nb090AlphaDummy759, nb090AlphaDummy761] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_693 (A : Class) :
    (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy761 A) := by
  simpa only [nb090AlphaDummy760, nb090AlphaDummy761] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_694 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy762 v u h) ∉
      (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy762] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_695 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy763 v u h) ∉
      (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy763] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_696 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy764 v u h) ∉
      (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy764] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_697 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy762 v u h) ≠ (nb090AlphaDummy763 v u h) := by
  simpa only [nb090AlphaDummy762, nb090AlphaDummy763] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_698 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy762 v u h) ≠ (nb090AlphaDummy764 v u h) := by
  simpa only [nb090AlphaDummy762, nb090AlphaDummy764] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_699 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy764 v u h) := by
  simpa only [nb090AlphaDummy763, nb090AlphaDummy764] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_700 (A : Class) :
    (nb090AlphaDummy771 A) ∉
      (((Class.cv (nb090AlphaDummy760 A))).fv ∪ ((Class.cv (nb090AlphaDummy760 A))).fv) :=
  by
  simpa only [nb090AlphaDummy771] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy760 A))).fv ∪ ((Class.cv (nb090AlphaDummy760 A))).fv)
      0

theorem nb090_fresh_701 (A : Class) :
    (nb090AlphaDummy767 A) ∉
      (((Class.cv (nb090AlphaDummy760 A))).fv ∪ ((Class.cv (nb090AlphaDummy761 A))).fv) :=
  by
  simpa only [nb090AlphaDummy767] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy760 A))).fv ∪ ((Class.cv (nb090AlphaDummy761 A))).fv)
      0

theorem nb090_fresh_702 (A : Class) :
    (nb090AlphaDummy773 A) ∉
      (((Class.cv (nb090AlphaDummy761 A))).fv ∪ ((Class.cv (nb090AlphaDummy761 A))).fv) :=
  by
  simpa only [nb090AlphaDummy773] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy761 A))).fv ∪ ((Class.cv (nb090AlphaDummy761 A))).fv)
      0

theorem nb090_fresh_703 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy772 v u h) ∉
      (((Class.cv (nb090AlphaDummy763 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy763 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy772] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy763 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy763 v u h))).fv)
      0

theorem nb090_fresh_704 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy768 v u h) ∉
      (((Class.cv (nb090AlphaDummy763 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy764 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy768] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy763 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy764 v u h))).fv)
      0

theorem nb090_fresh_705 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy774 v u h) ∉
      (((Class.cv (nb090AlphaDummy764 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy764 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy774] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy764 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy764 v u h))).fv)
      0

theorem nb090_fresh_706 (A : Class) :
    (nb090AlphaDummy821 A) ∉ (((Class.cv (nb090AlphaDummy779 A))).fv) := by
  simpa only [nb090AlphaDummy821] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy779 A))).fv) 0

theorem nb090_fresh_707 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy822 v u h) ∉ (((Class.cv (nb090AlphaDummy780 v u h))).fv) := by
  simpa only [nb090AlphaDummy822] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy780 v u h))).fv) 0

theorem nb090_fresh_708 (A : Class) :
    (nb090AlphaDummy793 A) ∉ (((Class.cv (nb090AlphaDummy786 A))).fv) := by
  simpa only [nb090AlphaDummy793] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy786 A))).fv) 0

theorem nb090_fresh_709 (A : Class) :
    (nb090AlphaDummy794 A) ∉ (((Class.cv (nb090AlphaDummy786 A))).fv) := by
  simpa only [nb090AlphaDummy794] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy786 A))).fv) 1

theorem nb090_distinct_710 (A : Class) :
    (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy794 A) := by
  simpa only [nb090AlphaDummy793, nb090AlphaDummy794] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy786 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_711 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy795 v u h) ∉ (((Class.cv (nb090AlphaDummy788 v u h))).fv) := by
  simpa only [nb090AlphaDummy795] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy788 v u h))).fv) 0

theorem nb090_fresh_712 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy796 v u h) ∉ (((Class.cv (nb090AlphaDummy788 v u h))).fv) := by
  simpa only [nb090AlphaDummy796] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy788 v u h))).fv) 1

theorem nb090_distinct_713 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy795 v u h) ≠ (nb090AlphaDummy796 v u h) := by
  simpa only [nb090AlphaDummy795, nb090AlphaDummy796] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy788 v u h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_714 (A : Class) :
    (nb090AlphaDummy799 A) ∉
      (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy799] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_715 (A : Class) :
    (nb090AlphaDummy800 A) ∉
      (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy800] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_716 (A : Class) :
    (nb090AlphaDummy801 A) ∉
      (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy801] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_717 (A : Class) :
    (nb090AlphaDummy799 A) ≠ (nb090AlphaDummy800 A) := by
  simpa only [nb090AlphaDummy799, nb090AlphaDummy800] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_718 (A : Class) :
    (nb090AlphaDummy799 A) ≠ (nb090AlphaDummy801 A) := by
  simpa only [nb090AlphaDummy799, nb090AlphaDummy801] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_719 (A : Class) :
    (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy801 A) := by
  simpa only [nb090AlphaDummy800, nb090AlphaDummy801] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_720 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy802 v u h) ∉
      (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy802] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_721 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy803 v u h) ∉
      (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy803] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_722 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy804 v u h) ∉
      (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy804] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_723 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy802 v u h) ≠ (nb090AlphaDummy803 v u h) := by
  simpa only [nb090AlphaDummy802, nb090AlphaDummy803] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_724 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy802 v u h) ≠ (nb090AlphaDummy804 v u h) := by
  simpa only [nb090AlphaDummy802, nb090AlphaDummy804] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_725 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy804 v u h) := by
  simpa only [nb090AlphaDummy803, nb090AlphaDummy804] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_726 (A : Class) :
    (nb090AlphaDummy811 A) ∉
      (((Class.cv (nb090AlphaDummy800 A))).fv ∪ ((Class.cv (nb090AlphaDummy800 A))).fv) :=
  by
  simpa only [nb090AlphaDummy811] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy800 A))).fv ∪ ((Class.cv (nb090AlphaDummy800 A))).fv)
      0

theorem nb090_fresh_727 (A : Class) :
    (nb090AlphaDummy807 A) ∉
      (((Class.cv (nb090AlphaDummy800 A))).fv ∪ ((Class.cv (nb090AlphaDummy801 A))).fv) :=
  by
  simpa only [nb090AlphaDummy807] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy800 A))).fv ∪ ((Class.cv (nb090AlphaDummy801 A))).fv)
      0

theorem nb090_fresh_728 (A : Class) :
    (nb090AlphaDummy813 A) ∉
      (((Class.cv (nb090AlphaDummy801 A))).fv ∪ ((Class.cv (nb090AlphaDummy801 A))).fv) :=
  by
  simpa only [nb090AlphaDummy813] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy801 A))).fv ∪ ((Class.cv (nb090AlphaDummy801 A))).fv)
      0

theorem nb090_fresh_729 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy812 v u h) ∉
      (((Class.cv (nb090AlphaDummy803 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy803 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy812] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy803 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy803 v u h))).fv)
      0

theorem nb090_fresh_730 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy808 v u h) ∉
      (((Class.cv (nb090AlphaDummy803 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy804 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy808] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy803 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy804 v u h))).fv)
      0

theorem nb090_fresh_731 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy814 v u h) ∉
      (((Class.cv (nb090AlphaDummy804 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy804 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy814] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy804 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy804 v u h))).fv)
      0

theorem nb090_fresh_732 (A : Class) :
    (nb090AlphaDummy871 A) ∉ (((Class.cv (nb090AlphaDummy829 A))).fv) := by
  simpa only [nb090AlphaDummy871] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy829 A))).fv) 0

theorem nb090_fresh_733 (v : Var) :
    (nb090AlphaDummy872 v) ∉ (((Class.cv (nb090AlphaDummy830 v))).fv) := by
  simpa only [nb090AlphaDummy872] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy830 v))).fv) 0

theorem nb090_fresh_734 (A : Class) :
    (nb090AlphaDummy843 A) ∉ (((Class.cv (nb090AlphaDummy836 A))).fv) := by
  simpa only [nb090AlphaDummy843] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy836 A))).fv) 0

theorem nb090_fresh_735 (A : Class) :
    (nb090AlphaDummy844 A) ∉ (((Class.cv (nb090AlphaDummy836 A))).fv) := by
  simpa only [nb090AlphaDummy844] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy836 A))).fv) 1

theorem nb090_distinct_736 (A : Class) :
    (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy844 A) := by
  simpa only [nb090AlphaDummy843, nb090AlphaDummy844] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy836 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_737 (v : Var) :
    (nb090AlphaDummy845 v) ∉ (((Class.cv (nb090AlphaDummy838 v))).fv) := by
  simpa only [nb090AlphaDummy845] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy838 v))).fv) 0

theorem nb090_fresh_738 (v : Var) :
    (nb090AlphaDummy846 v) ∉ (((Class.cv (nb090AlphaDummy838 v))).fv) := by
  simpa only [nb090AlphaDummy846] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy838 v))).fv) 1

theorem nb090_distinct_739 (v : Var) :
    (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy846 v) := by
  simpa only [nb090AlphaDummy845, nb090AlphaDummy846] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy838 v))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_740 (A : Class) :
    (nb090AlphaDummy849 A) ∉
      (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy849] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_741 (A : Class) :
    (nb090AlphaDummy850 A) ∉
      (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy850] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_742 (A : Class) :
    (nb090AlphaDummy851 A) ∉
      (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy851] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_743 (A : Class) :
    (nb090AlphaDummy849 A) ≠ (nb090AlphaDummy850 A) := by
  simpa only [nb090AlphaDummy849, nb090AlphaDummy850] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_744 (A : Class) :
    (nb090AlphaDummy849 A) ≠ (nb090AlphaDummy851 A) := by
  simpa only [nb090AlphaDummy849, nb090AlphaDummy851] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_745 (A : Class) :
    (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy851 A) := by
  simpa only [nb090AlphaDummy850, nb090AlphaDummy851] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_746 (v : Var) :
    (nb090AlphaDummy852 v) ∉
      (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy852] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_747 (v : Var) :
    (nb090AlphaDummy853 v) ∉
      (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy853] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_748 (v : Var) :
    (nb090AlphaDummy854 v) ∉
      (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy854] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_749 (v : Var) :
    (nb090AlphaDummy852 v) ≠ (nb090AlphaDummy853 v) := by
  simpa only [nb090AlphaDummy852, nb090AlphaDummy853] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_750 (v : Var) :
    (nb090AlphaDummy852 v) ≠ (nb090AlphaDummy854 v) := by
  simpa only [nb090AlphaDummy852, nb090AlphaDummy854] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_751 (v : Var) :
    (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy854 v) := by
  simpa only [nb090AlphaDummy853, nb090AlphaDummy854] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_752 (A : Class) :
    (nb090AlphaDummy861 A) ∉
      (((Class.cv (nb090AlphaDummy850 A))).fv ∪ ((Class.cv (nb090AlphaDummy850 A))).fv) :=
  by
  simpa only [nb090AlphaDummy861] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy850 A))).fv ∪ ((Class.cv (nb090AlphaDummy850 A))).fv)
      0

theorem nb090_fresh_753 (A : Class) :
    (nb090AlphaDummy857 A) ∉
      (((Class.cv (nb090AlphaDummy850 A))).fv ∪ ((Class.cv (nb090AlphaDummy851 A))).fv) :=
  by
  simpa only [nb090AlphaDummy857] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy850 A))).fv ∪ ((Class.cv (nb090AlphaDummy851 A))).fv)
      0

theorem nb090_fresh_754 (A : Class) :
    (nb090AlphaDummy863 A) ∉
      (((Class.cv (nb090AlphaDummy851 A))).fv ∪ ((Class.cv (nb090AlphaDummy851 A))).fv) :=
  by
  simpa only [nb090AlphaDummy863] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy851 A))).fv ∪ ((Class.cv (nb090AlphaDummy851 A))).fv)
      0

theorem nb090_fresh_755 (v : Var) :
    (nb090AlphaDummy862 v) ∉
      (((Class.cv (nb090AlphaDummy853 v))).fv ∪ ((Class.cv (nb090AlphaDummy853 v))).fv) :=
  by
  simpa only [nb090AlphaDummy862] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy853 v))).fv ∪ ((Class.cv (nb090AlphaDummy853 v))).fv)
      0

theorem nb090_fresh_756 (v : Var) :
    (nb090AlphaDummy858 v) ∉
      (((Class.cv (nb090AlphaDummy853 v))).fv ∪ ((Class.cv (nb090AlphaDummy854 v))).fv) :=
  by
  simpa only [nb090AlphaDummy858] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy853 v))).fv ∪ ((Class.cv (nb090AlphaDummy854 v))).fv)
      0

theorem nb090_fresh_757 (v : Var) :
    (nb090AlphaDummy864 v) ∉
      (((Class.cv (nb090AlphaDummy854 v))).fv ∪ ((Class.cv (nb090AlphaDummy854 v))).fv) :=
  by
  simpa only [nb090AlphaDummy864] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy854 v))).fv ∪ ((Class.cv (nb090AlphaDummy854 v))).fv)
      0

theorem nb090_fresh_758 (h : Var) : (nb090AlphaDummy131 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb090AlphaDummy131] using freshVar_not_mem (((Class.cv h)).fv) 0

theorem nb090_fresh_759 (h : Var) : (nb090AlphaDummy132 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb090AlphaDummy132] using freshVar_not_mem (((Class.cv h)).fv) 1

theorem nb090_distinct_760 (h : Var) :
    (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy132 h) := by
  simpa only [nb090AlphaDummy131, nb090AlphaDummy132] using
    (freshVar_injective (((Class.cv h)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_761 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy708 v u h) ∉
      (((Class.cv h)).fv ∪ ((Class.cv (nb090AlphaDummy043 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy708] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((Class.cv (nb090AlphaDummy043 v u h))).fv) 0

theorem nb090_fresh_762 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy778 v u h) ∉
      (((Class.cv h)).fv ∪ ((Class.cv (nb090AlphaDummy044 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy778] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((Class.cv (nb090AlphaDummy044 v u h))).fv) 0

theorem nb090_fresh_763 (h : Var) :
    (nb090AlphaDummy052 h) ∉ (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) := by
  simpa only [nb090AlphaDummy052] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 0

theorem nb090_fresh_764 (h : Var) :
    (nb090AlphaDummy053 h) ∉ (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) := by
  simpa only [nb090AlphaDummy053] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 1

theorem nb090_fresh_765 (h : Var) :
    (nb090AlphaDummy054 h) ∉ (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) := by
  simpa only [nb090AlphaDummy054] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 2

theorem nb090_distinct_766 (h : Var) :
    (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy053 h) := by
  simpa only [nb090AlphaDummy052, nb090AlphaDummy053] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb090_distinct_767 (h : Var) :
    (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy054 h) := by
  simpa only [nb090AlphaDummy052, nb090AlphaDummy054] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb090_distinct_768 (h : Var) :
    (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy054 h) := by
  simpa only [nb090AlphaDummy053, nb090AlphaDummy054] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb090_fresh_769 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∉
      (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
            ((synCfv (synC1st) (Class.cv v))).fv ∪ ((synCfv (synC2nd) (Class.cv u))).fv ∪
        ((synCfv (synC2nd) (Class.cv v))).fv) :=
  by
  simpa only [nb090AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
            ((synCfv (synC1st) (Class.cv v))).fv ∪ ((synCfv (synC2nd) (Class.cv u))).fv ∪
        ((synCfv (synC2nd) (Class.cv v))).fv)
      0

theorem nb090_fresh_770 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∉
      (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
            ((synCfv (synC1st) (Class.cv v))).fv ∪ ((synCfv (synC2nd) (Class.cv u))).fv ∪
        ((synCfv (synC2nd) (Class.cv v))).fv) :=
  by
  simpa only [nb090AlphaDummy044] using
    freshVar_not_mem
      (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
            ((synCfv (synC1st) (Class.cv v))).fv ∪ ((synCfv (synC2nd) (Class.cv u))).fv ∪
        ((synCfv (synC2nd) (Class.cv v))).fv)
      1

theorem nb090_distinct_771 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy044 v u h) := by
  simpa only [nb090AlphaDummy043, nb090AlphaDummy044] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
            ((synCfv (synC1st) (Class.cv v))).fv ∪ ((synCfv (synC2nd) (Class.cv u))).fv ∪
        ((synCfv (synC2nd) (Class.cv v))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_772 (h : Var) :
    (nb090AlphaDummy335 h) ∉ (((Class.cv h)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb090AlphaDummy335] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((synCvv)).fv) 0

theorem nb090_fresh_773 (h : Var) :
    (nb090AlphaDummy336 h) ∉ (((Class.cv h)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb090AlphaDummy336] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((synCvv)).fv) 1

theorem nb090_distinct_774 (h : Var) :
    (nb090AlphaDummy335 h) ≠ (nb090AlphaDummy336 h) := by
  simpa only [nb090AlphaDummy335, nb090AlphaDummy336] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((synCvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_775 (u : Var) :
    (nb090AlphaDummy293 u) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) :=
  by
  simpa only [nb090AlphaDummy293] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) 0

theorem nb090_fresh_776 (u : Var) :
    (nb090AlphaDummy294 u) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) :=
  by
  simpa only [nb090AlphaDummy294] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) 1

theorem nb090_distinct_777 (u : Var) :
    (nb090AlphaDummy293 u) ≠ (nb090AlphaDummy294 u) := by
  simpa only [nb090AlphaDummy293, nb090AlphaDummy294] using
    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_778 (u : Var) :
    (nb090AlphaDummy663 u) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) :=
  by
  simpa only [nb090AlphaDummy663] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) 0

theorem nb090_fresh_779 (u : Var) :
    (nb090AlphaDummy664 u) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) :=
  by
  simpa only [nb090AlphaDummy664] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) 1

theorem nb090_distinct_780 (u : Var) :
    (nb090AlphaDummy663 u) ≠ (nb090AlphaDummy664 u) := by
  simpa only [nb090AlphaDummy663, nb090AlphaDummy664] using
    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_781 (v : Var) (u : Var) :
    (nb090AlphaDummy007 v u) ∉ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090AlphaDummy007] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 0

theorem nb090_fresh_782 (v : Var) (u : Var) :
    (nb090AlphaDummy008 v u) ∉ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090AlphaDummy008] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 1

theorem nb090_distinct_783 (v : Var) (u : Var) :
    (nb090AlphaDummy007 v u) ≠ (nb090AlphaDummy008 v u) := by
  simpa only [nb090AlphaDummy007, nb090AlphaDummy008] using
    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv v)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_784 (v : Var) :
    (nb090AlphaDummy383 v) ∉
      (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv) :=
  by
  simpa only [nb090AlphaDummy383] using
    freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv) 0

theorem nb090_fresh_785 (v : Var) :
    (nb090AlphaDummy384 v) ∉
      (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv) :=
  by
  simpa only [nb090AlphaDummy384] using
    freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv) 1

theorem nb090_distinct_786 (v : Var) :
    (nb090AlphaDummy383 v) ≠ (nb090AlphaDummy384 v) := by
  simpa only [nb090AlphaDummy383, nb090AlphaDummy384] using
    (freshVar_injective (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_787 (v : Var) :
    (nb090AlphaDummy837 v) ∉
      (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) :=
  by
  simpa only [nb090AlphaDummy837] using
    freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) 0

theorem nb090_fresh_788 (v : Var) :
    (nb090AlphaDummy838 v) ∉
      (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) :=
  by
  simpa only [nb090AlphaDummy838] using
    freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) 1

theorem nb090_distinct_789 (v : Var) :
    (nb090AlphaDummy837 v) ≠ (nb090AlphaDummy838 v) := by
  simpa only [nb090AlphaDummy837, nb090AlphaDummy838] using
    (freshVar_injective (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_790 (A : Class) :
    (nb090AlphaDummy017 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy013 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy013 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy013 A))).fv) :=
  by
  simpa only [nb090AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy013 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy013 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy013 A))).fv)
      0

theorem nb090_fresh_791 (v : Var) (u : Var) :
    (nb090AlphaDummy018 v u) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy015 v u)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy015 v u)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy015 v u))).fv) :=
  by
  simpa only [nb090AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy015 v u)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy015 v u)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy015 v u))).fv)
      0

theorem nb090_fresh_792 (A : Class) :
    (nb090AlphaDummy069 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy065 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy065 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy065 A))).fv) :=
  by
  simpa only [nb090AlphaDummy069] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy065 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy065 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy065 A))).fv)
      0

theorem nb090_fresh_793 (h : Var) :
    (nb090AlphaDummy070 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy067 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy067 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy067 h))).fv) :=
  by
  simpa only [nb090AlphaDummy070] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy067 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy067 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy067 h))).fv)
      0

theorem nb090_fresh_794 (A : Class) :
    (nb090AlphaDummy105 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy101 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy101 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy101 A))).fv) :=
  by
  simpa only [nb090AlphaDummy105] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy101 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy101 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy101 A))).fv)
      0

theorem nb090_fresh_795 (h : Var) :
    (nb090AlphaDummy106 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy103 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy103 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy103 h))).fv) :=
  by
  simpa only [nb090AlphaDummy106] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy103 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy103 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy103 h))).fv)
      0

theorem nb090_fresh_796 (A : Class) :
    (nb090AlphaDummy147 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy143 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy143 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy143 A))).fv) :=
  by
  simpa only [nb090AlphaDummy147] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy143 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy143 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy143 A))).fv)
      0

theorem nb090_fresh_797 (h : Var) :
    (nb090AlphaDummy148 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy145 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy145 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy145 h))).fv) :=
  by
  simpa only [nb090AlphaDummy148] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy145 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy145 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy145 h))).fv)
      0

theorem nb090_fresh_798 (A : Class) :
    (nb090AlphaDummy183 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy179 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy179 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy179 A))).fv) :=
  by
  simpa only [nb090AlphaDummy183] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy179 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy179 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy179 A))).fv)
      0

theorem nb090_fresh_799 (h : Var) :
    (nb090AlphaDummy184 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy181 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy181 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy181 h))).fv) :=
  by
  simpa only [nb090AlphaDummy184] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy181 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy181 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy181 h))).fv)
      0

theorem nb090_fresh_800 (A : Class) :
    (nb090AlphaDummy219 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy215 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy215 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy215 A))).fv) :=
  by
  simpa only [nb090AlphaDummy219] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy215 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy215 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy215 A))).fv)
      0

theorem nb090_fresh_801 (h : Var) :
    (nb090AlphaDummy220 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy217 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy217 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy217 h))).fv) :=
  by
  simpa only [nb090AlphaDummy220] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy217 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy217 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy217 h))).fv)
      0

theorem nb090_fresh_802 (A : Class) :
    (nb090AlphaDummy259 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy255 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy255 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy255 A))).fv) :=
  by
  simpa only [nb090AlphaDummy259] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy255 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy255 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy255 A))).fv)
      0

theorem nb090_fresh_803 (h : Var) :
    (nb090AlphaDummy260 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy257 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy257 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy257 h))).fv) :=
  by
  simpa only [nb090AlphaDummy260] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy257 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy257 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy257 h))).fv)
      0

theorem nb090_fresh_804 (A : Class) :
    (nb090AlphaDummy303 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy299 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy299 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy299 A))).fv) :=
  by
  simpa only [nb090AlphaDummy303] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy299 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy299 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy299 A))).fv)
      0

theorem nb090_fresh_805 (u : Var) :
    (nb090AlphaDummy304 u) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy301 u)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy301 u)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy301 u))).fv) :=
  by
  simpa only [nb090AlphaDummy304] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy301 u)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy301 u)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy301 u))).fv)
      0

theorem nb090_fresh_806 (A : Class) :
    (nb090AlphaDummy349 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy345 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy345 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy345 A))).fv) :=
  by
  simpa only [nb090AlphaDummy349] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy345 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy345 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy345 A))).fv)
      0

theorem nb090_fresh_807 (h : Var) :
    (nb090AlphaDummy350 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy347 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy347 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy347 h))).fv) :=
  by
  simpa only [nb090AlphaDummy350] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy347 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy347 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy347 h))).fv)
      0

theorem nb090_fresh_808 (A : Class) :
    (nb090AlphaDummy393 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy389 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy389 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy389 A))).fv) :=
  by
  simpa only [nb090AlphaDummy393] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy389 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy389 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy389 A))).fv)
      0

theorem nb090_fresh_809 (v : Var) :
    (nb090AlphaDummy394 v) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy391 v)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy391 v)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy391 v))).fv) :=
  by
  simpa only [nb090AlphaDummy394] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy391 v)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy391 v)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy391 v))).fv)
      0

theorem nb090_fresh_810 (A : Class) :
    (nb090AlphaDummy443 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy439 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy439 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy439 A))).fv) :=
  by
  simpa only [nb090AlphaDummy443] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy439 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy439 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy439 A))).fv)
      0

theorem nb090_fresh_811 (h : Var) :
    (nb090AlphaDummy444 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy441 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy441 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy441 h))).fv) :=
  by
  simpa only [nb090AlphaDummy444] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy441 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy441 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy441 h))).fv)
      0

theorem nb090_fresh_812 (A : Class) :
    (nb090AlphaDummy479 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy475 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy475 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy475 A))).fv) :=
  by
  simpa only [nb090AlphaDummy479] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy475 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy475 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy475 A))).fv)
      0

theorem nb090_fresh_813 (h : Var) :
    (nb090AlphaDummy480 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy477 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy477 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy477 h))).fv) :=
  by
  simpa only [nb090AlphaDummy480] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy477 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy477 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy477 h))).fv)
      0

theorem nb090_fresh_814 (A : Class) :
    (nb090AlphaDummy521 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy517 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy517 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy517 A))).fv) :=
  by
  simpa only [nb090AlphaDummy521] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy517 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy517 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy517 A))).fv)
      0

theorem nb090_fresh_815 (h : Var) :
    (nb090AlphaDummy522 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy519 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy519 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy519 h))).fv) :=
  by
  simpa only [nb090AlphaDummy522] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy519 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy519 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy519 h))).fv)
      0

theorem nb090_fresh_816 (A : Class) :
    (nb090AlphaDummy557 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy553 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy553 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy553 A))).fv) :=
  by
  simpa only [nb090AlphaDummy557] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy553 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy553 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy553 A))).fv)
      0

theorem nb090_fresh_817 (h : Var) :
    (nb090AlphaDummy558 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy555 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy555 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy555 h))).fv) :=
  by
  simpa only [nb090AlphaDummy558] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy555 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy555 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy555 h))).fv)
      0

theorem nb090_fresh_818 (A : Class) :
    (nb090AlphaDummy593 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy589 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy589 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy589 A))).fv) :=
  by
  simpa only [nb090AlphaDummy593] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy589 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy589 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy589 A))).fv)
      0

theorem nb090_fresh_819 (h : Var) :
    (nb090AlphaDummy594 h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy591 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy591 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy591 h))).fv) :=
  by
  simpa only [nb090AlphaDummy594] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy591 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy591 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy591 h))).fv)
      0

theorem nb090_fresh_820 (A : Class) :
    (nb090AlphaDummy629 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy625 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy625 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy625 A))).fv) :=
  by
  simpa only [nb090AlphaDummy629] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy625 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy625 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy625 A))).fv)
      0

theorem nb090_fresh_821 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy630 v u h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy627 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy627 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy627 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy630] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy627 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy627 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy627 v u h))).fv)
      0

theorem nb090_fresh_822 (A : Class) :
    (nb090AlphaDummy673 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy669 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy669 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy669 A))).fv) :=
  by
  simpa only [nb090AlphaDummy673] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy669 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy669 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy669 A))).fv)
      0

theorem nb090_fresh_823 (u : Var) :
    (nb090AlphaDummy674 u) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy671 u)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy671 u)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy671 u))).fv) :=
  by
  simpa only [nb090AlphaDummy674] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy671 u)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy671 u)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy671 u))).fv)
      0

theorem nb090_fresh_824 (A : Class) :
    (nb090AlphaDummy727 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy723 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy723 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy723 A))).fv) :=
  by
  simpa only [nb090AlphaDummy727] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy723 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy723 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy723 A))).fv)
      0

theorem nb090_fresh_825 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy728 v u h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy725 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy725 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy725 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy728] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy725 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy725 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy725 v u h))).fv)
      0

theorem nb090_fresh_826 (A : Class) :
    (nb090AlphaDummy757 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy753 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy753 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy753 A))).fv) :=
  by
  simpa only [nb090AlphaDummy757] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy753 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy753 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy753 A))).fv)
      0

theorem nb090_fresh_827 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy758 v u h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy755 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy755 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy755 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy758] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy755 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy755 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy755 v u h))).fv)
      0

theorem nb090_fresh_828 (A : Class) :
    (nb090AlphaDummy797 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy793 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy793 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy793 A))).fv) :=
  by
  simpa only [nb090AlphaDummy797] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy793 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy793 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy793 A))).fv)
      0

theorem nb090_fresh_829 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy798 v u h) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy795 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy795 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy795 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy798] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy795 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy795 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy795 v u h))).fv)
      0

theorem nb090_fresh_830 (A : Class) :
    (nb090AlphaDummy847 A) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy843 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy843 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy843 A))).fv) :=
  by
  simpa only [nb090AlphaDummy847] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy843 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy843 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy843 A))).fv)
      0

theorem nb090_fresh_831 (v : Var) :
    (nb090AlphaDummy848 v) ∉
      (((Wff.classMem (Class.cv (nb090AlphaDummy845 v)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy845 v)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy845 v))).fv) :=
  by
  simpa only [nb090AlphaDummy848] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090AlphaDummy845 v)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy845 v)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy845 v))).fv)
      0

theorem nb090_fresh_832 (A : Class) :
    (nb090AlphaDummy653 A) ∉
      (((synC1st)).fv ∪ ((Class.cv (nb090AlphaDummy001 A))).fv) :=
  by
  simpa only [nb090AlphaDummy653] using
    freshVar_not_mem (((synC1st)).fv ∪ ((Class.cv (nb090AlphaDummy001 A))).fv) 0

theorem nb090_fresh_833 (A : Class) :
    (nb090AlphaDummy827 A) ∉
      (((synC1st)).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) :=
  by
  simpa only [nb090AlphaDummy827] using
    freshVar_not_mem (((synC1st)).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) 0

theorem nb090_fresh_834 (u : Var) :
    (nb090AlphaDummy654 u) ∉ (((synC1st)).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb090AlphaDummy654] using
    freshVar_not_mem (((synC1st)).fv ∪ ((Class.cv u)).fv) 0

theorem nb090_fresh_835 (v : Var) :
    (nb090AlphaDummy828 v) ∉ (((synC1st)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090AlphaDummy828] using
    freshVar_not_mem (((synC1st)).fv ∪ ((Class.cv v)).fv) 0

theorem nb090_fresh_836 (A : Class) :
    (nb090AlphaDummy283 A) ∉
      (((synC2nd)).fv ∪ ((Class.cv (nb090AlphaDummy001 A))).fv) :=
  by
  simpa only [nb090AlphaDummy283] using
    freshVar_not_mem (((synC2nd)).fv ∪ ((Class.cv (nb090AlphaDummy001 A))).fv) 0

theorem nb090_fresh_837 (A : Class) :
    (nb090AlphaDummy373 A) ∉
      (((synC2nd)).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) :=
  by
  simpa only [nb090AlphaDummy373] using
    freshVar_not_mem (((synC2nd)).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) 0

theorem nb090_fresh_838 (u : Var) :
    (nb090AlphaDummy284 u) ∉ (((synC2nd)).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb090AlphaDummy284] using
    freshVar_not_mem (((synC2nd)).fv ∪ ((Class.cv u)).fv) 0

theorem nb090_fresh_839 (v : Var) :
    (nb090AlphaDummy374 v) ∉ (((synC2nd)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090AlphaDummy374] using
    freshVar_not_mem (((synC2nd)).fv ∪ ((Class.cv v)).fv) 0

theorem nb090_fresh_840 (A : Class) :
    (nb090AlphaDummy503 A) ∉ (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy503] using
    freshVar_not_mem (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) 0

theorem nb090_fresh_841 (A : Class) :
    (nb090AlphaDummy504 A) ∉ (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy504] using
    freshVar_not_mem (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part013`. -/


section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb090_distinct_842 (A : Class) :
    (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy504 A) := by
  simpa only [nb090AlphaDummy503, nb090AlphaDummy504] using
    (freshVar_injective (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb090_fresh_843 (A : Class) :
    (nb090AlphaDummy423 A) ∉
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv) :=
  by
  simpa only [nb090AlphaDummy423] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv)
      0

theorem nb090_fresh_844 (A : Class) :
    (nb090AlphaDummy424 A) ∉
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv) :=
  by
  simpa only [nb090AlphaDummy424] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv)
      1

theorem nb090_fresh_845 (A : Class) :
    (nb090AlphaDummy425 A) ∉
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv) :=
  by
  simpa only [nb090AlphaDummy425] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv)
      2

theorem nb090_distinct_846 (A : Class) :
    (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy424 A) := by
  simpa only [nb090AlphaDummy423, nb090AlphaDummy424] using
    (freshVar_injective (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_847 (A : Class) :
    (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy425 A) := by
  simpa only [nb090AlphaDummy423, nb090AlphaDummy425] using
    (freshVar_injective (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_848 (A : Class) :
    (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy425 A) := by
  simpa only [nb090AlphaDummy424, nb090AlphaDummy425] using
    (freshVar_injective (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_849 (A : Class) :
    (nb090AlphaDummy243 A) ∉
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb090AlphaDummy243] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCvv)).fv) 0

theorem nb090_fresh_850 (A : Class) :
    (nb090AlphaDummy244 A) ∉
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb090AlphaDummy244] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCvv)).fv) 1

theorem nb090_distinct_851 (A : Class) :
    (nb090AlphaDummy243 A) ≠ (nb090AlphaDummy244 A) := by
  simpa only [nb090AlphaDummy243, nb090AlphaDummy244] using
    (freshVar_injective
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCvv)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb090_fresh_852 (h : Var) :
    (nb090AlphaDummy505 h) ∉ (((synCcnv (Class.cv h))).fv) := by
  simpa only [nb090AlphaDummy505] using
    freshVar_not_mem (((synCcnv (Class.cv h))).fv) 0

theorem nb090_fresh_853 (h : Var) :
    (nb090AlphaDummy506 h) ∉ (((synCcnv (Class.cv h))).fv) := by
  simpa only [nb090AlphaDummy506] using
    freshVar_not_mem (((synCcnv (Class.cv h))).fv) 1

theorem nb090_distinct_854 (h : Var) :
    (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy506 h) := by
  simpa only [nb090AlphaDummy505, nb090AlphaDummy506] using
    (freshVar_injective (((synCcnv (Class.cv h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_855 (h : Var) :
    (nb090AlphaDummy426 h) ∉
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) :=
  by
  simpa only [nb090AlphaDummy426] using
    freshVar_not_mem
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 0

theorem nb090_fresh_856 (h : Var) :
    (nb090AlphaDummy427 h) ∉
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) :=
  by
  simpa only [nb090AlphaDummy427] using
    freshVar_not_mem
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 1

theorem nb090_fresh_857 (h : Var) :
    (nb090AlphaDummy428 h) ∉
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) :=
  by
  simpa only [nb090AlphaDummy428] using
    freshVar_not_mem
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 2

theorem nb090_distinct_858 (h : Var) :
    (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy427 h) := by
  simpa only [nb090AlphaDummy426, nb090AlphaDummy427] using
    (freshVar_injective
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb090_distinct_859 (h : Var) :
    (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy428 h) := by
  simpa only [nb090AlphaDummy426, nb090AlphaDummy428] using
    (freshVar_injective
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) (i := 0)
      (j := 2) (by decide))

theorem nb090_distinct_860 (h : Var) :
    (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy428 h) := by
  simpa only [nb090AlphaDummy427, nb090AlphaDummy428] using
    (freshVar_injective
      (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) (i := 1)
      (j := 2) (by decide))

theorem nb090_fresh_861 (h : Var) :
    (nb090AlphaDummy245 h) ∉ (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb090AlphaDummy245] using
    freshVar_not_mem (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) 0

theorem nb090_fresh_862 (h : Var) :
    (nb090AlphaDummy246 h) ∉ (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb090AlphaDummy246] using
    freshVar_not_mem (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) 1

theorem nb090_distinct_863 (h : Var) :
    (nb090AlphaDummy245 h) ≠ (nb090AlphaDummy246 h) := by
  simpa only [nb090AlphaDummy245, nb090AlphaDummy246] using
    (freshVar_injective (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_864 (A : Class) :
    (nb090AlphaDummy047 A) ∉
      (((synCcom (Class.cv (nb090AlphaDummy000 A))
            (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb090AlphaDummy047] using
    freshVar_not_mem
      (((synCcom (Class.cv (nb090AlphaDummy000 A))
            (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv ∪ ((synCid)).fv)
      0

theorem nb090_fresh_865 (h : Var) :
    (nb090AlphaDummy048 h) ∉
      (((synCcom (Class.cv h) (synCcnv (Class.cv h)))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb090AlphaDummy048] using
    freshVar_not_mem
      (((synCcom (Class.cv h) (synCcnv (Class.cv h)))).fv ∪ ((synCid)).fv) 0

theorem nb090_fresh_866 (A : Class) :
    (nb090AlphaDummy421 A) ∉
      (((synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
            (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A)))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb090AlphaDummy421] using
    freshVar_not_mem
      (((synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
            (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A)))))).fv ∪ ((synCid)).fv)
      0

theorem nb090_fresh_867 (h : Var) :
    (nb090AlphaDummy422 h) ∉
      (((synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))).fv ∪
        ((synCid)).fv) :=
  by
  simpa only [nb090AlphaDummy422] using
    freshVar_not_mem
      (((synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))).fv ∪
        ((synCid)).fv)
      0

theorem nb090_fresh_868 (A : Class) :
    (nb090AlphaDummy009 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy005 A)
              (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                  (synCphi (Class.cv (nb090AlphaDummy006 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy005 A)
              (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy005 A)
              (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                  (synCphi (Class.cv (nb090AlphaDummy006 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy005 A)
              (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_869 (v : Var) (u : Var) :
    (nb090AlphaDummy010 v u) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy007 v u)
              (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                  (synCphi (Class.cv (nb090AlphaDummy008 v u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy007 v u)
              (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy007 v u)
              (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                  (synCphi (Class.cv (nb090AlphaDummy008 v u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy007 v u)
              (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_870 (A : Class) :
    (nb090AlphaDummy061 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy057 A)
              (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                  (synCphi (Class.cv (nb090AlphaDummy058 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy057 A)
              (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy061] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy057 A)
              (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                  (synCphi (Class.cv (nb090AlphaDummy058 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy057 A)
              (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_871 (h : Var) :
    (nb090AlphaDummy062 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy059 h)
              (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                  (synCphi (Class.cv (nb090AlphaDummy060 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy059 h)
              (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy062] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy059 h)
              (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                  (synCphi (Class.cv (nb090AlphaDummy060 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy059 h)
              (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_872 (A : Class) :
    (nb090AlphaDummy097 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy093 A)
              (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                  (synCphi (Class.cv (nb090AlphaDummy094 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy093 A)
              (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy097] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy093 A)
              (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                  (synCphi (Class.cv (nb090AlphaDummy094 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy093 A)
              (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_873 (h : Var) :
    (nb090AlphaDummy098 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy095 h)
              (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                  (synCphi (Class.cv (nb090AlphaDummy096 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy095 h)
              (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy098] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy095 h)
              (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                  (synCphi (Class.cv (nb090AlphaDummy096 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy095 h)
              (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_874 (A : Class) :
    (nb090AlphaDummy139 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy135 A)
              (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                  (synCphi (Class.cv (nb090AlphaDummy136 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy135 A)
              (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy139] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy135 A)
              (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                  (synCphi (Class.cv (nb090AlphaDummy136 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy135 A)
              (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_875 (h : Var) :
    (nb090AlphaDummy140 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy137 h)
              (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                  (synCphi (Class.cv (nb090AlphaDummy138 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy137 h)
              (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy140] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy137 h)
              (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                  (synCphi (Class.cv (nb090AlphaDummy138 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy137 h)
              (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_876 (A : Class) :
    (nb090AlphaDummy175 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy171 A)
              (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                  (synCphi (Class.cv (nb090AlphaDummy172 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy171 A)
              (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy175] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy171 A)
              (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                  (synCphi (Class.cv (nb090AlphaDummy172 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy171 A)
              (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_877 (h : Var) :
    (nb090AlphaDummy176 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy173 h)
              (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                  (synCphi (Class.cv (nb090AlphaDummy174 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy173 h)
              (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy176] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy173 h)
              (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                  (synCphi (Class.cv (nb090AlphaDummy174 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy173 h)
              (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_878 (A : Class) :
    (nb090AlphaDummy211 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy207 A)
              (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                  (synCphi (Class.cv (nb090AlphaDummy208 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy207 A)
              (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy211] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy207 A)
              (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                  (synCphi (Class.cv (nb090AlphaDummy208 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy207 A)
              (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_879 (h : Var) :
    (nb090AlphaDummy212 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy209 h)
              (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                  (synCphi (Class.cv (nb090AlphaDummy210 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy209 h)
              (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy212] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy209 h)
              (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                  (synCphi (Class.cv (nb090AlphaDummy210 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy209 h)
              (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_880 (A : Class) :
    (nb090AlphaDummy251 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy247 A)
              (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                  (synCphi (Class.cv (nb090AlphaDummy248 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy247 A)
              (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy251] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy247 A)
              (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                  (synCphi (Class.cv (nb090AlphaDummy248 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy247 A)
              (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_881 (h : Var) :
    (nb090AlphaDummy252 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy249 h)
              (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                  (synCphi (Class.cv (nb090AlphaDummy250 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy249 h)
              (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy252] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy249 h)
              (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                  (synCphi (Class.cv (nb090AlphaDummy250 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy249 h)
              (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_882 (A : Class) :
    (nb090AlphaDummy295 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy291 A)
              (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                  (synCphi (Class.cv (nb090AlphaDummy292 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy291 A)
              (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy295] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy291 A)
              (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                  (synCphi (Class.cv (nb090AlphaDummy292 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy291 A)
              (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_883 (u : Var) :
    (nb090AlphaDummy296 u) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy293 u)
              (synWrex (nb090AlphaDummy294 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                  (synCphi (Class.cv (nb090AlphaDummy294 u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy293 u)
              (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
                (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy296] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy293 u)
              (synWrex (nb090AlphaDummy294 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                  (synCphi (Class.cv (nb090AlphaDummy294 u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy293 u)
              (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
                (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_884 (A : Class) :
    (nb090AlphaDummy341 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy337 A)
              (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                  (synCphi (Class.cv (nb090AlphaDummy338 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy337 A)
              (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy341] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy337 A)
              (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                  (synCphi (Class.cv (nb090AlphaDummy338 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy337 A)
              (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_885 (h : Var) :
    (nb090AlphaDummy342 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy339 h)
              (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                  (synCphi (Class.cv (nb090AlphaDummy340 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy339 h)
              (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy342] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy339 h)
              (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                  (synCphi (Class.cv (nb090AlphaDummy340 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy339 h)
              (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_886 (A : Class) :
    (nb090AlphaDummy385 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy381 A)
              (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                  (synCphi (Class.cv (nb090AlphaDummy382 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy381 A)
              (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy385] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy381 A)
              (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                  (synCphi (Class.cv (nb090AlphaDummy382 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy381 A)
              (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_887 (v : Var) :
    (nb090AlphaDummy386 v) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy383 v)
              (synWrex (nb090AlphaDummy384 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                  (synCphi (Class.cv (nb090AlphaDummy384 v)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy383 v)
              (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
                (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy386] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy383 v)
              (synWrex (nb090AlphaDummy384 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                  (synCphi (Class.cv (nb090AlphaDummy384 v)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy383 v)
              (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
                (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_888 (A : Class) :
    (nb090AlphaDummy435 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy431 A)
              (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                  (synCphi (Class.cv (nb090AlphaDummy432 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy431 A)
              (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy435] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy431 A)
              (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                  (synCphi (Class.cv (nb090AlphaDummy432 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy431 A)
              (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_889 (h : Var) :
    (nb090AlphaDummy436 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy433 h)
              (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                  (synCphi (Class.cv (nb090AlphaDummy434 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy433 h)
              (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy436] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy433 h)
              (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                  (synCphi (Class.cv (nb090AlphaDummy434 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy433 h)
              (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_890 (A : Class) :
    (nb090AlphaDummy471 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy467 A)
              (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                  (synCphi (Class.cv (nb090AlphaDummy468 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy467 A)
              (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy471] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy467 A)
              (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                  (synCphi (Class.cv (nb090AlphaDummy468 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy467 A)
              (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_891 (h : Var) :
    (nb090AlphaDummy472 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy469 h)
              (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                  (synCphi (Class.cv (nb090AlphaDummy470 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy469 h)
              (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy472] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy469 h)
              (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                  (synCphi (Class.cv (nb090AlphaDummy470 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy469 h)
              (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_892 (A : Class) :
    (nb090AlphaDummy513 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy509 A)
              (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                  (synCphi (Class.cv (nb090AlphaDummy510 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy509 A)
              (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy513] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy509 A)
              (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                  (synCphi (Class.cv (nb090AlphaDummy510 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy509 A)
              (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_893 (h : Var) :
    (nb090AlphaDummy514 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy511 h)
              (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                  (synCphi (Class.cv (nb090AlphaDummy512 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy511 h)
              (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy514] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy511 h)
              (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                  (synCphi (Class.cv (nb090AlphaDummy512 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy511 h)
              (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_894 (A : Class) :
    (nb090AlphaDummy549 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy545 A)
              (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                  (synCphi (Class.cv (nb090AlphaDummy546 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy545 A)
              (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy549] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy545 A)
              (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                  (synCphi (Class.cv (nb090AlphaDummy546 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy545 A)
              (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_895 (h : Var) :
    (nb090AlphaDummy550 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy547 h)
              (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                  (synCphi (Class.cv (nb090AlphaDummy548 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy547 h)
              (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy550] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy547 h)
              (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                  (synCphi (Class.cv (nb090AlphaDummy548 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy547 h)
              (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_896 (A : Class) :
    (nb090AlphaDummy585 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy581 A)
              (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                  (synCphi (Class.cv (nb090AlphaDummy582 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy581 A)
              (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy585] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy581 A)
              (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                  (synCphi (Class.cv (nb090AlphaDummy582 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy581 A)
              (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_897 (h : Var) :
    (nb090AlphaDummy586 h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy583 h)
              (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                  (synCphi (Class.cv (nb090AlphaDummy584 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy583 h)
              (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy586] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy583 h)
              (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                  (synCphi (Class.cv (nb090AlphaDummy584 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy583 h)
              (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_898 (A : Class) :
    (nb090AlphaDummy621 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy617 A)
              (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                  (synCphi (Class.cv (nb090AlphaDummy618 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy617 A)
              (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy621] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy617 A)
              (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                  (synCphi (Class.cv (nb090AlphaDummy618 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy617 A)
              (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_899 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy622 v u h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy619 v u h)
              (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy043 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy620 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
                (Class.cv (nb090AlphaDummy044 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy622] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy619 v u h)
              (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy043 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy620 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
                (Class.cv (nb090AlphaDummy044 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_900 (A : Class) :
    (nb090AlphaDummy665 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy661 A)
              (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                  (synCphi (Class.cv (nb090AlphaDummy662 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy661 A)
              (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy665] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy661 A)
              (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                  (synCphi (Class.cv (nb090AlphaDummy662 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy661 A)
              (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_901 (u : Var) :
    (nb090AlphaDummy666 u) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy663 u)
              (synWrex (nb090AlphaDummy664 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                  (synCphi (Class.cv (nb090AlphaDummy664 u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy663 u)
              (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
                (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy666] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy663 u)
              (synWrex (nb090AlphaDummy664 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                  (synCphi (Class.cv (nb090AlphaDummy664 u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy663 u)
              (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
                (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_902 (A : Class) :
    (nb090AlphaDummy703 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
                (synCfv (Class.cv (nb090AlphaDummy000 A))
                  (Class.cv (nb090AlphaDummy041 A)))
                (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                  (synCphi (Class.cv (nb090AlphaDummy700 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
                (synCfv (Class.cv (nb090AlphaDummy000 A))
                  (Class.cv (nb090AlphaDummy042 A)))
                (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy703] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
                (synCfv (Class.cv (nb090AlphaDummy000 A))
                  (Class.cv (nb090AlphaDummy041 A)))
                (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                  (synCphi (Class.cv (nb090AlphaDummy700 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
                (synCfv (Class.cv (nb090AlphaDummy000 A))
                  (Class.cv (nb090AlphaDummy042 A)))
                (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_903 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy704 v u h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy701 v u h)
              (synWrex (nb090AlphaDummy702 v u h)
                (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
                (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy702 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
                (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
                (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy704] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy701 v u h)
              (synWrex (nb090AlphaDummy702 v u h)
                (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
                (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy702 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
                (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
                (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_904 (A : Class) :
    (nb090AlphaDummy719 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy715 A)
              (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                  (synCphi (Class.cv (nb090AlphaDummy716 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy715 A)
              (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy719] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy715 A)
              (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                  (synCphi (Class.cv (nb090AlphaDummy716 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy715 A)
              (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_905 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy720 v u h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy717 v u h)
              (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy043 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy718 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
                (Class.cv (nb090AlphaDummy708 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy720] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy717 v u h)
              (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy043 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy718 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
                (Class.cv (nb090AlphaDummy708 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_906 (A : Class) :
    (nb090AlphaDummy789 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy785 A)
              (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                  (synCphi (Class.cv (nb090AlphaDummy786 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy785 A)
              (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy789] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy785 A)
              (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                  (synCphi (Class.cv (nb090AlphaDummy786 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy785 A)
              (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_907 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy790 v u h) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy787 v u h)
              (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy044 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy788 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
                (Class.cv (nb090AlphaDummy778 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy790] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy787 v u h)
              (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy044 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy788 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
                (Class.cv (nb090AlphaDummy778 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_908 (A : Class) :
    (nb090AlphaDummy839 A) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy835 A)
              (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                  (synCphi (Class.cv (nb090AlphaDummy836 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy835 A)
              (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy839] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy835 A)
              (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                  (synCphi (Class.cv (nb090AlphaDummy836 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy835 A)
              (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_909 (v : Var) :
    (nb090AlphaDummy840 v) ∉
      (((synCcompl (Class.cab (nb090AlphaDummy837 v)
              (synWrex (nb090AlphaDummy838 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                  (synCphi (Class.cv (nb090AlphaDummy838 v)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy837 v)
              (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
                (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb090AlphaDummy840] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb090AlphaDummy837 v)
              (synWrex (nb090AlphaDummy838 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                  (synCphi (Class.cv (nb090AlphaDummy838 v)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy837 v)
              (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
                (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb090_fresh_910 (A : Class) :
    (nb090AlphaDummy029 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy020 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy021 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy020 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy021 A)))).fv)
      0

theorem nb090_fresh_911 (v : Var) (u : Var) :
    (nb090AlphaDummy030 v u) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy023 v u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy024 v u)))).fv) :=
  by
  simpa only [nb090AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy023 v u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy024 v u)))).fv)
      0

theorem nb090_fresh_912 (A : Class) :
    (nb090AlphaDummy081 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy072 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy073 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy081] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy072 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy073 A)))).fv)
      0

theorem nb090_fresh_913 (h : Var) :
    (nb090AlphaDummy082 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy075 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy076 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy082] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy075 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy076 h)))).fv)
      0

theorem nb090_fresh_914 (A : Class) :
    (nb090AlphaDummy117 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy108 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy109 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy117] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy108 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy109 A)))).fv)
      0

theorem nb090_fresh_915 (h : Var) :
    (nb090AlphaDummy118 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy111 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy112 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy118] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy111 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy112 h)))).fv)
      0

theorem nb090_fresh_916 (A : Class) :
    (nb090AlphaDummy159 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy150 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy151 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy159] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy150 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy151 A)))).fv)
      0

theorem nb090_fresh_917 (h : Var) :
    (nb090AlphaDummy160 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy153 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy154 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy160] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy153 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy154 h)))).fv)
      0

theorem nb090_fresh_918 (A : Class) :
    (nb090AlphaDummy195 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy186 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy187 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy195] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy186 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy187 A)))).fv)
      0

theorem nb090_fresh_919 (h : Var) :
    (nb090AlphaDummy196 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy189 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy190 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy196] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy189 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy190 h)))).fv)
      0

theorem nb090_fresh_920 (A : Class) :
    (nb090AlphaDummy231 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy222 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy223 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy231] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy222 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy223 A)))).fv)
      0

theorem nb090_fresh_921 (h : Var) :
    (nb090AlphaDummy232 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy225 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy226 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy232] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy225 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy226 h)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
