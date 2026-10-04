/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part003

/-! NF weak partition development: NAR4H5C095M3Part004. -/


public section


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

theorem nb095_fresh_349 (f : Var) :
    (nb095AlphaDummy310 f) ∉ (((Class.cv (nb095AlphaDummy302 f))).fv) := by
  simpa only [nb095AlphaDummy310] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy302 f))).fv) 1

theorem nb095_distinct_350 (f : Var) :
    (nb095AlphaDummy309 f) ≠ (nb095AlphaDummy310 f) := by
  simpa only [nb095AlphaDummy309, nb095AlphaDummy310] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy302 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_351 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy313 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy313] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_352 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy314 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy314] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_353 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy315 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy315] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_354 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy313 D R S_cls E) ≠ (nb095AlphaDummy314 D R S_cls E) := by
  simpa only [nb095AlphaDummy313, nb095AlphaDummy314] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_355 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy313 D R S_cls E) ≠ (nb095AlphaDummy315 D R S_cls E) := by
  simpa only [nb095AlphaDummy313, nb095AlphaDummy315] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_356 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy314 D R S_cls E) ≠ (nb095AlphaDummy315 D R S_cls E) := by
  simpa only [nb095AlphaDummy314, nb095AlphaDummy315] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_357 (f : Var) :
    (nb095AlphaDummy316 f) ∉
      (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy316] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_358 (f : Var) :
    (nb095AlphaDummy317 f) ∉
      (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy317] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_359 (f : Var) :
    (nb095AlphaDummy318 f) ∉
      (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy318] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_360 (f : Var) :
    (nb095AlphaDummy316 f) ≠ (nb095AlphaDummy317 f) := by
  simpa only [nb095AlphaDummy316, nb095AlphaDummy317] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_361 (f : Var) :
    (nb095AlphaDummy316 f) ≠ (nb095AlphaDummy318 f) := by
  simpa only [nb095AlphaDummy316, nb095AlphaDummy318] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_362 (f : Var) :
    (nb095AlphaDummy317 f) ≠ (nb095AlphaDummy318 f) := by
  simpa only [nb095AlphaDummy317, nb095AlphaDummy318] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_363 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy325 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy314 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy314 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy325] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy314 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy314 D R S_cls E))).fv)
      0

theorem nb095_fresh_364 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy321 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy314 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy315 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy321] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy314 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy315 D R S_cls E))).fv)
      0

theorem nb095_fresh_365 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy327 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy315 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy315 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy327] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy315 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy315 D R S_cls E))).fv)
      0

theorem nb095_fresh_366 (f : Var) :
    (nb095AlphaDummy326 f) ∉
      (((Class.cv (nb095AlphaDummy317 f))).fv ∪ ((Class.cv (nb095AlphaDummy317 f))).fv) :=
  by
  simpa only [nb095AlphaDummy326] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy317 f))).fv ∪ ((Class.cv (nb095AlphaDummy317 f))).fv)
      0

theorem nb095_fresh_367 (f : Var) :
    (nb095AlphaDummy322 f) ∉
      (((Class.cv (nb095AlphaDummy317 f))).fv ∪ ((Class.cv (nb095AlphaDummy318 f))).fv) :=
  by
  simpa only [nb095AlphaDummy322] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy317 f))).fv ∪ ((Class.cv (nb095AlphaDummy318 f))).fv)
      0

theorem nb095_fresh_368 (f : Var) :
    (nb095AlphaDummy328 f) ∉
      (((Class.cv (nb095AlphaDummy318 f))).fv ∪ ((Class.cv (nb095AlphaDummy318 f))).fv) :=
  by
  simpa only [nb095AlphaDummy328] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy318 f))).fv ∪ ((Class.cv (nb095AlphaDummy318 f))).fv)
      0

theorem nb095_fresh_369 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy345 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy340 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy345] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy340 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv)
      0

theorem nb095_fresh_370 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy346 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy340 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy346] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy340 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv)
      1

theorem nb095_distinct_371 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy345 D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) := by
  simpa only [nb095AlphaDummy345, nb095AlphaDummy346] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy340 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_372 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy347 u S_cls) ∉
      (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪
        ((Class.cv (nb095AlphaDummy341 u S_cls))).fv) :=
  by
  simpa only [nb095AlphaDummy347] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪
        ((Class.cv (nb095AlphaDummy341 u S_cls))).fv)
      0

theorem nb095_fresh_373 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy348 u S_cls) ∉
      (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪
        ((Class.cv (nb095AlphaDummy341 u S_cls))).fv) :=
  by
  simpa only [nb095AlphaDummy348] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪
        ((Class.cv (nb095AlphaDummy341 u S_cls))).fv)
      1

theorem nb095_distinct_374 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy347 u S_cls) ≠ (nb095AlphaDummy348 u S_cls) := by
  simpa only [nb095AlphaDummy347, nb095AlphaDummy348] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪
        ((Class.cv (nb095AlphaDummy341 u S_cls))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_375 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy353 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy346 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy353] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy346 D R S_cls E))).fv) 0

theorem nb095_fresh_376 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy354 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy346 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy354] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy346 D R S_cls E))).fv) 1

theorem nb095_distinct_377 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy353 D R S_cls E) ≠ (nb095AlphaDummy354 D R S_cls E) := by
  simpa only [nb095AlphaDummy353, nb095AlphaDummy354] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy346 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_378 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy355 u S_cls) ∉ (((Class.cv (nb095AlphaDummy348 u S_cls))).fv) :=
  by
  simpa only [nb095AlphaDummy355] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy348 u S_cls))).fv) 0

theorem nb095_fresh_379 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy356 u S_cls) ∉ (((Class.cv (nb095AlphaDummy348 u S_cls))).fv) :=
  by
  simpa only [nb095AlphaDummy356] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy348 u S_cls))).fv) 1

theorem nb095_distinct_380 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy355 u S_cls) ≠ (nb095AlphaDummy356 u S_cls) := by
  simpa only [nb095AlphaDummy355, nb095AlphaDummy356] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy348 u S_cls))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb095_fresh_381 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy359 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy359] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_382 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy360 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy360] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_383 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy361 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy361] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_384 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy359 D R S_cls E) ≠ (nb095AlphaDummy360 D R S_cls E) := by
  simpa only [nb095AlphaDummy359, nb095AlphaDummy360] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_385 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy359 D R S_cls E) ≠ (nb095AlphaDummy361 D R S_cls E) := by
  simpa only [nb095AlphaDummy359, nb095AlphaDummy361] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_386 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy360 D R S_cls E) ≠ (nb095AlphaDummy361 D R S_cls E) := by
  simpa only [nb095AlphaDummy360, nb095AlphaDummy361] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_387 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy362 u S_cls) ∉
      (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy362] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_388 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy363 u S_cls) ∉
      (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy363] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_389 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy364 u S_cls) ∉
      (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy364] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_390 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy362 u S_cls) ≠ (nb095AlphaDummy363 u S_cls) := by
  simpa only [nb095AlphaDummy362, nb095AlphaDummy363] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_distinct_391 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy362 u S_cls) ≠ (nb095AlphaDummy364 u S_cls) := by
  simpa only [nb095AlphaDummy362, nb095AlphaDummy364] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb095_distinct_392 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy363 u S_cls) ≠ (nb095AlphaDummy364 u S_cls) := by
  simpa only [nb095AlphaDummy363, nb095AlphaDummy364] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb095_fresh_393 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy371 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy360 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy360 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy371] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy360 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy360 D R S_cls E))).fv)
      0

theorem nb095_fresh_394 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy367 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy360 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy361 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy367] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy360 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy361 D R S_cls E))).fv)
      0

theorem nb095_fresh_395 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy373 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy361 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy361 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy373] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy361 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy361 D R S_cls E))).fv)
      0

theorem nb095_fresh_396 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy372 u S_cls) ∉
      (((Class.cv (nb095AlphaDummy363 u S_cls))).fv ∪
        ((Class.cv (nb095AlphaDummy363 u S_cls))).fv) :=
  by
  simpa only [nb095AlphaDummy372] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy363 u S_cls))).fv ∪
        ((Class.cv (nb095AlphaDummy363 u S_cls))).fv)
      0

theorem nb095_fresh_397 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy368 u S_cls) ∉
      (((Class.cv (nb095AlphaDummy363 u S_cls))).fv ∪
        ((Class.cv (nb095AlphaDummy364 u S_cls))).fv) :=
  by
  simpa only [nb095AlphaDummy368] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy363 u S_cls))).fv ∪
        ((Class.cv (nb095AlphaDummy364 u S_cls))).fv)
      0

theorem nb095_fresh_398 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy374 u S_cls) ∉
      (((Class.cv (nb095AlphaDummy364 u S_cls))).fv ∪
        ((Class.cv (nb095AlphaDummy364 u S_cls))).fv) :=
  by
  simpa only [nb095AlphaDummy374] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy364 u S_cls))).fv ∪
        ((Class.cv (nb095AlphaDummy364 u S_cls))).fv)
      0

theorem nb095_fresh_399 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy393 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy393] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv)
      0

theorem nb095_fresh_400 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy394 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy394] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv)
      1

theorem nb095_distinct_401 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy393 D R S_cls E) ≠ (nb095AlphaDummy394 D R S_cls E) := by
  simpa only [nb095AlphaDummy393, nb095AlphaDummy394] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_402 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy429 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy429] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv)
      0

theorem nb095_fresh_403 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy430 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy430] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv)
      1

theorem nb095_distinct_404 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy429 D R S_cls E) ≠ (nb095AlphaDummy430 D R S_cls E) := by
  simpa only [nb095AlphaDummy429, nb095AlphaDummy430] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_405 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy543 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy543] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv)
      0

theorem nb095_fresh_406 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy544 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy544] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv)
      1

theorem nb095_distinct_407 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy543 D R S_cls E) ≠ (nb095AlphaDummy544 D R S_cls E) := by
  simpa only [nb095AlphaDummy543, nb095AlphaDummy544] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_408 (f : Var) :
    (nb095AlphaDummy395 f) ∉
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv) :=
  by
  simpa only [nb095AlphaDummy395] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv)
      0

theorem nb095_fresh_409 (f : Var) :
    (nb095AlphaDummy396 f) ∉
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv) :=
  by
  simpa only [nb095AlphaDummy396] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv)
      1

theorem nb095_distinct_410 (f : Var) :
    (nb095AlphaDummy395 f) ≠ (nb095AlphaDummy396 f) := by
  simpa only [nb095AlphaDummy395, nb095AlphaDummy396] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy388 f))).fv ∪
        ((Class.cv (nb095AlphaDummy389 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_411 (f : Var) :
    (nb095AlphaDummy431 f) ∉
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy390 f))).fv) :=
  by
  simpa only [nb095AlphaDummy431] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy390 f))).fv)
      0

theorem nb095_fresh_412 (f : Var) :
    (nb095AlphaDummy432 f) ∉
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy390 f))).fv) :=
  by
  simpa only [nb095AlphaDummy432] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy390 f))).fv)
      1

theorem nb095_distinct_413 (f : Var) :
    (nb095AlphaDummy431 f) ≠ (nb095AlphaDummy432 f) := by
  simpa only [nb095AlphaDummy431, nb095AlphaDummy432] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy388 f))).fv ∪
        ((Class.cv (nb095AlphaDummy390 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_414 (f : Var) :
    (nb095AlphaDummy545 f) ∉
      (((Class.cv (nb095AlphaDummy390 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv) :=
  by
  simpa only [nb095AlphaDummy545] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy390 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv)
      0

theorem nb095_fresh_415 (f : Var) :
    (nb095AlphaDummy546 f) ∉
      (((Class.cv (nb095AlphaDummy390 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv) :=
  by
  simpa only [nb095AlphaDummy546] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy390 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv)
      1

theorem nb095_distinct_416 (f : Var) :
    (nb095AlphaDummy545 f) ≠ (nb095AlphaDummy546 f) := by
  simpa only [nb095AlphaDummy545, nb095AlphaDummy546] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy390 f))).fv ∪
        ((Class.cv (nb095AlphaDummy389 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_417 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy401 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy394 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy401] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy394 D R S_cls E))).fv) 0

theorem nb095_fresh_418 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy402 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy394 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy402] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy394 D R S_cls E))).fv) 1

theorem nb095_distinct_419 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy401 D R S_cls E) ≠ (nb095AlphaDummy402 D R S_cls E) := by
  simpa only [nb095AlphaDummy401, nb095AlphaDummy402] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy394 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_420 (f : Var) :
    (nb095AlphaDummy403 f) ∉ (((Class.cv (nb095AlphaDummy396 f))).fv) := by
  simpa only [nb095AlphaDummy403] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy396 f))).fv) 0

theorem nb095_fresh_421 (f : Var) :
    (nb095AlphaDummy404 f) ∉ (((Class.cv (nb095AlphaDummy396 f))).fv) := by
  simpa only [nb095AlphaDummy404] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy396 f))).fv) 1

theorem nb095_distinct_422 (f : Var) :
    (nb095AlphaDummy403 f) ≠ (nb095AlphaDummy404 f) := by
  simpa only [nb095AlphaDummy403, nb095AlphaDummy404] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy396 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_423 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy407 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy407] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_424 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy408 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy408] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_425 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy409 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy409] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_426 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy407 D R S_cls E) ≠ (nb095AlphaDummy408 D R S_cls E) := by
  simpa only [nb095AlphaDummy407, nb095AlphaDummy408] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_427 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy407 D R S_cls E) ≠ (nb095AlphaDummy409 D R S_cls E) := by
  simpa only [nb095AlphaDummy407, nb095AlphaDummy409] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_428 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy408 D R S_cls E) ≠ (nb095AlphaDummy409 D R S_cls E) := by
  simpa only [nb095AlphaDummy408, nb095AlphaDummy409] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_429 (f : Var) :
    (nb095AlphaDummy410 f) ∉
      (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy410] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_430 (f : Var) :
    (nb095AlphaDummy411 f) ∉
      (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy411] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_431 (f : Var) :
    (nb095AlphaDummy412 f) ∉
      (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy412] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_432 (f : Var) :
    (nb095AlphaDummy410 f) ≠ (nb095AlphaDummy411 f) := by
  simpa only [nb095AlphaDummy410, nb095AlphaDummy411] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_433 (f : Var) :
    (nb095AlphaDummy410 f) ≠ (nb095AlphaDummy412 f) := by
  simpa only [nb095AlphaDummy410, nb095AlphaDummy412] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_434 (f : Var) :
    (nb095AlphaDummy411 f) ≠ (nb095AlphaDummy412 f) := by
  simpa only [nb095AlphaDummy411, nb095AlphaDummy412] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_435 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy419 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy419] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv)
      0

theorem nb095_fresh_436 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy415 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy415] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv)
      0

theorem nb095_fresh_437 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy421 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy421] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv)
      0

theorem nb095_fresh_438 (f : Var) :
    (nb095AlphaDummy420 f) ∉
      (((Class.cv (nb095AlphaDummy411 f))).fv ∪ ((Class.cv (nb095AlphaDummy411 f))).fv) :=
  by
  simpa only [nb095AlphaDummy420] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy411 f))).fv ∪ ((Class.cv (nb095AlphaDummy411 f))).fv)
      0

theorem nb095_fresh_439 (f : Var) :
    (nb095AlphaDummy416 f) ∉
      (((Class.cv (nb095AlphaDummy411 f))).fv ∪ ((Class.cv (nb095AlphaDummy412 f))).fv) :=
  by
  simpa only [nb095AlphaDummy416] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy411 f))).fv ∪ ((Class.cv (nb095AlphaDummy412 f))).fv)
      0

theorem nb095_fresh_440 (f : Var) :
    (nb095AlphaDummy422 f) ∉
      (((Class.cv (nb095AlphaDummy412 f))).fv ∪ ((Class.cv (nb095AlphaDummy412 f))).fv) :=
  by
  simpa only [nb095AlphaDummy422] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy412 f))).fv ∪ ((Class.cv (nb095AlphaDummy412 f))).fv)
      0

theorem nb095_fresh_441 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy437 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy430 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy437] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy430 D R S_cls E))).fv) 0

theorem nb095_fresh_442 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy438 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy430 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy438] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy430 D R S_cls E))).fv) 1

theorem nb095_distinct_443 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy437 D R S_cls E) ≠ (nb095AlphaDummy438 D R S_cls E) := by
  simpa only [nb095AlphaDummy437, nb095AlphaDummy438] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy430 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_444 (f : Var) :
    (nb095AlphaDummy439 f) ∉ (((Class.cv (nb095AlphaDummy432 f))).fv) := by
  simpa only [nb095AlphaDummy439] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy432 f))).fv) 0

theorem nb095_fresh_445 (f : Var) :
    (nb095AlphaDummy440 f) ∉ (((Class.cv (nb095AlphaDummy432 f))).fv) := by
  simpa only [nb095AlphaDummy440] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy432 f))).fv) 1

theorem nb095_distinct_446 (f : Var) :
    (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy440 f) := by
  simpa only [nb095AlphaDummy439, nb095AlphaDummy440] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy432 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_447 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy443 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy443] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_448 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy444 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy444] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_449 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy445 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy445] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_450 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy443 D R S_cls E) ≠ (nb095AlphaDummy444 D R S_cls E) := by
  simpa only [nb095AlphaDummy443, nb095AlphaDummy444] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_451 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy443 D R S_cls E) ≠ (nb095AlphaDummy445 D R S_cls E) := by
  simpa only [nb095AlphaDummy443, nb095AlphaDummy445] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_452 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy444 D R S_cls E) ≠ (nb095AlphaDummy445 D R S_cls E) := by
  simpa only [nb095AlphaDummy444, nb095AlphaDummy445] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_453 (f : Var) :
    (nb095AlphaDummy446 f) ∉
      (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy446] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_454 (f : Var) :
    (nb095AlphaDummy447 f) ∉
      (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy447] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_455 (f : Var) :
    (nb095AlphaDummy448 f) ∉
      (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy448] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_456 (f : Var) :
    (nb095AlphaDummy446 f) ≠ (nb095AlphaDummy447 f) := by
  simpa only [nb095AlphaDummy446, nb095AlphaDummy447] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_457 (f : Var) :
    (nb095AlphaDummy446 f) ≠ (nb095AlphaDummy448 f) := by
  simpa only [nb095AlphaDummy446, nb095AlphaDummy448] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_458 (f : Var) :
    (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy448 f) := by
  simpa only [nb095AlphaDummy447, nb095AlphaDummy448] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_459 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy455 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy455] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv)
      0

theorem nb095_fresh_460 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy451 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy451] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy444 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv)
      0

theorem nb095_fresh_461 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy457 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy457] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy445 D R S_cls E))).fv)
      0

theorem nb095_fresh_462 (f : Var) :
    (nb095AlphaDummy456 f) ∉
      (((Class.cv (nb095AlphaDummy447 f))).fv ∪ ((Class.cv (nb095AlphaDummy447 f))).fv) :=
  by
  simpa only [nb095AlphaDummy456] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy447 f))).fv ∪ ((Class.cv (nb095AlphaDummy447 f))).fv)
      0

theorem nb095_fresh_463 (f : Var) :
    (nb095AlphaDummy452 f) ∉
      (((Class.cv (nb095AlphaDummy447 f))).fv ∪ ((Class.cv (nb095AlphaDummy448 f))).fv) :=
  by
  simpa only [nb095AlphaDummy452] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy447 f))).fv ∪ ((Class.cv (nb095AlphaDummy448 f))).fv)
      0

theorem nb095_fresh_464 (f : Var) :
    (nb095AlphaDummy458 f) ∉
      (((Class.cv (nb095AlphaDummy448 f))).fv ∪ ((Class.cv (nb095AlphaDummy448 f))).fv) :=
  by
  simpa only [nb095AlphaDummy458] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy448 f))).fv ∪ ((Class.cv (nb095AlphaDummy448 f))).fv)
      0

theorem nb095_fresh_465 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy471 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy471] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv)
      0

theorem nb095_fresh_466 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy472 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy472] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv)
      1

theorem nb095_distinct_467 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy471 D R S_cls E) ≠ (nb095AlphaDummy472 D R S_cls E) := by
  simpa only [nb095AlphaDummy471, nb095AlphaDummy472] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_468 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy507 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy507] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv)
      0

theorem nb095_fresh_469 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy508 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy508] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv)
      1

theorem nb095_distinct_470 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy507 D R S_cls E) ≠ (nb095AlphaDummy508 D R S_cls E) := by
  simpa only [nb095AlphaDummy507, nb095AlphaDummy508] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_471 (f : Var) :
    (nb095AlphaDummy473 f) ∉
      (((Class.cv (nb095AlphaDummy467 f))).fv ∪ ((Class.cv (nb095AlphaDummy468 f))).fv) :=
  by
  simpa only [nb095AlphaDummy473] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy467 f))).fv ∪ ((Class.cv (nb095AlphaDummy468 f))).fv)
      0

theorem nb095_fresh_472 (f : Var) :
    (nb095AlphaDummy474 f) ∉
      (((Class.cv (nb095AlphaDummy467 f))).fv ∪ ((Class.cv (nb095AlphaDummy468 f))).fv) :=
  by
  simpa only [nb095AlphaDummy474] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy467 f))).fv ∪ ((Class.cv (nb095AlphaDummy468 f))).fv)
      1

theorem nb095_distinct_473 (f : Var) :
    (nb095AlphaDummy473 f) ≠ (nb095AlphaDummy474 f) := by
  simpa only [nb095AlphaDummy473, nb095AlphaDummy474] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy467 f))).fv ∪
        ((Class.cv (nb095AlphaDummy468 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_474 (f : Var) :
    (nb095AlphaDummy509 f) ∉
      (((Class.cv (nb095AlphaDummy468 f))).fv ∪ ((Class.cv (nb095AlphaDummy467 f))).fv) :=
  by
  simpa only [nb095AlphaDummy509] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy468 f))).fv ∪ ((Class.cv (nb095AlphaDummy467 f))).fv)
      0

theorem nb095_fresh_475 (f : Var) :
    (nb095AlphaDummy510 f) ∉
      (((Class.cv (nb095AlphaDummy468 f))).fv ∪ ((Class.cv (nb095AlphaDummy467 f))).fv) :=
  by
  simpa only [nb095AlphaDummy510] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy468 f))).fv ∪ ((Class.cv (nb095AlphaDummy467 f))).fv)
      1

theorem nb095_distinct_476 (f : Var) :
    (nb095AlphaDummy509 f) ≠ (nb095AlphaDummy510 f) := by
  simpa only [nb095AlphaDummy509, nb095AlphaDummy510] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy468 f))).fv ∪
        ((Class.cv (nb095AlphaDummy467 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_477 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy479 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy479] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) 0

theorem nb095_fresh_478 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy480 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy480] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) 1

theorem nb095_distinct_479 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy479 D R S_cls E) ≠ (nb095AlphaDummy480 D R S_cls E) := by
  simpa only [nb095AlphaDummy479, nb095AlphaDummy480] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_480 (f : Var) :
    (nb095AlphaDummy481 f) ∉ (((Class.cv (nb095AlphaDummy474 f))).fv) := by
  simpa only [nb095AlphaDummy481] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy474 f))).fv) 0

theorem nb095_fresh_481 (f : Var) :
    (nb095AlphaDummy482 f) ∉ (((Class.cv (nb095AlphaDummy474 f))).fv) := by
  simpa only [nb095AlphaDummy482] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy474 f))).fv) 1

theorem nb095_distinct_482 (f : Var) :
    (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy482 f) := by
  simpa only [nb095AlphaDummy481, nb095AlphaDummy482] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy474 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_483 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy485 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy485] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_484 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy486 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy486] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_485 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy487 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy487] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_486 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy485 D R S_cls E) ≠ (nb095AlphaDummy486 D R S_cls E) := by
  simpa only [nb095AlphaDummy485, nb095AlphaDummy486] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_487 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy485 D R S_cls E) ≠ (nb095AlphaDummy487 D R S_cls E) := by
  simpa only [nb095AlphaDummy485, nb095AlphaDummy487] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_488 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy487 D R S_cls E) := by
  simpa only [nb095AlphaDummy486, nb095AlphaDummy487] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_489 (f : Var) :
    (nb095AlphaDummy488 f) ∉
      (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy488] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_490 (f : Var) :
    (nb095AlphaDummy489 f) ∉
      (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy489] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_491 (f : Var) :
    (nb095AlphaDummy490 f) ∉
      (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy490] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_492 (f : Var) :
    (nb095AlphaDummy488 f) ≠ (nb095AlphaDummy489 f) := by
  simpa only [nb095AlphaDummy488, nb095AlphaDummy489] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_493 (f : Var) :
    (nb095AlphaDummy488 f) ≠ (nb095AlphaDummy490 f) := by
  simpa only [nb095AlphaDummy488, nb095AlphaDummy490] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_494 (f : Var) :
    (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy490 f) := by
  simpa only [nb095AlphaDummy489, nb095AlphaDummy490] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_495 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy497 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy497] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv)
      0

theorem nb095_fresh_496 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy493 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy493] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy486 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv)
      0

theorem nb095_fresh_497 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy499 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy499] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy487 D R S_cls E))).fv)
      0

theorem nb095_fresh_498 (f : Var) :
    (nb095AlphaDummy498 f) ∉
      (((Class.cv (nb095AlphaDummy489 f))).fv ∪ ((Class.cv (nb095AlphaDummy489 f))).fv) :=
  by
  simpa only [nb095AlphaDummy498] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy489 f))).fv ∪ ((Class.cv (nb095AlphaDummy489 f))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

theorem nb095_fresh_499 (f : Var) :
    (nb095AlphaDummy494 f) ∉
      (((Class.cv (nb095AlphaDummy489 f))).fv ∪ ((Class.cv (nb095AlphaDummy490 f))).fv) :=
  by
  simpa only [nb095AlphaDummy494] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy489 f))).fv ∪ ((Class.cv (nb095AlphaDummy490 f))).fv)
      0

theorem nb095_fresh_500 (f : Var) :
    (nb095AlphaDummy500 f) ∉
      (((Class.cv (nb095AlphaDummy490 f))).fv ∪ ((Class.cv (nb095AlphaDummy490 f))).fv) :=
  by
  simpa only [nb095AlphaDummy500] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy490 f))).fv ∪ ((Class.cv (nb095AlphaDummy490 f))).fv)
      0

theorem nb095_fresh_501 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy515 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy515] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) 0

theorem nb095_fresh_502 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy516 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy516] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) 1

theorem nb095_distinct_503 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy516 D R S_cls E) := by
  simpa only [nb095AlphaDummy515, nb095AlphaDummy516] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_504 (f : Var) :
    (nb095AlphaDummy517 f) ∉ (((Class.cv (nb095AlphaDummy510 f))).fv) := by
  simpa only [nb095AlphaDummy517] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy510 f))).fv) 0

theorem nb095_fresh_505 (f : Var) :
    (nb095AlphaDummy518 f) ∉ (((Class.cv (nb095AlphaDummy510 f))).fv) := by
  simpa only [nb095AlphaDummy518] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy510 f))).fv) 1

theorem nb095_distinct_506 (f : Var) :
    (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy518 f) := by
  simpa only [nb095AlphaDummy517, nb095AlphaDummy518] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy510 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_507 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy521 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy521] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_508 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy522 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy522] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_509 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy523 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy523] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_510 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy521 D R S_cls E) ≠ (nb095AlphaDummy522 D R S_cls E) := by
  simpa only [nb095AlphaDummy521, nb095AlphaDummy522] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_511 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy521 D R S_cls E) ≠ (nb095AlphaDummy523 D R S_cls E) := by
  simpa only [nb095AlphaDummy521, nb095AlphaDummy523] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_512 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy523 D R S_cls E) := by
  simpa only [nb095AlphaDummy522, nb095AlphaDummy523] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_513 (f : Var) :
    (nb095AlphaDummy524 f) ∉
      (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy524] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_514 (f : Var) :
    (nb095AlphaDummy525 f) ∉
      (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy525] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_515 (f : Var) :
    (nb095AlphaDummy526 f) ∉
      (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy526] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_516 (f : Var) :
    (nb095AlphaDummy524 f) ≠ (nb095AlphaDummy525 f) := by
  simpa only [nb095AlphaDummy524, nb095AlphaDummy525] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_517 (f : Var) :
    (nb095AlphaDummy524 f) ≠ (nb095AlphaDummy526 f) := by
  simpa only [nb095AlphaDummy524, nb095AlphaDummy526] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_518 (f : Var) :
    (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy526 f) := by
  simpa only [nb095AlphaDummy525, nb095AlphaDummy526] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_519 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy533 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy533] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv)
      0

theorem nb095_fresh_520 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy529 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy529] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy522 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv)
      0

theorem nb095_fresh_521 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy535 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy535] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy523 D R S_cls E))).fv)
      0

theorem nb095_fresh_522 (f : Var) :
    (nb095AlphaDummy534 f) ∉
      (((Class.cv (nb095AlphaDummy525 f))).fv ∪ ((Class.cv (nb095AlphaDummy525 f))).fv) :=
  by
  simpa only [nb095AlphaDummy534] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy525 f))).fv ∪ ((Class.cv (nb095AlphaDummy525 f))).fv)
      0

theorem nb095_fresh_523 (f : Var) :
    (nb095AlphaDummy530 f) ∉
      (((Class.cv (nb095AlphaDummy525 f))).fv ∪ ((Class.cv (nb095AlphaDummy526 f))).fv) :=
  by
  simpa only [nb095AlphaDummy530] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy525 f))).fv ∪ ((Class.cv (nb095AlphaDummy526 f))).fv)
      0

theorem nb095_fresh_524 (f : Var) :
    (nb095AlphaDummy536 f) ∉
      (((Class.cv (nb095AlphaDummy526 f))).fv ∪ ((Class.cv (nb095AlphaDummy526 f))).fv) :=
  by
  simpa only [nb095AlphaDummy536] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy526 f))).fv ∪ ((Class.cv (nb095AlphaDummy526 f))).fv)
      0

theorem nb095_fresh_525 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy551 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy551] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) 0

theorem nb095_fresh_526 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy552 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy552] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) 1

theorem nb095_distinct_527 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy552 D R S_cls E) := by
  simpa only [nb095AlphaDummy551, nb095AlphaDummy552] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_528 (f : Var) :
    (nb095AlphaDummy553 f) ∉ (((Class.cv (nb095AlphaDummy546 f))).fv) := by
  simpa only [nb095AlphaDummy553] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy546 f))).fv) 0

theorem nb095_fresh_529 (f : Var) :
    (nb095AlphaDummy554 f) ∉ (((Class.cv (nb095AlphaDummy546 f))).fv) := by
  simpa only [nb095AlphaDummy554] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy546 f))).fv) 1

theorem nb095_distinct_530 (f : Var) :
    (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy554 f) := by
  simpa only [nb095AlphaDummy553, nb095AlphaDummy554] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy546 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_531 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy557 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy557] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_532 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy558 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy558] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_533 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy559 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy559] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_534 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy557 D R S_cls E) ≠ (nb095AlphaDummy558 D R S_cls E) := by
  simpa only [nb095AlphaDummy557, nb095AlphaDummy558] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_535 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy557 D R S_cls E) ≠ (nb095AlphaDummy559 D R S_cls E) := by
  simpa only [nb095AlphaDummy557, nb095AlphaDummy559] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_536 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy559 D R S_cls E) := by
  simpa only [nb095AlphaDummy558, nb095AlphaDummy559] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_537 (f : Var) :
    (nb095AlphaDummy560 f) ∉
      (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy560] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_538 (f : Var) :
    (nb095AlphaDummy561 f) ∉
      (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy561] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_539 (f : Var) :
    (nb095AlphaDummy562 f) ∉
      (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy562] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_540 (f : Var) :
    (nb095AlphaDummy560 f) ≠ (nb095AlphaDummy561 f) := by
  simpa only [nb095AlphaDummy560, nb095AlphaDummy561] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_541 (f : Var) :
    (nb095AlphaDummy560 f) ≠ (nb095AlphaDummy562 f) := by
  simpa only [nb095AlphaDummy560, nb095AlphaDummy562] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_542 (f : Var) :
    (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy562 f) := by
  simpa only [nb095AlphaDummy561, nb095AlphaDummy562] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_543 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy569 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy569] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv)
      0

theorem nb095_fresh_544 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy565 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy565] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy558 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv)
      0

theorem nb095_fresh_545 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy571 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy571] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy559 D R S_cls E))).fv)
      0

theorem nb095_fresh_546 (f : Var) :
    (nb095AlphaDummy570 f) ∉
      (((Class.cv (nb095AlphaDummy561 f))).fv ∪ ((Class.cv (nb095AlphaDummy561 f))).fv) :=
  by
  simpa only [nb095AlphaDummy570] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy561 f))).fv ∪ ((Class.cv (nb095AlphaDummy561 f))).fv)
      0

theorem nb095_fresh_547 (f : Var) :
    (nb095AlphaDummy566 f) ∉
      (((Class.cv (nb095AlphaDummy561 f))).fv ∪ ((Class.cv (nb095AlphaDummy562 f))).fv) :=
  by
  simpa only [nb095AlphaDummy566] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy561 f))).fv ∪ ((Class.cv (nb095AlphaDummy562 f))).fv)
      0

theorem nb095_fresh_548 (f : Var) :
    (nb095AlphaDummy572 f) ∉
      (((Class.cv (nb095AlphaDummy562 f))).fv ∪ ((Class.cv (nb095AlphaDummy562 f))).fv) :=
  by
  simpa only [nb095AlphaDummy572] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy562 f))).fv ∪ ((Class.cv (nb095AlphaDummy562 f))).fv)
      0

theorem nb095_fresh_549 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy587 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy580 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy587] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy580 D R S_cls E))).fv) 0

theorem nb095_fresh_550 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy588 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy580 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy588] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy580 D R S_cls E))).fv) 1

theorem nb095_distinct_551 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy587 D R S_cls E) ≠ (nb095AlphaDummy588 D R S_cls E) := by
  simpa only [nb095AlphaDummy587, nb095AlphaDummy588] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy580 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_552 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy589 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy582 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy589] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy582 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_553 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy590 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy582 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy590] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy582 x u D R S_cls f E))).fv) 1

theorem nb095_distinct_554 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy589 x u D R S_cls f E) ≠
      (nb095AlphaDummy590 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy589, nb095AlphaDummy590] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy582 x u D R S_cls f E))).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_fresh_555 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy593 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy593] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_556 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy594 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy594] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_557 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy595 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy595] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_558 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy593 D R S_cls E) ≠ (nb095AlphaDummy594 D R S_cls E) := by
  simpa only [nb095AlphaDummy593, nb095AlphaDummy594] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_559 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy593 D R S_cls E) ≠ (nb095AlphaDummy595 D R S_cls E) := by
  simpa only [nb095AlphaDummy593, nb095AlphaDummy595] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_560 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy594 D R S_cls E) ≠ (nb095AlphaDummy595 D R S_cls E) := by
  simpa only [nb095AlphaDummy594, nb095AlphaDummy595] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_561 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy596 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy596] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_562 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy597 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy597] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_563 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy598 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy598] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_564 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy596 x u D R S_cls f E) ≠
      (nb095AlphaDummy597 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy596, nb095AlphaDummy597] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_565 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy596 x u D R S_cls f E) ≠
      (nb095AlphaDummy598 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy596, nb095AlphaDummy598] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_566 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy597 x u D R S_cls f E) ≠
      (nb095AlphaDummy598 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy597, nb095AlphaDummy598] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_567 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy605 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy605] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv)
      0

theorem nb095_fresh_568 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy601 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy601] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy594 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv)
      0

theorem nb095_fresh_569 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy607 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy607] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy595 D R S_cls E))).fv)
      0

theorem nb095_fresh_570 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy606 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy606] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_571 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy602 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy602] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_572 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy608 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy608] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy598 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_573 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy625 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy619 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy625] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy619 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv)
      0

theorem nb095_fresh_574 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy626 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy619 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy626] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy619 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv)
      1

theorem nb095_distinct_575 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy625 D R S_cls E) ≠ (nb095AlphaDummy626 D R S_cls E) := by
  simpa only [nb095AlphaDummy625, nb095AlphaDummy626] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy619 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_576 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy627 x D R) ∉
      (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy622 x D R))).fv) :=
  by
  simpa only [nb095AlphaDummy627] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy622 x D R))).fv)
      0

theorem nb095_fresh_577 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy628 x D R) ∉
      (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy622 x D R))).fv) :=
  by
  simpa only [nb095AlphaDummy628] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy622 x D R))).fv)
      1

theorem nb095_distinct_578 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy627 x D R) ≠ (nb095AlphaDummy628 x D R) := by
  simpa only [nb095AlphaDummy627, nb095AlphaDummy628] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy622 x D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_579 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy633 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy633] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) 0

theorem nb095_fresh_580 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy634 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy634] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) 1

theorem nb095_distinct_581 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy633 D R S_cls E) ≠ (nb095AlphaDummy634 D R S_cls E) := by
  simpa only [nb095AlphaDummy633, nb095AlphaDummy634] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_582 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy635 x D R) ∉ (((Class.cv (nb095AlphaDummy628 x D R))).fv) := by
  simpa only [nb095AlphaDummy635] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy628 x D R))).fv) 0

theorem nb095_fresh_583 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy636 x D R) ∉ (((Class.cv (nb095AlphaDummy628 x D R))).fv) := by
  simpa only [nb095AlphaDummy636] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy628 x D R))).fv) 1

theorem nb095_distinct_584 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy636 x D R) := by
  simpa only [nb095AlphaDummy635, nb095AlphaDummy636] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy628 x D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_585 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy639 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy639] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_586 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy640 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy640] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_587 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy641 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy641] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_588 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy639 D R S_cls E) ≠ (nb095AlphaDummy640 D R S_cls E) := by
  simpa only [nb095AlphaDummy639, nb095AlphaDummy640] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_589 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy639 D R S_cls E) ≠ (nb095AlphaDummy641 D R S_cls E) := by
  simpa only [nb095AlphaDummy639, nb095AlphaDummy641] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_590 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy641 D R S_cls E) := by
  simpa only [nb095AlphaDummy640, nb095AlphaDummy641] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_591 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy642 x D R) ∉
      (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy642] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_592 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy643 x D R) ∉
      (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy643] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_593 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy644 x D R) ∉
      (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy644] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_594 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy642 x D R) ≠ (nb095AlphaDummy643 x D R) := by
  simpa only [nb095AlphaDummy642, nb095AlphaDummy643] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_distinct_595 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy642 x D R) ≠ (nb095AlphaDummy644 x D R) := by
  simpa only [nb095AlphaDummy642, nb095AlphaDummy644] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb095_distinct_596 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy644 x D R) := by
  simpa only [nb095AlphaDummy643, nb095AlphaDummy644] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb095_fresh_597 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy651 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy651] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv)
      0

theorem nb095_fresh_598 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy647 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy647] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy640 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv)
      0

theorem nb095_fresh_599 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy653 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy653] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy641 D R S_cls E))).fv)
      0

theorem nb095_fresh_600 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy652 x D R) ∉
      (((Class.cv (nb095AlphaDummy643 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy643 x D R))).fv) :=
  by
  simpa only [nb095AlphaDummy652] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy643 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy643 x D R))).fv)
      0

theorem nb095_fresh_601 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy648 x D R) ∉
      (((Class.cv (nb095AlphaDummy643 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy644 x D R))).fv) :=
  by
  simpa only [nb095AlphaDummy648] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy643 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy644 x D R))).fv)
      0

theorem nb095_fresh_602 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy654 x D R) ∉
      (((Class.cv (nb095AlphaDummy644 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy644 x D R))).fv) :=
  by
  simpa only [nb095AlphaDummy654] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy644 x D R))).fv ∪
        ((Class.cv (nb095AlphaDummy644 x D R))).fv)
      0

theorem nb095_fresh_603 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy715 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy662 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy715] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy662 D R S_cls E))).fv) 0

theorem nb095_fresh_604 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy716 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy662 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy716] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy662 D R S_cls E))).fv) 1

theorem nb095_distinct_605 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy715 D R S_cls E) ≠ (nb095AlphaDummy716 D R S_cls E) := by
  simpa only [nb095AlphaDummy715, nb095AlphaDummy716] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy662 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_606 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy717 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy664 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy717] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy664 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_607 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy718 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy664 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy718] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy664 x u D R S_cls f E))).fv) 1

theorem nb095_distinct_608 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy717 x u D R S_cls f E) ≠
      (nb095AlphaDummy718 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy717, nb095AlphaDummy718] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy664 x u D R S_cls f E))).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_fresh_609 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy713 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy671 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy713] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy671 D R S_cls E))).fv) 0

theorem nb095_fresh_610 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy714 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy672 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy714] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy672 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_611 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy685 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy685] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) 0

theorem nb095_fresh_612 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy686 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy686] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) 1

theorem nb095_distinct_613 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy685 D R S_cls E) ≠ (nb095AlphaDummy686 D R S_cls E) := by
  simpa only [nb095AlphaDummy685, nb095AlphaDummy686] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_614 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy687 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy687] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_615 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy688 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy688] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv) 1

theorem nb095_distinct_616 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy687 x u D R S_cls f E) ≠
      (nb095AlphaDummy688 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy687, nb095AlphaDummy688] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_fresh_617 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy691 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy691] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_618 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy692 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy692] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_619 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy693 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy693] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_620 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy691 D R S_cls E) ≠ (nb095AlphaDummy692 D R S_cls E) := by
  simpa only [nb095AlphaDummy691, nb095AlphaDummy692] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_621 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy691 D R S_cls E) ≠ (nb095AlphaDummy693 D R S_cls E) := by
  simpa only [nb095AlphaDummy691, nb095AlphaDummy693] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_622 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy692 D R S_cls E) ≠ (nb095AlphaDummy693 D R S_cls E) := by
  simpa only [nb095AlphaDummy692, nb095AlphaDummy693] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_623 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy694 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy694] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_624 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy695 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy695] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_625 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy696 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy696] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_626 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy694 x u D R S_cls f E) ≠
      (nb095AlphaDummy695 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy694, nb095AlphaDummy695] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_627 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy694 x u D R S_cls f E) ≠
      (nb095AlphaDummy696 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy694, nb095AlphaDummy696] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_628 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy695 x u D R S_cls f E) ≠
      (nb095AlphaDummy696 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy695, nb095AlphaDummy696] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_629 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy703 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy703] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv)
      0

theorem nb095_fresh_630 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy699 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy699] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy692 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv)
      0

theorem nb095_fresh_631 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy705 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy705] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv)
      0

theorem nb095_fresh_632 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy704 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy704] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_633 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy700 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy700] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_634 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy706 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy706] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_635 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy721 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy721] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_636 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy722 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy722] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_637 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy723 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy723] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_638 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy721 D R S_cls E) ≠ (nb095AlphaDummy722 D R S_cls E) := by
  simpa only [nb095AlphaDummy721, nb095AlphaDummy722] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_639 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy721 D R S_cls E) ≠ (nb095AlphaDummy723 D R S_cls E) := by
  simpa only [nb095AlphaDummy721, nb095AlphaDummy723] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_640 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy722 D R S_cls E) ≠ (nb095AlphaDummy723 D R S_cls E) := by
  simpa only [nb095AlphaDummy722, nb095AlphaDummy723] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_641 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy724 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy724] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_642 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy725 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy725] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_643 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy726 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy726] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_644 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy724 x u D R S_cls f E) ≠
      (nb095AlphaDummy725 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy724, nb095AlphaDummy725] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_645 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy724 x u D R S_cls f E) ≠
      (nb095AlphaDummy726 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy724, nb095AlphaDummy726] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_646 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy725 x u D R S_cls f E) ≠
      (nb095AlphaDummy726 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy725, nb095AlphaDummy726] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_647 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy733 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy733] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv)
      0

theorem nb095_fresh_648 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy729 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy729] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

theorem nb095_fresh_649 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy735 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy735] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv)
      0

theorem nb095_fresh_650 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy734 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy734] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_651 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy730 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy730] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_652 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy736 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy736] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_653 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy783 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy741 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy783] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy741 D R S_cls E))).fv) 0

theorem nb095_fresh_654 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy784 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy742 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy784] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy742 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_655 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy755 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy755] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) 0

theorem nb095_fresh_656 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy756 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy756] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) 1

theorem nb095_distinct_657 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy755 D R S_cls E) ≠ (nb095AlphaDummy756 D R S_cls E) := by
  simpa only [nb095AlphaDummy755, nb095AlphaDummy756] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_658 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy757 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy757] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_659 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy758 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy758] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv) 1

theorem nb095_distinct_660 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy757 x u D R S_cls f E) ≠
      (nb095AlphaDummy758 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy757, nb095AlphaDummy758] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_fresh_661 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy761 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy761] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_662 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy762 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy762] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_663 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy763 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy763] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_664 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy761 D R S_cls E) ≠ (nb095AlphaDummy762 D R S_cls E) := by
  simpa only [nb095AlphaDummy761, nb095AlphaDummy762] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_665 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy761 D R S_cls E) ≠ (nb095AlphaDummy763 D R S_cls E) := by
  simpa only [nb095AlphaDummy761, nb095AlphaDummy763] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_666 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy762 D R S_cls E) ≠ (nb095AlphaDummy763 D R S_cls E) := by
  simpa only [nb095AlphaDummy762, nb095AlphaDummy763] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_667 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy764 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy764] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_668 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy765 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy765] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_669 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy766 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy766] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_670 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy764 x u D R S_cls f E) ≠
      (nb095AlphaDummy765 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy764, nb095AlphaDummy765] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_671 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy764 x u D R S_cls f E) ≠
      (nb095AlphaDummy766 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy764, nb095AlphaDummy766] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_672 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy765 x u D R S_cls f E) ≠
      (nb095AlphaDummy766 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy765, nb095AlphaDummy766] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_673 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy773 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy773] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv)
      0

theorem nb095_fresh_674 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy769 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy769] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv)
      0

theorem nb095_fresh_675 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy775 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy775] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv)
      0

theorem nb095_fresh_676 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy774 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy774] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_677 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy770 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy770] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_678 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy776 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy776] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_679 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy799 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy793 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy799] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy793 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv)
      0

theorem nb095_fresh_680 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy800 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy793 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy800] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy793 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv)
      1

theorem nb095_distinct_681 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy799 D R S_cls E) ≠ (nb095AlphaDummy800 D R S_cls E) := by
  simpa only [nb095AlphaDummy799, nb095AlphaDummy800] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy793 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_682 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy801 u S_cls E) ∉
      (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy796 u S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy801] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy796 u S_cls E))).fv)
      0

theorem nb095_fresh_683 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy802 u S_cls E) ∉
      (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy796 u S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy802] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy796 u S_cls E))).fv)
      1

theorem nb095_distinct_684 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy801 u S_cls E) ≠ (nb095AlphaDummy802 u S_cls E) := by
  simpa only [nb095AlphaDummy801, nb095AlphaDummy802] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy796 u S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_685 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy807 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy807] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) 0

theorem nb095_fresh_686 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy808 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy808] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) 1

theorem nb095_distinct_687 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy807 D R S_cls E) ≠ (nb095AlphaDummy808 D R S_cls E) := by
  simpa only [nb095AlphaDummy807, nb095AlphaDummy808] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_688 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy809 u S_cls E) ∉
      (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy809] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv) 0

theorem nb095_fresh_689 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy810 u S_cls E) ∉
      (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy810] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv) 1

theorem nb095_distinct_690 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy809 u S_cls E) ≠ (nb095AlphaDummy810 u S_cls E) := by
  simpa only [nb095AlphaDummy809, nb095AlphaDummy810] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb095_fresh_691 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy813 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy813] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_692 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy814 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy814] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_693 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy815 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy815] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_694 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy813 D R S_cls E) ≠ (nb095AlphaDummy814 D R S_cls E) := by
  simpa only [nb095AlphaDummy813, nb095AlphaDummy814] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_695 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy813 D R S_cls E) ≠ (nb095AlphaDummy815 D R S_cls E) := by
  simpa only [nb095AlphaDummy813, nb095AlphaDummy815] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_696 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy814 D R S_cls E) ≠ (nb095AlphaDummy815 D R S_cls E) := by
  simpa only [nb095AlphaDummy814, nb095AlphaDummy815] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_697 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy816 u S_cls E) ∉
      (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy816] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv)
      0

theorem nb095_fresh_698 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy817 u S_cls E) ∉
      (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy817] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv)
      1

theorem nb095_fresh_699 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy818 u S_cls E) ∉
      (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy818] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv)
      2

theorem nb095_distinct_700 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy816 u S_cls E) ≠ (nb095AlphaDummy817 u S_cls E) := by
  simpa only [nb095AlphaDummy816, nb095AlphaDummy817] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb095_distinct_701 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy816 u S_cls E) ≠ (nb095AlphaDummy818 u S_cls E) := by
  simpa only [nb095AlphaDummy816, nb095AlphaDummy818] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (i := 0) (j :=
      2) (by decide))

theorem nb095_distinct_702 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy818 u S_cls E) := by
  simpa only [nb095AlphaDummy817, nb095AlphaDummy818] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (i := 1) (j :=
      2) (by decide))

theorem nb095_fresh_703 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy825 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy825] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv)
      0

theorem nb095_fresh_704 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy821 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy821] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv)
      0

theorem nb095_fresh_705 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy827 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy827] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv)
      0

theorem nb095_fresh_706 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy826 u S_cls E) ∉
      (((Class.cv (nb095AlphaDummy817 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy817 u S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy826] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy817 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy817 u S_cls E))).fv)
      0

theorem nb095_fresh_707 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy822 u S_cls E) ∉
      (((Class.cv (nb095AlphaDummy817 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy818 u S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy822] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy817 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy818 u S_cls E))).fv)
      0

theorem nb095_fresh_708 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy828 u S_cls E) ∉
      (((Class.cv (nb095AlphaDummy818 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy818 u S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy828] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy818 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy818 u S_cls E))).fv)
      0

theorem nb095_fresh_709 (f : Var) : (nb095AlphaDummy093 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb095AlphaDummy093] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb095_fresh_710 (f : Var) : (nb095AlphaDummy094 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb095AlphaDummy094] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb095_distinct_711 (f : Var) :
    (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy094 f) := by
  simpa only [nb095AlphaDummy093, nb095AlphaDummy094] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_712 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy670 x u D R S_cls f E) ∉
      (((Class.cv f)).fv ∪ ((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy670] using
    freshVar_not_mem
      (((Class.cv f)).fv ∪ ((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_713 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy740 x u D R S_cls f E) ∉
      (((Class.cv f)).fv ∪ ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy740] using
    freshVar_not_mem
      (((Class.cv f)).fv ∪ ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_714 (f : Var) :
    (nb095AlphaDummy014 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb095AlphaDummy014] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0

theorem nb095_fresh_715 (f : Var) :
    (nb095AlphaDummy015 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb095AlphaDummy015] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1

theorem nb095_fresh_716 (f : Var) :
    (nb095AlphaDummy016 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb095AlphaDummy016] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2

theorem nb095_distinct_717 (f : Var) :
    (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy015 f) := by
  simpa only [nb095AlphaDummy014, nb095AlphaDummy015] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb095_distinct_718 (f : Var) :
    (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy016 f) := by
  simpa only [nb095AlphaDummy014, nb095AlphaDummy016] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb095_distinct_719 (f : Var) :
    (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy016 f) := by
  simpa only [nb095AlphaDummy015, nb095AlphaDummy016] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb095_fresh_720 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ∉
      (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                  (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv u))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv u))))).fv) :=
  by
  simpa only [nb095AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                  (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv u))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
      0

theorem nb095_fresh_721 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy006 x u D R S_cls f E) ∉
      (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                  (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv u))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv u))))).fv) :=
  by
  simpa only [nb095AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                  (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv u))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
      1

theorem nb095_distinct_722 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ≠
      (nb095AlphaDummy006 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy005, nb095AlphaDummy006] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                  (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv u))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_723 (f : Var) :
    (nb095AlphaDummy297 f) ∉ (((Class.cv f)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb095AlphaDummy297] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCvv)).fv) 0

theorem nb095_fresh_724 (f : Var) :
    (nb095AlphaDummy298 f) ∉ (((Class.cv f)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb095AlphaDummy298] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCvv)).fv) 1

theorem nb095_distinct_725 (f : Var) :
    (nb095AlphaDummy297 f) ≠ (nb095AlphaDummy298 f) := by
  simpa only [nb095AlphaDummy297, nb095AlphaDummy298] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_726 (u : Var) : (nb095AlphaDummy344 u) ∉ (((Class.cv u)).fv) := by
  simpa only [nb095AlphaDummy344] using freshVar_not_mem (((Class.cv u)).fv) 0

theorem nb095_fresh_727 (x : Var) : (nb095AlphaDummy254 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb095AlphaDummy254] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb095_fresh_728 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy031 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy027 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy027 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy031] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy027 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy027 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv)
      0

theorem nb095_fresh_729 (f : Var) :
    (nb095AlphaDummy032 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy029 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy029 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy029 f))).fv) :=
  by
  simpa only [nb095AlphaDummy032] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy029 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy029 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy029 f))).fv)
      0

theorem nb095_fresh_730 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy067 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy063 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy063 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy067] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy063 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy063 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv)
      0

theorem nb095_fresh_731 (f : Var) :
    (nb095AlphaDummy068 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy065 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy065 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy065 f))).fv) :=
  by
  simpa only [nb095AlphaDummy068] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy065 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy065 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy065 f))).fv)
      0

theorem nb095_fresh_732 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy109 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy105 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy105 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy109] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy105 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy105 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv)
      0

theorem nb095_fresh_733 (f : Var) :
    (nb095AlphaDummy110 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy107 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy107 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy107 f))).fv) :=
  by
  simpa only [nb095AlphaDummy110] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy107 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy107 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy107 f))).fv)
      0

theorem nb095_fresh_734 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy145 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy141 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy141 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy145] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy141 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy141 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv)
      0

theorem nb095_fresh_735 (f : Var) :
    (nb095AlphaDummy146 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy143 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy143 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy143 f))).fv) :=
  by
  simpa only [nb095AlphaDummy146] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy143 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy143 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy143 f))).fv)
      0

theorem nb095_fresh_736 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy181 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy177 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy177 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy181] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy177 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy177 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv)
      0

theorem nb095_fresh_737 (f : Var) :
    (nb095AlphaDummy182 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy179 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy179 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy179 f))).fv) :=
  by
  simpa only [nb095AlphaDummy182] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy179 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy179 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy179 f))).fv)
      0

theorem nb095_fresh_738 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy221 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy217 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy217 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy221] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy217 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy217 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv)
      0

theorem nb095_fresh_739 (f : Var) :
    (nb095AlphaDummy222 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy219 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy219 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy219 f))).fv) :=
  by
  simpa only [nb095AlphaDummy222] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy219 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy219 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy219 f))).fv)
      0

theorem nb095_fresh_740 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy267 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy263 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy263 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy267] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy263 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy263 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv)
      0

theorem nb095_fresh_741 (x : Var) (R : Class) :
    (nb095AlphaDummy268 x R) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy265 x R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy265 x R)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy265 x R))).fv) :=
  by
  simpa only [nb095AlphaDummy268] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy265 x R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy265 x R)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy265 x R))).fv)
      0

theorem nb095_fresh_742 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy311 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy307 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy307 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy311] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy307 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy307 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv)
      0

theorem nb095_fresh_743 (f : Var) :
    (nb095AlphaDummy312 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy309 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy309 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy309 f))).fv) :=
  by
  simpa only [nb095AlphaDummy312] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy309 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy309 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy309 f))).fv)
      0

theorem nb095_fresh_744 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy357 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy353 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy353 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy357] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy353 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy353 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv)
      0

theorem nb095_fresh_745 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy358 u S_cls) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy355 u S_cls)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy355 u S_cls)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy355 u S_cls))).fv) :=
  by
  simpa only [nb095AlphaDummy358] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy355 u S_cls)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy355 u S_cls)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy355 u S_cls))).fv)
      0

theorem nb095_fresh_746 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy405 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy401 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy401 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy405] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy401 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy401 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv)
      0

theorem nb095_fresh_747 (f : Var) :
    (nb095AlphaDummy406 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy403 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy403 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy403 f))).fv) :=
  by
  simpa only [nb095AlphaDummy406] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy403 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy403 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy403 f))).fv)
      0

theorem nb095_fresh_748 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy441 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy437 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy437 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy441] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy437 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy437 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv)
      0

theorem nb095_fresh_749 (f : Var) :
    (nb095AlphaDummy442 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy439 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy439 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy439 f))).fv) :=
  by
  simpa only [nb095AlphaDummy442] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy439 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy439 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy439 f))).fv)
      0

theorem nb095_fresh_750 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy483 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy479 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy479 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy483] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy479 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy479 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv)
      0

theorem nb095_fresh_751 (f : Var) :
    (nb095AlphaDummy484 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy481 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy481 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy481 f))).fv) :=
  by
  simpa only [nb095AlphaDummy484] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy481 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy481 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy481 f))).fv)
      0

theorem nb095_fresh_752 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy519 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy515 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy515 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy519] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy515 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy515 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy515 D R S_cls E))).fv)
      0

theorem nb095_fresh_753 (f : Var) :
    (nb095AlphaDummy520 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy517 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy517 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy517 f))).fv) :=
  by
  simpa only [nb095AlphaDummy520] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy517 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy517 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy517 f))).fv)
      0

theorem nb095_fresh_754 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy555 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy551 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy551 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy555] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy551 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy551 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy551 D R S_cls E))).fv)
      0

theorem nb095_fresh_755 (f : Var) :
    (nb095AlphaDummy556 f) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy553 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy553 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy553 f))).fv) :=
  by
  simpa only [nb095AlphaDummy556] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy553 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy553 f)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy553 f))).fv)
      0

theorem nb095_fresh_756 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy591 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy587 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy587 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy591] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy587 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy587 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy587 D R S_cls E))).fv)
      0

theorem nb095_fresh_757 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy592 x u D R S_cls f E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy589 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy589 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy592] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy589 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy589 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_758 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy637 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy633 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy633 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy637] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy633 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy633 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv)
      0

theorem nb095_fresh_759 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy638 x D R) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy635 x D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy635 x D R)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy635 x D R))).fv) :=
  by
  simpa only [nb095AlphaDummy638] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy635 x D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy635 x D R)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy635 x D R))).fv)
      0

theorem nb095_fresh_760 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy689 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy685 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy685 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy689] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy685 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy685 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv)
      0

theorem nb095_fresh_761 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy690 x u D R S_cls f E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy687 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy687 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy690] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy687 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy687 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_762 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy719 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy715 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy715 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy719] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy715 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy715 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv)
      0

theorem nb095_fresh_763 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy720 x u D R S_cls f E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy717 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy717 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy720] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy717 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy717 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_764 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy759 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy759] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv)
      0

theorem nb095_fresh_765 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy760 x u D R S_cls f E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy757 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy757 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy760] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy757 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy757 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_766 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy811 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy807 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy807 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy811] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy807 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy807 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv)
      0

theorem nb095_fresh_767 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy812 u S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy809 u S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy809 u S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy809 u S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy812] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy809 u S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy809 u S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy809 u S_cls E))).fv)
      0

theorem nb095_fresh_768 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy465 D R S_cls E) ∉
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy465] using
    freshVar_not_mem (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) 0

theorem nb095_fresh_769 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy466 D R S_cls E) ∉
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy466] using
    freshVar_not_mem (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) 1

theorem nb095_distinct_770 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy465 D R S_cls E) ≠ (nb095AlphaDummy466 D R S_cls E) := by
  simpa only [nb095AlphaDummy465, nb095AlphaDummy466] using
    (freshVar_injective (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_771 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy385 D R S_cls E) ∉
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv) :=
  by
  simpa only [nb095AlphaDummy385] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv)
      0

theorem nb095_fresh_772 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy386 D R S_cls E) ∉
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv) :=
  by
  simpa only [nb095AlphaDummy386] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv)
      1

theorem nb095_fresh_773 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy387 D R S_cls E) ∉
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv) :=
  by
  simpa only [nb095AlphaDummy387] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv)
      2

theorem nb095_distinct_774 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy385 D R S_cls E) ≠ (nb095AlphaDummy386 D R S_cls E) := by
  simpa only [nb095AlphaDummy385, nb095AlphaDummy386] using
    (freshVar_injective (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_distinct_775 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy385 D R S_cls E) ≠ (nb095AlphaDummy387 D R S_cls E) := by
  simpa only [nb095AlphaDummy385, nb095AlphaDummy387] using
    (freshVar_injective (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb095_distinct_776 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy387 D R S_cls E) := by
  simpa only [nb095AlphaDummy386, nb095AlphaDummy387] using
    (freshVar_injective (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb095_fresh_777 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy205 D R S_cls E) ∉
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb095AlphaDummy205] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCvv)).fv) 0

theorem nb095_fresh_778 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy206 D R S_cls E) ∉
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb095AlphaDummy206] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCvv)).fv) 1

theorem nb095_distinct_779 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy205 D R S_cls E) ≠ (nb095AlphaDummy206 D R S_cls E) := by
  simpa only [nb095AlphaDummy205, nb095AlphaDummy206] using
    (freshVar_injective
      (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCvv)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_780 (f : Var) :
    (nb095AlphaDummy467 f) ∉ (((synCcnv (Class.cv f))).fv) := by
  simpa only [nb095AlphaDummy467] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv) 0

theorem nb095_fresh_781 (f : Var) :
    (nb095AlphaDummy468 f) ∉ (((synCcnv (Class.cv f))).fv) := by
  simpa only [nb095AlphaDummy468] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv) 1

theorem nb095_distinct_782 (f : Var) :
    (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy468 f) := by
  simpa only [nb095AlphaDummy467, nb095AlphaDummy468] using
    (freshVar_injective (((synCcnv (Class.cv f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_783 (f : Var) :
    (nb095AlphaDummy388 f) ∉
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) :=
  by
  simpa only [nb095AlphaDummy388] using
    freshVar_not_mem
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 0

theorem nb095_fresh_784 (f : Var) :
    (nb095AlphaDummy389 f) ∉
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) :=
  by
  simpa only [nb095AlphaDummy389] using
    freshVar_not_mem
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 1

theorem nb095_fresh_785 (f : Var) :
    (nb095AlphaDummy390 f) ∉
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) :=
  by
  simpa only [nb095AlphaDummy390] using
    freshVar_not_mem
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 2

theorem nb095_distinct_786 (f : Var) :
    (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy389 f) := by
  simpa only [nb095AlphaDummy388, nb095AlphaDummy389] using
    (freshVar_injective
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_787 (f : Var) :
    (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy390 f) := by
  simpa only [nb095AlphaDummy388, nb095AlphaDummy390] using
    (freshVar_injective
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_788 (f : Var) :
    (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy390 f) := by
  simpa only [nb095AlphaDummy389, nb095AlphaDummy390] using
    (freshVar_injective
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (i := 1)
      (j := 2) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
