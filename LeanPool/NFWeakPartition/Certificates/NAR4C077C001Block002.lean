/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part006`. -/


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

theorem nb077_fresh_356 (F : Class) (I : Class) :
    (nb077AlphaDummy305 F I) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy296 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy297 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy305] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy296 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy297 F I)))).fv)
      0

theorem nb077_fresh_357 (x : Var) :
    (nb077AlphaDummy306 x) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy299 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy300 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy306] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy299 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy300 x)))).fv)
      0

theorem nb077_fresh_358 (F : Class) (I : Class) :
    (nb077AlphaDummy335 F I) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy326 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy327 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy335] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy326 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy327 F I)))).fv)
      0

theorem nb077_fresh_359 (x : Var) :
    (nb077AlphaDummy336 x) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy329 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy330 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy336] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy329 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy330 x)))).fv)
      0

theorem nb077_fresh_360 (F : Class) (I : Class) :
    (nb077AlphaDummy051 F I) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy020 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy051] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy020 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_361 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy052 x F I) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy022 x F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy052] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy022 x F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_362 (F : Class) (I : Class) :
    (nb077AlphaDummy099 F I) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy068 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy099] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy068 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_363 (x : Var) :
    (nb077AlphaDummy100 x) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy070 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy100] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy070 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_364 (F : Class) (I : Class) :
    (nb077AlphaDummy135 F I) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy104 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy135] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy104 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_365 (x : Var) :
    (nb077AlphaDummy136 x) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy106 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy136] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy106 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_366 (F : Class) (I : Class) :
    (nb077AlphaDummy179 F I) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy148 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy179] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy148 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_367 (x : Var) :
    (nb077AlphaDummy180 x) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy150 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy180] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy150 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_368 (F : Class) (I : Class) :
    (nb077AlphaDummy215 F I) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy184 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy215] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy184 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_369 (x : Var) :
    (nb077AlphaDummy216 x) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy186 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy216] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy186 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_370 (F : Class) (I : Class) :
    (nb077AlphaDummy251 F I) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy220 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy251] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy220 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_371 (x : Var) :
    (nb077AlphaDummy252 x) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy222 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy252] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy222 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_372 (F : Class) (I : Class) :
    (nb077AlphaDummy291 F I) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy260 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy291] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy260 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_373 (x : Var) :
    (nb077AlphaDummy292 x) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy262 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy292] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy262 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_374 (F : Class) (I : Class) :
    (nb077AlphaDummy343 F I) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy312 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy343] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy312 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_375 (x : Var) :
    (nb077AlphaDummy344 x) ∉
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy314 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb077AlphaDummy344] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy314 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb077_fresh_376 (F : Class) (I : Class) :
    (nb077AlphaDummy013 F I) ∉
      (((synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I)))).fv ∪
        ((Class.cv (nb077AlphaDummy001 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy013] using
    freshVar_not_mem
      (((synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I)))).fv ∪
        ((Class.cv (nb077AlphaDummy001 F I))).fv)
      0

theorem nb077_fresh_377 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy014 x F I) ∉
      (((synCima (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪
        ((Class.cv (nb077AlphaDummy002 x F I))).fv) :=
  by
  simpa only [nb077AlphaDummy014] using
    freshVar_not_mem
      (((synCima (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪
        ((Class.cv (nb077AlphaDummy002 x F I))).fv)
      0

theorem nb077_fresh_378 (F : Class) (I : Class) :
    (nb077AlphaDummy139 F I) ∉
      (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪
        ((synC1st)).fv) :=
  by
  simpa only [nb077AlphaDummy139] using
    freshVar_not_mem
      (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪ ((synC1st)).fv)
      0

theorem nb077_fresh_379 (F : Class) (I : Class) :
    (nb077AlphaDummy140 F I) ∉
      (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪
        ((synC1st)).fv) :=
  by
  simpa only [nb077AlphaDummy140] using
    freshVar_not_mem
      (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪ ((synC1st)).fv)
      1

theorem nb077_fresh_380 (F : Class) (I : Class) :
    (nb077AlphaDummy141 F I) ∉
      (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪
        ((synC1st)).fv) :=
  by
  simpa only [nb077AlphaDummy141] using
    freshVar_not_mem
      (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪ ((synC1st)).fv)
      2

theorem nb077_distinct_381 (F : Class) (I : Class) :
    (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy140 F I) := by
  simpa only [nb077AlphaDummy139, nb077AlphaDummy140] using
    (freshVar_injective (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪ ((synC1st)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_382 (F : Class) (I : Class) :
    (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy141 F I) := by
  simpa only [nb077AlphaDummy139, nb077AlphaDummy141] using
    (freshVar_injective (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪ ((synC1st)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_383 (F : Class) (I : Class) :
    (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy141 F I) := by
  simpa only [nb077AlphaDummy140, nb077AlphaDummy141] using
    (freshVar_injective (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪ ((synC1st)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_384 (x : Var) :
    (nb077AlphaDummy142 x) ∉
      (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv) :=
  by
  simpa only [nb077AlphaDummy142] using
    freshVar_not_mem
      (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv) 0

theorem nb077_fresh_385 (x : Var) :
    (nb077AlphaDummy143 x) ∉
      (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv) :=
  by
  simpa only [nb077AlphaDummy143] using
    freshVar_not_mem
      (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv) 1

theorem nb077_fresh_386 (x : Var) :
    (nb077AlphaDummy144 x) ∉
      (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv) :=
  by
  simpa only [nb077AlphaDummy144] using
    freshVar_not_mem
      (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv) 2

theorem nb077_distinct_387 (x : Var) :
    (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy143 x) := by
  simpa only [nb077AlphaDummy142, nb077AlphaDummy143] using
    (freshVar_injective
      (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_388 (x : Var) :
    (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy144 x) := by
  simpa only [nb077AlphaDummy142, nb077AlphaDummy144] using
    (freshVar_injective
      (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_389 (x : Var) :
    (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy144 x) := by
  simpa only [nb077AlphaDummy143, nb077AlphaDummy144] using
    (freshVar_injective
      (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_390 (F : Class) (I : Class) :
    (nb077AlphaDummy039 F I) ∉
      (((synCnin (Class.cv (nb077AlphaDummy034 F I))
            (Class.cv (nb077AlphaDummy035 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy034 F I))
            (Class.cv (nb077AlphaDummy035 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy039] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy034 F I))
            (Class.cv (nb077AlphaDummy035 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy034 F I))
            (Class.cv (nb077AlphaDummy035 F I)))).fv)
      0

theorem nb077_fresh_391 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy040 x F I) ∉
      (((synCnin (Class.cv (nb077AlphaDummy037 x F I))
            (Class.cv (nb077AlphaDummy038 x F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy037 x F I))
            (Class.cv (nb077AlphaDummy038 x F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy040] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy037 x F I))
            (Class.cv (nb077AlphaDummy038 x F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy037 x F I))
            (Class.cv (nb077AlphaDummy038 x F I)))).fv)
      0

theorem nb077_fresh_392 (F : Class) (I : Class) :
    (nb077AlphaDummy087 F I) ∉
      (((synCnin (Class.cv (nb077AlphaDummy082 F I))
            (Class.cv (nb077AlphaDummy083 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy082 F I))
            (Class.cv (nb077AlphaDummy083 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy087] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy082 F I))
            (Class.cv (nb077AlphaDummy083 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy082 F I))
            (Class.cv (nb077AlphaDummy083 F I)))).fv)
      0

theorem nb077_fresh_393 (x : Var) :
    (nb077AlphaDummy088 x) ∉
      (((synCnin (Class.cv (nb077AlphaDummy085 x))
            (Class.cv (nb077AlphaDummy086 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy085 x))
            (Class.cv (nb077AlphaDummy086 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy088] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy085 x))
            (Class.cv (nb077AlphaDummy086 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy085 x))
            (Class.cv (nb077AlphaDummy086 x)))).fv)
      0

theorem nb077_fresh_394 (F : Class) (I : Class) :
    (nb077AlphaDummy123 F I) ∉
      (((synCnin (Class.cv (nb077AlphaDummy118 F I))
            (Class.cv (nb077AlphaDummy119 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy118 F I))
            (Class.cv (nb077AlphaDummy119 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy123] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy118 F I))
            (Class.cv (nb077AlphaDummy119 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy118 F I))
            (Class.cv (nb077AlphaDummy119 F I)))).fv)
      0

theorem nb077_fresh_395 (x : Var) :
    (nb077AlphaDummy124 x) ∉
      (((synCnin (Class.cv (nb077AlphaDummy121 x))
            (Class.cv (nb077AlphaDummy122 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy121 x))
            (Class.cv (nb077AlphaDummy122 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy124] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy121 x))
            (Class.cv (nb077AlphaDummy122 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy121 x))
            (Class.cv (nb077AlphaDummy122 x)))).fv)
      0

theorem nb077_fresh_396 (F : Class) (I : Class) :
    (nb077AlphaDummy167 F I) ∉
      (((synCnin (Class.cv (nb077AlphaDummy162 F I))
            (Class.cv (nb077AlphaDummy163 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy162 F I))
            (Class.cv (nb077AlphaDummy163 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy167] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy162 F I))
            (Class.cv (nb077AlphaDummy163 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy162 F I))
            (Class.cv (nb077AlphaDummy163 F I)))).fv)
      0

theorem nb077_fresh_397 (x : Var) :
    (nb077AlphaDummy168 x) ∉
      (((synCnin (Class.cv (nb077AlphaDummy165 x))
            (Class.cv (nb077AlphaDummy166 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy165 x))
            (Class.cv (nb077AlphaDummy166 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy168] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy165 x))
            (Class.cv (nb077AlphaDummy166 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy165 x))
            (Class.cv (nb077AlphaDummy166 x)))).fv)
      0

theorem nb077_fresh_398 (F : Class) (I : Class) :
    (nb077AlphaDummy203 F I) ∉
      (((synCnin (Class.cv (nb077AlphaDummy198 F I))
            (Class.cv (nb077AlphaDummy199 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy198 F I))
            (Class.cv (nb077AlphaDummy199 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy203] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy198 F I))
            (Class.cv (nb077AlphaDummy199 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy198 F I))
            (Class.cv (nb077AlphaDummy199 F I)))).fv)
      0

theorem nb077_fresh_399 (x : Var) :
    (nb077AlphaDummy204 x) ∉
      (((synCnin (Class.cv (nb077AlphaDummy201 x))
            (Class.cv (nb077AlphaDummy202 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy201 x))
            (Class.cv (nb077AlphaDummy202 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy204] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy201 x))
            (Class.cv (nb077AlphaDummy202 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy201 x))
            (Class.cv (nb077AlphaDummy202 x)))).fv)
      0

theorem nb077_fresh_400 (F : Class) (I : Class) :
    (nb077AlphaDummy239 F I) ∉
      (((synCnin (Class.cv (nb077AlphaDummy234 F I))
            (Class.cv (nb077AlphaDummy235 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy234 F I))
            (Class.cv (nb077AlphaDummy235 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy239] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy234 F I))
            (Class.cv (nb077AlphaDummy235 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy234 F I))
            (Class.cv (nb077AlphaDummy235 F I)))).fv)
      0

theorem nb077_fresh_401 (x : Var) :
    (nb077AlphaDummy240 x) ∉
      (((synCnin (Class.cv (nb077AlphaDummy237 x))
            (Class.cv (nb077AlphaDummy238 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy237 x))
            (Class.cv (nb077AlphaDummy238 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy240] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy237 x))
            (Class.cv (nb077AlphaDummy238 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy237 x))
            (Class.cv (nb077AlphaDummy238 x)))).fv)
      0

theorem nb077_fresh_402 (F : Class) (I : Class) :
    (nb077AlphaDummy279 F I) ∉
      (((synCnin (Class.cv (nb077AlphaDummy274 F I))
            (Class.cv (nb077AlphaDummy275 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy274 F I))
            (Class.cv (nb077AlphaDummy275 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy279] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy274 F I))
            (Class.cv (nb077AlphaDummy275 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy274 F I))
            (Class.cv (nb077AlphaDummy275 F I)))).fv)
      0

theorem nb077_fresh_403 (x : Var) :
    (nb077AlphaDummy280 x) ∉
      (((synCnin (Class.cv (nb077AlphaDummy277 x))
            (Class.cv (nb077AlphaDummy278 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy277 x))
            (Class.cv (nb077AlphaDummy278 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy280] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy277 x))
            (Class.cv (nb077AlphaDummy278 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy277 x))
            (Class.cv (nb077AlphaDummy278 x)))).fv)
      0

theorem nb077_fresh_404 (F : Class) (I : Class) :
    (nb077AlphaDummy301 F I) ∉
      (((synCnin (Class.cv (nb077AlphaDummy296 F I))
            (Class.cv (nb077AlphaDummy297 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy296 F I))
            (Class.cv (nb077AlphaDummy297 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy301] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy296 F I))
            (Class.cv (nb077AlphaDummy297 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy296 F I))
            (Class.cv (nb077AlphaDummy297 F I)))).fv)
      0

theorem nb077_fresh_405 (x : Var) :
    (nb077AlphaDummy302 x) ∉
      (((synCnin (Class.cv (nb077AlphaDummy299 x))
            (Class.cv (nb077AlphaDummy300 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy299 x))
            (Class.cv (nb077AlphaDummy300 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy302] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy299 x))
            (Class.cv (nb077AlphaDummy300 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy299 x))
            (Class.cv (nb077AlphaDummy300 x)))).fv)
      0

theorem nb077_fresh_406 (F : Class) (I : Class) :
    (nb077AlphaDummy331 F I) ∉
      (((synCnin (Class.cv (nb077AlphaDummy326 F I))
            (Class.cv (nb077AlphaDummy327 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy326 F I))
            (Class.cv (nb077AlphaDummy327 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy331] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy326 F I))
            (Class.cv (nb077AlphaDummy327 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy326 F I))
            (Class.cv (nb077AlphaDummy327 F I)))).fv)
      0

theorem nb077_fresh_407 (x : Var) :
    (nb077AlphaDummy332 x) ∉
      (((synCnin (Class.cv (nb077AlphaDummy329 x))
            (Class.cv (nb077AlphaDummy330 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy329 x))
            (Class.cv (nb077AlphaDummy330 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy332] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb077AlphaDummy329 x))
            (Class.cv (nb077AlphaDummy330 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy329 x))
            (Class.cv (nb077AlphaDummy330 x)))).fv)
      0

theorem nb077_fresh_408 (F : Class) (I : Class) :
    (nb077AlphaDummy055 F I) ∉
      (((synCnin (synCcom (synCcnv (synC1st)) (synCcom
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))
            (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv ∪ ((synCnin
            (synCcom (synCcnv (synC1st)) (synCcom
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))
            (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv) :=
  by
  simpa only [nb077AlphaDummy055] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (synC1st)) (synCcom
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))
            (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv ∪ ((synCnin
            (synCcom (synCcnv (synC1st)) (synCcom
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))
            (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv)
      0

theorem nb077_fresh_409 (x : Var) (F : Class) :
    (nb077AlphaDummy056 x F) ∉
      (((synCnin (synCcom (synCcnv (synC1st))
              (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))
            (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv ∪ ((synCnin
            (synCcom (synCcnv (synC1st))
              (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))
            (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv) :=
  by
  simpa only [nb077AlphaDummy056] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (synC1st))
              (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))
            (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv ∪ ((synCnin
            (synCcom (synCcnv (synC1st))
              (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))
            (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv)
      0

theorem nb077_fresh_410 (F : Class) (I : Class) :
    (nb077AlphaDummy011 F I) ∉
      (((synCnin (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
              (Class.cv (nb077AlphaDummy001 F I)))
            (Class.cv (nb077AlphaDummy001 F I)))).fv ∪ ((synCnin (synCima (synCpprod
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
              (Class.cv (nb077AlphaDummy001 F I)))
            (Class.cv (nb077AlphaDummy001 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy011] using
    freshVar_not_mem
      (((synCnin (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
              (Class.cv (nb077AlphaDummy001 F I)))
            (Class.cv (nb077AlphaDummy001 F I)))).fv ∪ ((synCnin (synCima (synCpprod
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
              (Class.cv (nb077AlphaDummy001 F I)))
            (Class.cv (nb077AlphaDummy001 F I)))).fv)
      0

theorem nb077_fresh_411 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy012 x F I) ∉
      (((synCnin (synCima
              (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
              (Class.cv (nb077AlphaDummy002 x F I)))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪ ((synCnin (synCima
              (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
              (Class.cv (nb077AlphaDummy002 x F I)))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy012] using
    freshVar_not_mem
      (((synCnin (synCima
              (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
              (Class.cv (nb077AlphaDummy002 x F I)))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪ ((synCnin (synCima
              (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
              (Class.cv (nb077AlphaDummy002 x F I)))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv)
      0

theorem nb077_fresh_412 (F : Class) (I : Class) :
    (nb077AlphaDummy007 F I) ∉
      (((synCnin (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))).fv ∪
        ((synCnin (synCsn (synCop (synC0c) I))
            (Class.cv (nb077AlphaDummy001 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy007] using
    freshVar_not_mem
      (((synCnin (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))).fv ∪
        ((synCnin (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))).fv)
      0

theorem nb077_fresh_413 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy008 x F I) ∉
      (((synCnin (synCsn (synCop (synC0c) I))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪
        ((synCnin (synCsn (synCop (synC0c) I))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy008] using
    freshVar_not_mem
      (((synCnin (synCsn (synCop (synC0c) I))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪
        ((synCnin (synCsn (synCop (synC0c) I))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv)
      0

theorem nb077_fresh_414 (F : Class) (I : Class) :
    (nb077AlphaDummy053 F I) ∉
      (((synCphi (Class.cv (nb077AlphaDummy020 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy020 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy053] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy020 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy020 F I)))).fv)
      0

theorem nb077_fresh_415 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy054 x F I) ∉
      (((synCphi (Class.cv (nb077AlphaDummy022 x F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy022 x F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy054] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy022 x F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy022 x F I)))).fv)
      0

theorem nb077_fresh_416 (F : Class) (I : Class) :
    (nb077AlphaDummy101 F I) ∉
      (((synCphi (Class.cv (nb077AlphaDummy068 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy068 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy101] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy068 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy068 F I)))).fv)
      0

theorem nb077_fresh_417 (x : Var) :
    (nb077AlphaDummy102 x) ∉
      (((synCphi (Class.cv (nb077AlphaDummy070 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy070 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy102] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy070 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy070 x)))).fv)
      0

theorem nb077_fresh_418 (F : Class) (I : Class) :
    (nb077AlphaDummy137 F I) ∉
      (((synCphi (Class.cv (nb077AlphaDummy104 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy104 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy137] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy104 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy104 F I)))).fv)
      0

theorem nb077_fresh_419 (x : Var) :
    (nb077AlphaDummy138 x) ∉
      (((synCphi (Class.cv (nb077AlphaDummy106 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy106 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy138] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy106 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy106 x)))).fv)
      0

theorem nb077_fresh_420 (F : Class) (I : Class) :
    (nb077AlphaDummy181 F I) ∉
      (((synCphi (Class.cv (nb077AlphaDummy148 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy148 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy181] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy148 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy148 F I)))).fv)
      0

theorem nb077_fresh_421 (x : Var) :
    (nb077AlphaDummy182 x) ∉
      (((synCphi (Class.cv (nb077AlphaDummy150 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy150 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy182] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy150 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy150 x)))).fv)
      0

theorem nb077_fresh_422 (F : Class) (I : Class) :
    (nb077AlphaDummy217 F I) ∉
      (((synCphi (Class.cv (nb077AlphaDummy184 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy184 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy217] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy184 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy184 F I)))).fv)
      0

theorem nb077_fresh_423 (x : Var) :
    (nb077AlphaDummy218 x) ∉
      (((synCphi (Class.cv (nb077AlphaDummy186 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy186 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy218] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy186 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy186 x)))).fv)
      0

theorem nb077_fresh_424 (F : Class) (I : Class) :
    (nb077AlphaDummy253 F I) ∉
      (((synCphi (Class.cv (nb077AlphaDummy220 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy220 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy253] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy220 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy220 F I)))).fv)
      0

theorem nb077_fresh_425 (x : Var) :
    (nb077AlphaDummy254 x) ∉
      (((synCphi (Class.cv (nb077AlphaDummy222 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy222 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy254] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy222 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy222 x)))).fv)
      0

theorem nb077_fresh_426 (F : Class) (I : Class) :
    (nb077AlphaDummy293 F I) ∉
      (((synCphi (Class.cv (nb077AlphaDummy260 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy260 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy293] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy260 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy260 F I)))).fv)
      0

theorem nb077_fresh_427 (x : Var) :
    (nb077AlphaDummy294 x) ∉
      (((synCphi (Class.cv (nb077AlphaDummy262 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy262 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy294] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy262 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy262 x)))).fv)
      0

theorem nb077_fresh_428 (F : Class) (I : Class) :
    (nb077AlphaDummy345 F I) ∉
      (((synCphi (Class.cv (nb077AlphaDummy312 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy312 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy345] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy312 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy312 F I)))).fv)
      0

theorem nb077_fresh_429 (x : Var) :
    (nb077AlphaDummy346 x) ∉
      (((synCphi (Class.cv (nb077AlphaDummy314 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy314 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy346] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb077AlphaDummy314 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy314 x)))).fv)
      0

theorem nb077_fresh_430 (F : Class) (I : Class) :
    (nb077AlphaDummy015 F I) ∉
      (((synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy001 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy015] using
    freshVar_not_mem
      (((synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy001 F I))).fv)
      0

theorem nb077_fresh_431 (F : Class) (I : Class) :
    (nb077AlphaDummy016 F I) ∉
      (((synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy001 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy016] using
    freshVar_not_mem
      (((synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy001 F I))).fv)
      1

theorem nb077_distinct_432 (F : Class) (I : Class) :
    (nb077AlphaDummy015 F I) ≠ (nb077AlphaDummy016 F I) := by
  simpa only [nb077AlphaDummy015, nb077AlphaDummy016] using
    (freshVar_injective (((synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy001 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_433 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy017 x F I) ∉
      (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy002 x F I))).fv) :=
  by
  simpa only [nb077AlphaDummy017] using
    freshVar_not_mem
      (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy002 x F I))).fv)
      0

theorem nb077_fresh_434 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy018 x F I) ∉
      (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy002 x F I))).fv) :=
  by
  simpa only [nb077AlphaDummy018] using
    freshVar_not_mem
      (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy002 x F I))).fv)
      1

theorem nb077_distinct_435 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy018 x F I) := by
  simpa only [nb077AlphaDummy017, nb077AlphaDummy018] using
    (freshVar_injective
      (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy002 x F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_436 (F : Class) (I : Class) :
    (nb077AlphaDummy009 F I) ∉
      (((synCsn (synCop (synC0c) I))).fv ∪ ((Class.cv (nb077AlphaDummy001 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy009] using
    freshVar_not_mem
      (((synCsn (synCop (synC0c) I))).fv ∪ ((Class.cv (nb077AlphaDummy001 F I))).fv)
      0

theorem nb077_fresh_437 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy010 x F I) ∉
      (((synCsn (synCop (synC0c) I))).fv ∪ ((Class.cv (nb077AlphaDummy002 x F I))).fv) :=
  by
  simpa only [nb077AlphaDummy010] using
    freshVar_not_mem
      (((synCsn (synCop (synC0c) I))).fv ∪ ((Class.cv (nb077AlphaDummy002 x F I))).fv)
      0

theorem nb077_fresh_438 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∉
      (((synCsn (synCop (synC0c) I))).fv ∪ ((synCpprod
            (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv) :=
  by
  simpa only [nb077AlphaDummy001] using
    freshVar_not_mem
      (((synCsn (synCop (synC0c) I))).fv ∪ ((synCpprod
            (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv)
      0

theorem nb077_fresh_439 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∉
      (((synCsn (synCop (synC0c) I))).fv ∪
        ((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv) :=
  by
  simpa only [nb077AlphaDummy002] using
    freshVar_not_mem
      (((synCsn (synCop (synC0c) I))).fv ∪
        ((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv)
      0

theorem nb077_fresh_440 (F : Class) (I : Class) :
    (nb077AlphaDummy000 F I) ∉ ((F).fv ∪ (I).fv) := by
  simpa only [nb077AlphaDummy000] using freshVar_not_mem ((F).fv ∪ (I).fv) 0

theorem nb077_fresh_441 (F : Class) (I : Class) :
    (nb077AlphaDummy255 F I) ∉
      (({(nb077AlphaDummy000 F I)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))).fv) :=
  by
  simpa only [nb077AlphaDummy255] using
    freshVar_not_mem
      (({(nb077AlphaDummy000 F I)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))).fv)
      0

theorem nb077_fresh_442 (F : Class) (I : Class) :
    (nb077AlphaDummy257 F I) ∉
      (({(nb077AlphaDummy000 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy255 F I)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb077AlphaDummy000 F I)) (synCvv))
            (Wff.classEq (Class.cv (nb077AlphaDummy255 F I))
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))))).fv) :=
  by
  simpa only [nb077AlphaDummy257] using
    freshVar_not_mem
      (({(nb077AlphaDummy000 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy255 F I)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb077AlphaDummy000 F I)) (synCvv))
            (Wff.classEq (Class.cv (nb077AlphaDummy255 F I))
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))))).fv)
      0

theorem nb077_fresh_443 (F : Class) (I : Class) :
    (nb077AlphaDummy065 F I) ∉
      (({(nb077AlphaDummy059 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy060 F I)} : Finset Var) ∪ ((synWex (nb077AlphaDummy061 F I)
            (synWa (synWbr (Class.cv (nb077AlphaDummy059 F I)) (synCcom
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))
                (Class.cv (nb077AlphaDummy061 F I)))
              (synWbr (Class.cv (nb077AlphaDummy061 F I)) (synCcnv (synC1st))
                (Class.cv (nb077AlphaDummy060 F I)))))).fv) :=
  by
  simpa only [nb077AlphaDummy065] using
    freshVar_not_mem
      (({(nb077AlphaDummy059 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy060 F I)} : Finset Var) ∪ ((synWex (nb077AlphaDummy061 F I)
            (synWa (synWbr (Class.cv (nb077AlphaDummy059 F I)) (synCcom
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))
                (Class.cv (nb077AlphaDummy061 F I)))
              (synWbr (Class.cv (nb077AlphaDummy061 F I)) (synCcnv (synC1st))
                (Class.cv (nb077AlphaDummy060 F I)))))).fv)
      0

theorem nb077_fresh_444 (x : Var) :
    (nb077AlphaDummy066 x) ∉
      (({(nb077AlphaDummy062 x)} : Finset Var) ∪ ({(nb077AlphaDummy063 x)} : Finset Var) ∪
        ((synWex (nb077AlphaDummy064 x) (synWa
              (synWbr (Class.cv (nb077AlphaDummy062 x))
                (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))
                (Class.cv (nb077AlphaDummy064 x)))
              (synWbr (Class.cv (nb077AlphaDummy064 x)) (synCcnv (synC1st))
                (Class.cv (nb077AlphaDummy063 x)))))).fv) :=
  by
  simpa only [nb077AlphaDummy066] using
    freshVar_not_mem
      (({(nb077AlphaDummy062 x)} : Finset Var) ∪ ({(nb077AlphaDummy063 x)} : Finset Var) ∪
        ((synWex (nb077AlphaDummy064 x) (synWa
              (synWbr (Class.cv (nb077AlphaDummy062 x))
                (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))
                (Class.cv (nb077AlphaDummy064 x)))
              (synWbr (Class.cv (nb077AlphaDummy064 x)) (synCcnv (synC1st))
                (Class.cv (nb077AlphaDummy063 x)))))).fv)
      0

theorem nb077_fresh_445 (F : Class) (I : Class) :
    (nb077AlphaDummy145 F I) ∉
      (({(nb077AlphaDummy139 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy140 F I)} : Finset Var) ∪ ((synWex (nb077AlphaDummy141 F I)
            (synWa (synWbr (Class.cv (nb077AlphaDummy139 F I)) (synC1st)
                (Class.cv (nb077AlphaDummy141 F I)))
              (synWbr (Class.cv (nb077AlphaDummy141 F I))
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
                (Class.cv (nb077AlphaDummy140 F I)))))).fv) :=
  by
  simpa only [nb077AlphaDummy145] using
    freshVar_not_mem
      (({(nb077AlphaDummy139 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy140 F I)} : Finset Var) ∪ ((synWex (nb077AlphaDummy141 F I)
            (synWa (synWbr (Class.cv (nb077AlphaDummy139 F I)) (synC1st)
                (Class.cv (nb077AlphaDummy141 F I)))
              (synWbr (Class.cv (nb077AlphaDummy141 F I))
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
                (Class.cv (nb077AlphaDummy140 F I)))))).fv)
      0

theorem nb077_fresh_446 (x : Var) :
    (nb077AlphaDummy146 x) ∉
      (({(nb077AlphaDummy142 x)} : Finset Var) ∪ ({(nb077AlphaDummy143 x)} : Finset Var) ∪
        ((synWex (nb077AlphaDummy144 x) (synWa
              (synWbr (Class.cv (nb077AlphaDummy142 x)) (synC1st)
                (Class.cv (nb077AlphaDummy144 x)))
              (synWbr (Class.cv (nb077AlphaDummy144 x))
                (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
                (Class.cv (nb077AlphaDummy143 x)))))).fv) :=
  by
  simpa only [nb077AlphaDummy146] using
    freshVar_not_mem
      (({(nb077AlphaDummy142 x)} : Finset Var) ∪ ({(nb077AlphaDummy143 x)} : Finset Var) ∪
        ((synWex (nb077AlphaDummy144 x) (synWa
              (synWbr (Class.cv (nb077AlphaDummy142 x)) (synC1st)
                (Class.cv (nb077AlphaDummy144 x)))
              (synWbr (Class.cv (nb077AlphaDummy144 x))
                (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
                (Class.cv (nb077AlphaDummy143 x)))))).fv)
      0

theorem nb077_fresh_447 (x : Var) :
    (nb077AlphaDummy256 x) ∉
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCplc (Class.cv x) (synC1c))).fv) :=
  by
  simpa only [nb077AlphaDummy256] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCplc (Class.cv x) (synC1c))).fv) 0

theorem nb077_fresh_448 (x : Var) :
    (nb077AlphaDummy258 x) ∉
      (({ x } : Finset Var) ∪ ({(nb077AlphaDummy256 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb077AlphaDummy256 x))
              (synCplc (Class.cv x) (synC1c))))).fv) :=
  by
  simpa only [nb077AlphaDummy258] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({(nb077AlphaDummy256 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb077AlphaDummy256 x))
              (synCplc (Class.cv x) (synC1c))))).fv)
      0

theorem nb077_support_mem_0000 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∈
      (((synCnin (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))).fv ∪
        ((synCnin (synCsn (synCop (synC0c) I))
            (Class.cv (nb077AlphaDummy001 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0001 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∈
      (((synCnin (synCsn (synCop (synC0c) I))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪
        ((synCnin (synCsn (synCop (synC0c) I))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0002 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∈
      (((synCsn (synCop (synC0c) I))).fv ∪ ((Class.cv (nb077AlphaDummy001 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0003 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∈
      (((synCsn (synCop (synC0c) I))).fv ∪ ((Class.cv (nb077AlphaDummy002 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0004 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∈
      (((synCnin (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
              (Class.cv (nb077AlphaDummy001 F I)))
            (Class.cv (nb077AlphaDummy001 F I)))).fv ∪ ((synCnin (synCima (synCpprod
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
              (Class.cv (nb077AlphaDummy001 F I)))
            (Class.cv (nb077AlphaDummy001 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0005 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∈
      (((synCnin (synCima
              (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
              (Class.cv (nb077AlphaDummy002 x F I)))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪ ((synCnin (synCima
              (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
              (Class.cv (nb077AlphaDummy002 x F I)))
            (Class.cv (nb077AlphaDummy002 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0006 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∈
      (((synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I)))).fv ∪
        ((Class.cv (nb077AlphaDummy001 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0007 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∈
      (((synCima (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪
        ((Class.cv (nb077AlphaDummy002 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0008 (F : Class) (I : Class) :
    (nb077AlphaDummy001 F I) ∈
      (((synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy001 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0009 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy002 x F I) ∈
      (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv ∪
        ((Class.cv (nb077AlphaDummy002 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0010 (F : Class) (I : Class) :
    (nb077AlphaDummy016 F I) ∈
      (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy015 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0011 (F : Class) (I : Class) :
    (nb077AlphaDummy016 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy019 F I)
              (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                  (synCphi (Class.cv (nb077AlphaDummy020 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy019 F I)
              (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy019 F I) from (by
          unfold nb077AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy020 F I) from (by
            unfold nb077AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0012 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy018 x F I) ∈
      (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy017 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0013 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy018 x F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy021 x F I)
              (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy018 x F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                  (synCphi (Class.cv (nb077AlphaDummy022 x F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
                (Class.cv (nb077AlphaDummy017 x F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy021 x F I) from (by
          unfold nb077AlphaDummy021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy022 x F I) from (by
            unfold nb077AlphaDummy022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0014 (F : Class) (I : Class) :
    (nb077AlphaDummy016 F I) ∈
      (((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCphi (Class.cv (nb077AlphaDummy020 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCphi (Class.cv (nb077AlphaDummy020 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy019 F I) from (by
          unfold nb077AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy020 F I) from (by
            unfold nb077AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0015 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy018 x F I) ∈
      (((Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
              (Class.cv (nb077AlphaDummy018 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCphi (Class.cv (nb077AlphaDummy022 x F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
              (Class.cv (nb077AlphaDummy018 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCphi (Class.cv (nb077AlphaDummy022 x F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy021 x F I) from (by
          unfold nb077AlphaDummy021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy022 x F I) from (by
            unfold nb077AlphaDummy022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0016 (F : Class) (I : Class) :
    (nb077AlphaDummy020 F I) ∈ (((Class.cv (nb077AlphaDummy020 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0017 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy022 x F I) ∈ (((Class.cv (nb077AlphaDummy022 x F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0018 (F : Class) (I : Class) :
    (nb077AlphaDummy027 F I) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy027 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy027 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy027 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0019 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy029 x F I) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy029 x F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy029 x F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy029 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0020 (F : Class) (I : Class) :
    (nb077AlphaDummy027 F I) ∈
      (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0021 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy029 x F I) ∈
      (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0022 (F : Class) (I : Class) :
    (nb077AlphaDummy034 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy034 F I))
            (Class.cv (nb077AlphaDummy035 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy034 F I))
            (Class.cv (nb077AlphaDummy035 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0023 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy037 x F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy037 x F I))
            (Class.cv (nb077AlphaDummy038 x F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy037 x F I))
            (Class.cv (nb077AlphaDummy038 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0024 (F : Class) (I : Class) :
    (nb077AlphaDummy034 F I) ∈
      (((Class.cv (nb077AlphaDummy034 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy035 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0025 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy037 x F I) ∈
      (((Class.cv (nb077AlphaDummy037 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy038 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0026 (F : Class) (I : Class) :
    (nb077AlphaDummy035 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy034 F I))
            (Class.cv (nb077AlphaDummy035 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy034 F I))
            (Class.cv (nb077AlphaDummy035 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0027 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy038 x F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy037 x F I))
            (Class.cv (nb077AlphaDummy038 x F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy037 x F I))
            (Class.cv (nb077AlphaDummy038 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0028 (F : Class) (I : Class) :
    (nb077AlphaDummy035 F I) ∈
      (((Class.cv (nb077AlphaDummy034 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy035 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0029 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy038 x F I) ∈
      (((Class.cv (nb077AlphaDummy037 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy038 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0030 (F : Class) (I : Class) :
    (nb077AlphaDummy034 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy034 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy035 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0031 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy037 x F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy037 x F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy038 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0032 (F : Class) (I : Class) :
    (nb077AlphaDummy034 F I) ∈
      (((Class.cv (nb077AlphaDummy034 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy034 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0033 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy037 x F I) ∈
      (((Class.cv (nb077AlphaDummy037 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy037 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0034 (F : Class) (I : Class) :
    (nb077AlphaDummy035 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy034 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy035 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0035 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy038 x F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy037 x F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy038 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0036 (F : Class) (I : Class) :
    (nb077AlphaDummy035 F I) ∈
      (((Class.cv (nb077AlphaDummy035 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy035 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0037 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy038 x F I) ∈
      (((Class.cv (nb077AlphaDummy038 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy038 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0038 (F : Class) (I : Class) :
    (nb077AlphaDummy015 F I) ∈
      (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy015 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part007`. -/


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

theorem nb077_support_mem_0039 (F : Class) (I : Class) :
    (nb077AlphaDummy015 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy019 F I)
              (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                  (synCphi (Class.cv (nb077AlphaDummy020 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy019 F I)
              (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy015 F I) ≠ (nb077AlphaDummy019 F I) from (by
          unfold nb077AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy015 F I) ≠ (nb077AlphaDummy020 F I) from (by
            unfold nb077AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0040 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy017 x F I) ∈
      (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy017 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0041 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy017 x F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy021 x F I)
              (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy018 x F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                  (synCphi (Class.cv (nb077AlphaDummy022 x F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
                (Class.cv (nb077AlphaDummy017 x F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy021 x F I) from (by
          unfold nb077AlphaDummy021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy022 x F I) from (by
            unfold nb077AlphaDummy022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0042 (F : Class) (I : Class) :
    (nb077AlphaDummy015 F I) ∈
      (((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy015 F I) ≠ (nb077AlphaDummy019 F I) from (by
          unfold nb077AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy015 F I) ≠ (nb077AlphaDummy020 F I) from (by
            unfold nb077AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0043 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy017 x F I) ∈
      (((Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
              (Class.cv (nb077AlphaDummy017 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy021 x F I)
            (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy017 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy021 x F I) from (by
          unfold nb077AlphaDummy021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy022 x F I) from (by
            unfold nb077AlphaDummy022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0044 (F : Class) (I : Class) :
    (nb077AlphaDummy020 F I) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy020 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0045 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy022 x F I) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy022 x F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0046 (F : Class) (I : Class) :
    (nb077AlphaDummy020 F I) ∈
      (((synCphi (Class.cv (nb077AlphaDummy020 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy020 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0047 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy022 x F I) ∈
      (((synCphi (Class.cv (nb077AlphaDummy022 x F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy022 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0048 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ∈
      (({(nb077AlphaDummy059 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy060 F I)} : Finset Var) ∪ ((synWex (nb077AlphaDummy061 F I)
            (synWa (synWbr (Class.cv (nb077AlphaDummy059 F I)) (synCcom
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))
                (Class.cv (nb077AlphaDummy061 F I)))
              (synWbr (Class.cv (nb077AlphaDummy061 F I)) (synCcnv (synC1st))
                (Class.cv (nb077AlphaDummy060 F I)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0049 (x : Var) :
    (nb077AlphaDummy062 x) ∈
      (({(nb077AlphaDummy062 x)} : Finset Var) ∪ ({(nb077AlphaDummy063 x)} : Finset Var) ∪
        ((synWex (nb077AlphaDummy064 x) (synWa
              (synWbr (Class.cv (nb077AlphaDummy062 x))
                (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))
                (Class.cv (nb077AlphaDummy064 x)))
              (synWbr (Class.cv (nb077AlphaDummy064 x)) (synCcnv (synC1st))
                (Class.cv (nb077AlphaDummy063 x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0050 (F : Class) (I : Class) :
    (nb077AlphaDummy060 F I) ∈
      (({(nb077AlphaDummy059 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy060 F I)} : Finset Var) ∪ ((synWex (nb077AlphaDummy061 F I)
            (synWa (synWbr (Class.cv (nb077AlphaDummy059 F I)) (synCcom
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))
                (Class.cv (nb077AlphaDummy061 F I)))
              (synWbr (Class.cv (nb077AlphaDummy061 F I)) (synCcnv (synC1st))
                (Class.cv (nb077AlphaDummy060 F I)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0051 (x : Var) :
    (nb077AlphaDummy063 x) ∈
      (({(nb077AlphaDummy062 x)} : Finset Var) ∪ ({(nb077AlphaDummy063 x)} : Finset Var) ∪
        ((synWex (nb077AlphaDummy064 x) (synWa
              (synWbr (Class.cv (nb077AlphaDummy062 x))
                (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))
                (Class.cv (nb077AlphaDummy064 x)))
              (synWbr (Class.cv (nb077AlphaDummy064 x)) (synCcnv (synC1st))
                (Class.cv (nb077AlphaDummy063 x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0052 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ∈
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0053 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy067 F I)
              (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                  (synCphi (Class.cv (nb077AlphaDummy068 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy067 F I)
              (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy067 F I) from (by
          unfold nb077AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy068 F I) from (by
            unfold nb077AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0054 (x : Var) :
    (nb077AlphaDummy062 x) ∈
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0055 (x : Var) :
    (nb077AlphaDummy062 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy069 x)
              (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                  (synCphi (Class.cv (nb077AlphaDummy070 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy069 x)
              (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy069 x) from (by
          unfold nb077AlphaDummy069;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy070 x) from (by
            unfold nb077AlphaDummy070;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0056 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ∈
      (((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCphi (Class.cv (nb077AlphaDummy068 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCphi (Class.cv (nb077AlphaDummy068 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy067 F I) from (by
          unfold nb077AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy068 F I) from (by
            unfold nb077AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0057 (x : Var) :
    (nb077AlphaDummy062 x) ∈
      (((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCphi (Class.cv (nb077AlphaDummy070 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCphi (Class.cv (nb077AlphaDummy070 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy069 x) from (by
          unfold nb077AlphaDummy069;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy070 x) from (by
            unfold nb077AlphaDummy070;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0058 (F : Class) (I : Class) :
    (nb077AlphaDummy068 F I) ∈ (((Class.cv (nb077AlphaDummy068 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0059 (x : Var) :
    (nb077AlphaDummy070 x) ∈ (((Class.cv (nb077AlphaDummy070 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0060 (F : Class) (I : Class) :
    (nb077AlphaDummy075 F I) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy075 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy075 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy075 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0061 (x : Var) :
    (nb077AlphaDummy077 x) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy077 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy077 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy077 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0062 (F : Class) (I : Class) :
    (nb077AlphaDummy075 F I) ∈
      (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0063 (x : Var) :
    (nb077AlphaDummy077 x) ∈
      (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0064 (F : Class) (I : Class) :
    (nb077AlphaDummy082 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy082 F I))
            (Class.cv (nb077AlphaDummy083 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy082 F I))
            (Class.cv (nb077AlphaDummy083 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0065 (x : Var) :
    (nb077AlphaDummy085 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy085 x))
            (Class.cv (nb077AlphaDummy086 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy085 x))
            (Class.cv (nb077AlphaDummy086 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0066 (F : Class) (I : Class) :
    (nb077AlphaDummy082 F I) ∈
      (((Class.cv (nb077AlphaDummy082 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy083 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0067 (x : Var) :
    (nb077AlphaDummy085 x) ∈
      (((Class.cv (nb077AlphaDummy085 x))).fv ∪ ((Class.cv (nb077AlphaDummy086 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0068 (F : Class) (I : Class) :
    (nb077AlphaDummy083 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy082 F I))
            (Class.cv (nb077AlphaDummy083 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy082 F I))
            (Class.cv (nb077AlphaDummy083 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0069 (x : Var) :
    (nb077AlphaDummy086 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy085 x))
            (Class.cv (nb077AlphaDummy086 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy085 x))
            (Class.cv (nb077AlphaDummy086 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0070 (F : Class) (I : Class) :
    (nb077AlphaDummy083 F I) ∈
      (((Class.cv (nb077AlphaDummy082 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy083 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0071 (x : Var) :
    (nb077AlphaDummy086 x) ∈
      (((Class.cv (nb077AlphaDummy085 x))).fv ∪ ((Class.cv (nb077AlphaDummy086 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0072 (F : Class) (I : Class) :
    (nb077AlphaDummy082 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy082 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy083 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0073 (x : Var) :
    (nb077AlphaDummy085 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy085 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy086 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0074 (F : Class) (I : Class) :
    (nb077AlphaDummy082 F I) ∈
      (((Class.cv (nb077AlphaDummy082 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy082 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0075 (x : Var) :
    (nb077AlphaDummy085 x) ∈
      (((Class.cv (nb077AlphaDummy085 x))).fv ∪ ((Class.cv (nb077AlphaDummy085 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0076 (F : Class) (I : Class) :
    (nb077AlphaDummy083 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy082 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy083 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0077 (x : Var) :
    (nb077AlphaDummy086 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy085 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy086 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0078 (F : Class) (I : Class) :
    (nb077AlphaDummy083 F I) ∈
      (((Class.cv (nb077AlphaDummy083 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy083 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0079 (x : Var) :
    (nb077AlphaDummy086 x) ∈
      (((Class.cv (nb077AlphaDummy086 x))).fv ∪ ((Class.cv (nb077AlphaDummy086 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0080 (F : Class) (I : Class) :
    (nb077AlphaDummy060 F I) ∈
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0081 (F : Class) (I : Class) :
    (nb077AlphaDummy060 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy067 F I)
              (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                  (synCphi (Class.cv (nb077AlphaDummy068 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy067 F I)
              (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy067 F I) from (by
          unfold nb077AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy068 F I) from (by
            unfold nb077AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0082 (x : Var) :
    (nb077AlphaDummy063 x) ∈
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0083 (x : Var) :
    (nb077AlphaDummy063 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy069 x)
              (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                  (synCphi (Class.cv (nb077AlphaDummy070 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy069 x)
              (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy069 x) from (by
          unfold nb077AlphaDummy069;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy070 x) from (by
            unfold nb077AlphaDummy070;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0084 (F : Class) (I : Class) :
    (nb077AlphaDummy060 F I) ∈
      (((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy067 F I) from (by
          unfold nb077AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy068 F I) from (by
            unfold nb077AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0085 (x : Var) :
    (nb077AlphaDummy063 x) ∈
      (((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy069 x) from (by
          unfold nb077AlphaDummy069;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy070 x) from (by
            unfold nb077AlphaDummy070;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0086 (F : Class) (I : Class) :
    (nb077AlphaDummy068 F I) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy068 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0087 (x : Var) :
    (nb077AlphaDummy070 x) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy070 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0088 (F : Class) (I : Class) :
    (nb077AlphaDummy068 F I) ∈
      (((synCphi (Class.cv (nb077AlphaDummy068 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy068 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0089 (x : Var) :
    (nb077AlphaDummy070 x) ∈
      (((synCphi (Class.cv (nb077AlphaDummy070 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy070 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0090 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ∈
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy061 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0091 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy103 F I)
              (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                  (synCphi (Class.cv (nb077AlphaDummy104 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy103 F I)
              (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy103 F I) from (by
          unfold nb077AlphaDummy103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy104 F I) from (by
            unfold nb077AlphaDummy104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0092 (x : Var) :
    (nb077AlphaDummy062 x) ∈
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0093 (x : Var) :
    (nb077AlphaDummy062 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy105 x)
              (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                  (synCphi (Class.cv (nb077AlphaDummy106 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy105 x)
              (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy105 x) from (by
          unfold nb077AlphaDummy105;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy106 x) from (by
            unfold nb077AlphaDummy106;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0094 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ∈
      (((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCphi (Class.cv (nb077AlphaDummy104 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCphi (Class.cv (nb077AlphaDummy104 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy103 F I) from (by
          unfold nb077AlphaDummy103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy104 F I) from (by
            unfold nb077AlphaDummy104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0095 (x : Var) :
    (nb077AlphaDummy062 x) ∈
      (((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCphi (Class.cv (nb077AlphaDummy106 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCphi (Class.cv (nb077AlphaDummy106 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy105 x) from (by
          unfold nb077AlphaDummy105;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy106 x) from (by
            unfold nb077AlphaDummy106;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0096 (F : Class) (I : Class) :
    (nb077AlphaDummy104 F I) ∈ (((Class.cv (nb077AlphaDummy104 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0097 (x : Var) :
    (nb077AlphaDummy106 x) ∈ (((Class.cv (nb077AlphaDummy106 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0098 (F : Class) (I : Class) :
    (nb077AlphaDummy111 F I) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy111 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy111 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy111 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0099 (x : Var) :
    (nb077AlphaDummy113 x) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy113 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy113 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy113 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0100 (F : Class) (I : Class) :
    (nb077AlphaDummy111 F I) ∈
      (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0101 (x : Var) :
    (nb077AlphaDummy113 x) ∈
      (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0102 (F : Class) (I : Class) :
    (nb077AlphaDummy118 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy118 F I))
            (Class.cv (nb077AlphaDummy119 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy118 F I))
            (Class.cv (nb077AlphaDummy119 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0103 (x : Var) :
    (nb077AlphaDummy121 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy121 x))
            (Class.cv (nb077AlphaDummy122 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy121 x))
            (Class.cv (nb077AlphaDummy122 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0104 (F : Class) (I : Class) :
    (nb077AlphaDummy118 F I) ∈
      (((Class.cv (nb077AlphaDummy118 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy119 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0105 (x : Var) :
    (nb077AlphaDummy121 x) ∈
      (((Class.cv (nb077AlphaDummy121 x))).fv ∪ ((Class.cv (nb077AlphaDummy122 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0106 (F : Class) (I : Class) :
    (nb077AlphaDummy119 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy118 F I))
            (Class.cv (nb077AlphaDummy119 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy118 F I))
            (Class.cv (nb077AlphaDummy119 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0107 (x : Var) :
    (nb077AlphaDummy122 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy121 x))
            (Class.cv (nb077AlphaDummy122 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy121 x))
            (Class.cv (nb077AlphaDummy122 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0108 (F : Class) (I : Class) :
    (nb077AlphaDummy119 F I) ∈
      (((Class.cv (nb077AlphaDummy118 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy119 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0109 (x : Var) :
    (nb077AlphaDummy122 x) ∈
      (((Class.cv (nb077AlphaDummy121 x))).fv ∪ ((Class.cv (nb077AlphaDummy122 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0110 (F : Class) (I : Class) :
    (nb077AlphaDummy118 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy118 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy119 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0111 (x : Var) :
    (nb077AlphaDummy121 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy121 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy122 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0112 (F : Class) (I : Class) :
    (nb077AlphaDummy118 F I) ∈
      (((Class.cv (nb077AlphaDummy118 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy118 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0113 (x : Var) :
    (nb077AlphaDummy121 x) ∈
      (((Class.cv (nb077AlphaDummy121 x))).fv ∪ ((Class.cv (nb077AlphaDummy121 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0114 (F : Class) (I : Class) :
    (nb077AlphaDummy119 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy118 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy119 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0115 (x : Var) :
    (nb077AlphaDummy122 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy121 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy122 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0116 (F : Class) (I : Class) :
    (nb077AlphaDummy119 F I) ∈
      (((Class.cv (nb077AlphaDummy119 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy119 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0117 (x : Var) :
    (nb077AlphaDummy122 x) ∈
      (((Class.cv (nb077AlphaDummy122 x))).fv ∪ ((Class.cv (nb077AlphaDummy122 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0118 (F : Class) (I : Class) :
    (nb077AlphaDummy061 F I) ∈
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy061 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0119 (F : Class) (I : Class) :
    (nb077AlphaDummy061 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy103 F I)
              (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                  (synCphi (Class.cv (nb077AlphaDummy104 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy103 F I)
              (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy103 F I) from (by
          unfold nb077AlphaDummy103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy104 F I) from (by
            unfold nb077AlphaDummy104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0120 (x : Var) :
    (nb077AlphaDummy064 x) ∈
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0121 (x : Var) :
    (nb077AlphaDummy064 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy105 x)
              (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                  (synCphi (Class.cv (nb077AlphaDummy106 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy105 x)
              (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy105 x) from (by
          unfold nb077AlphaDummy105;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy106 x) from (by
            unfold nb077AlphaDummy106;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0122 (F : Class) (I : Class) :
    (nb077AlphaDummy061 F I) ∈
      (((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy103 F I) from (by
          unfold nb077AlphaDummy103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy104 F I) from (by
            unfold nb077AlphaDummy104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0123 (x : Var) :
    (nb077AlphaDummy064 x) ∈
      (((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy105 x) from (by
          unfold nb077AlphaDummy105;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy106 x) from (by
            unfold nb077AlphaDummy106;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0124 (F : Class) (I : Class) :
    (nb077AlphaDummy104 F I) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy104 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0125 (x : Var) :
    (nb077AlphaDummy106 x) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy106 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0126 (F : Class) (I : Class) :
    (nb077AlphaDummy104 F I) ∈
      (((synCphi (Class.cv (nb077AlphaDummy104 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy104 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0127 (x : Var) :
    (nb077AlphaDummy106 x) ∈
      (((synCphi (Class.cv (nb077AlphaDummy106 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy106 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0128 (F : Class) (I : Class) :
    (nb077AlphaDummy139 F I) ∈
      (({(nb077AlphaDummy139 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy140 F I)} : Finset Var) ∪ ((synWex (nb077AlphaDummy141 F I)
            (synWa (synWbr (Class.cv (nb077AlphaDummy139 F I)) (synC1st)
                (Class.cv (nb077AlphaDummy141 F I)))
              (synWbr (Class.cv (nb077AlphaDummy141 F I))
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
                (Class.cv (nb077AlphaDummy140 F I)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0129 (x : Var) :
    (nb077AlphaDummy142 x) ∈
      (({(nb077AlphaDummy142 x)} : Finset Var) ∪ ({(nb077AlphaDummy143 x)} : Finset Var) ∪
        ((synWex (nb077AlphaDummy144 x) (synWa
              (synWbr (Class.cv (nb077AlphaDummy142 x)) (synC1st)
                (Class.cv (nb077AlphaDummy144 x)))
              (synWbr (Class.cv (nb077AlphaDummy144 x))
                (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
                (Class.cv (nb077AlphaDummy143 x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0130 (F : Class) (I : Class) :
    (nb077AlphaDummy140 F I) ∈
      (({(nb077AlphaDummy139 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy140 F I)} : Finset Var) ∪ ((synWex (nb077AlphaDummy141 F I)
            (synWa (synWbr (Class.cv (nb077AlphaDummy139 F I)) (synC1st)
                (Class.cv (nb077AlphaDummy141 F I)))
              (synWbr (Class.cv (nb077AlphaDummy141 F I))
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
                (Class.cv (nb077AlphaDummy140 F I)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0131 (x : Var) :
    (nb077AlphaDummy143 x) ∈
      (({(nb077AlphaDummy142 x)} : Finset Var) ∪ ({(nb077AlphaDummy143 x)} : Finset Var) ∪
        ((synWex (nb077AlphaDummy144 x) (synWa
              (synWbr (Class.cv (nb077AlphaDummy142 x)) (synC1st)
                (Class.cv (nb077AlphaDummy144 x)))
              (synWbr (Class.cv (nb077AlphaDummy144 x))
                (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
                (Class.cv (nb077AlphaDummy143 x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0132 (F : Class) (I : Class) :
    (nb077AlphaDummy139 F I) ∈
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0133 (F : Class) (I : Class) :
    (nb077AlphaDummy139 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy147 F I)
              (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                  (synCphi (Class.cv (nb077AlphaDummy148 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy147 F I)
              (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy147 F I) from (by
          unfold nb077AlphaDummy147;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy148 F I) from (by
            unfold nb077AlphaDummy148;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0134 (x : Var) :
    (nb077AlphaDummy142 x) ∈
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0135 (x : Var) :
    (nb077AlphaDummy142 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy149 x)
              (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                  (synCphi (Class.cv (nb077AlphaDummy150 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy149 x)
              (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy149 x) from (by
          unfold nb077AlphaDummy149;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy150 x) from (by
            unfold nb077AlphaDummy150;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0136 (F : Class) (I : Class) :
    (nb077AlphaDummy139 F I) ∈
      (((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCphi (Class.cv (nb077AlphaDummy148 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCphi (Class.cv (nb077AlphaDummy148 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy147 F I) from (by
          unfold nb077AlphaDummy147;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy148 F I) from (by
            unfold nb077AlphaDummy148;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0137 (x : Var) :
    (nb077AlphaDummy142 x) ∈
      (((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCphi (Class.cv (nb077AlphaDummy150 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCphi (Class.cv (nb077AlphaDummy150 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy149 x) from (by
          unfold nb077AlphaDummy149;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy150 x) from (by
            unfold nb077AlphaDummy150;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0138 (F : Class) (I : Class) :
    (nb077AlphaDummy148 F I) ∈ (((Class.cv (nb077AlphaDummy148 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0139 (x : Var) :
    (nb077AlphaDummy150 x) ∈ (((Class.cv (nb077AlphaDummy150 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0140 (F : Class) (I : Class) :
    (nb077AlphaDummy155 F I) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy155 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy155 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy155 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0141 (x : Var) :
    (nb077AlphaDummy157 x) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy157 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy157 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy157 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0142 (F : Class) (I : Class) :
    (nb077AlphaDummy155 F I) ∈
      (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0143 (x : Var) :
    (nb077AlphaDummy157 x) ∈
      (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0144 (F : Class) (I : Class) :
    (nb077AlphaDummy162 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy162 F I))
            (Class.cv (nb077AlphaDummy163 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy162 F I))
            (Class.cv (nb077AlphaDummy163 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0145 (x : Var) :
    (nb077AlphaDummy165 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy165 x))
            (Class.cv (nb077AlphaDummy166 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy165 x))
            (Class.cv (nb077AlphaDummy166 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0146 (F : Class) (I : Class) :
    (nb077AlphaDummy162 F I) ∈
      (((Class.cv (nb077AlphaDummy162 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy163 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0147 (x : Var) :
    (nb077AlphaDummy165 x) ∈
      (((Class.cv (nb077AlphaDummy165 x))).fv ∪ ((Class.cv (nb077AlphaDummy166 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0148 (F : Class) (I : Class) :
    (nb077AlphaDummy163 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy162 F I))
            (Class.cv (nb077AlphaDummy163 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy162 F I))
            (Class.cv (nb077AlphaDummy163 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0149 (x : Var) :
    (nb077AlphaDummy166 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy165 x))
            (Class.cv (nb077AlphaDummy166 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy165 x))
            (Class.cv (nb077AlphaDummy166 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0150 (F : Class) (I : Class) :
    (nb077AlphaDummy163 F I) ∈
      (((Class.cv (nb077AlphaDummy162 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy163 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0151 (x : Var) :
    (nb077AlphaDummy166 x) ∈
      (((Class.cv (nb077AlphaDummy165 x))).fv ∪ ((Class.cv (nb077AlphaDummy166 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0152 (F : Class) (I : Class) :
    (nb077AlphaDummy162 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy162 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy163 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0153 (x : Var) :
    (nb077AlphaDummy165 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy165 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy166 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0154 (F : Class) (I : Class) :
    (nb077AlphaDummy162 F I) ∈
      (((Class.cv (nb077AlphaDummy162 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy162 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0155 (x : Var) :
    (nb077AlphaDummy165 x) ∈
      (((Class.cv (nb077AlphaDummy165 x))).fv ∪ ((Class.cv (nb077AlphaDummy165 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0156 (F : Class) (I : Class) :
    (nb077AlphaDummy163 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy162 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy163 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0157 (x : Var) :
    (nb077AlphaDummy166 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy165 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy166 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0158 (F : Class) (I : Class) :
    (nb077AlphaDummy163 F I) ∈
      (((Class.cv (nb077AlphaDummy163 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy163 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0159 (x : Var) :
    (nb077AlphaDummy166 x) ∈
      (((Class.cv (nb077AlphaDummy166 x))).fv ∪ ((Class.cv (nb077AlphaDummy166 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0160 (F : Class) (I : Class) :
    (nb077AlphaDummy140 F I) ∈
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0161 (F : Class) (I : Class) :
    (nb077AlphaDummy140 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy147 F I)
              (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                  (synCphi (Class.cv (nb077AlphaDummy148 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy147 F I)
              (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy147 F I) from (by
          unfold nb077AlphaDummy147;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0160 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy148 F I) from (by
            unfold nb077AlphaDummy148;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0160 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0162 (x : Var) :
    (nb077AlphaDummy143 x) ∈
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0163 (x : Var) :
    (nb077AlphaDummy143 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy149 x)
              (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                  (synCphi (Class.cv (nb077AlphaDummy150 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy149 x)
              (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy149 x) from (by
          unfold nb077AlphaDummy149;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy150 x) from (by
            unfold nb077AlphaDummy150;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0164 (F : Class) (I : Class) :
    (nb077AlphaDummy140 F I) ∈
      (((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy147 F I) from (by
          unfold nb077AlphaDummy147;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0160 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy148 F I) from (by
            unfold nb077AlphaDummy148;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0160 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part008`. -/


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

theorem nb077_support_mem_0165 (x : Var) :
    (nb077AlphaDummy143 x) ∈
      (((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy149 x) from (by
          unfold nb077AlphaDummy149;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy150 x) from (by
            unfold nb077AlphaDummy150;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0166 (F : Class) (I : Class) :
    (nb077AlphaDummy148 F I) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy148 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0167 (x : Var) :
    (nb077AlphaDummy150 x) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy150 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0168 (F : Class) (I : Class) :
    (nb077AlphaDummy148 F I) ∈
      (((synCphi (Class.cv (nb077AlphaDummy148 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy148 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0169 (x : Var) :
    (nb077AlphaDummy150 x) ∈
      (((synCphi (Class.cv (nb077AlphaDummy150 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy150 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0170 (F : Class) (I : Class) :
    (nb077AlphaDummy139 F I) ∈
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy141 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0171 (F : Class) (I : Class) :
    (nb077AlphaDummy139 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy183 F I)
              (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                  (synCphi (Class.cv (nb077AlphaDummy184 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy183 F I)
              (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy183 F I) from (by
          unfold nb077AlphaDummy183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy184 F I) from (by
            unfold nb077AlphaDummy184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0172 (x : Var) :
    (nb077AlphaDummy142 x) ∈
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy144 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0173 (x : Var) :
    (nb077AlphaDummy142 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy185 x)
              (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                  (synCphi (Class.cv (nb077AlphaDummy186 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy185 x)
              (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy185 x) from (by
          unfold nb077AlphaDummy185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy186 x) from (by
            unfold nb077AlphaDummy186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0174 (F : Class) (I : Class) :
    (nb077AlphaDummy139 F I) ∈
      (((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCphi (Class.cv (nb077AlphaDummy184 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCphi (Class.cv (nb077AlphaDummy184 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy183 F I) from (by
          unfold nb077AlphaDummy183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy184 F I) from (by
            unfold nb077AlphaDummy184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0175 (x : Var) :
    (nb077AlphaDummy142 x) ∈
      (((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCphi (Class.cv (nb077AlphaDummy186 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCphi (Class.cv (nb077AlphaDummy186 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy185 x) from (by
          unfold nb077AlphaDummy185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy186 x) from (by
            unfold nb077AlphaDummy186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0176 (F : Class) (I : Class) :
    (nb077AlphaDummy184 F I) ∈ (((Class.cv (nb077AlphaDummy184 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0177 (x : Var) :
    (nb077AlphaDummy186 x) ∈ (((Class.cv (nb077AlphaDummy186 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0178 (F : Class) (I : Class) :
    (nb077AlphaDummy191 F I) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy191 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy191 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy191 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0179 (x : Var) :
    (nb077AlphaDummy193 x) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy193 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy193 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy193 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0180 (F : Class) (I : Class) :
    (nb077AlphaDummy191 F I) ∈
      (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0181 (x : Var) :
    (nb077AlphaDummy193 x) ∈
      (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0182 (F : Class) (I : Class) :
    (nb077AlphaDummy198 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy198 F I))
            (Class.cv (nb077AlphaDummy199 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy198 F I))
            (Class.cv (nb077AlphaDummy199 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0183 (x : Var) :
    (nb077AlphaDummy201 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy201 x))
            (Class.cv (nb077AlphaDummy202 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy201 x))
            (Class.cv (nb077AlphaDummy202 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0184 (F : Class) (I : Class) :
    (nb077AlphaDummy198 F I) ∈
      (((Class.cv (nb077AlphaDummy198 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy199 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0185 (x : Var) :
    (nb077AlphaDummy201 x) ∈
      (((Class.cv (nb077AlphaDummy201 x))).fv ∪ ((Class.cv (nb077AlphaDummy202 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0186 (F : Class) (I : Class) :
    (nb077AlphaDummy199 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy198 F I))
            (Class.cv (nb077AlphaDummy199 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy198 F I))
            (Class.cv (nb077AlphaDummy199 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0187 (x : Var) :
    (nb077AlphaDummy202 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy201 x))
            (Class.cv (nb077AlphaDummy202 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy201 x))
            (Class.cv (nb077AlphaDummy202 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0188 (F : Class) (I : Class) :
    (nb077AlphaDummy199 F I) ∈
      (((Class.cv (nb077AlphaDummy198 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy199 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0189 (x : Var) :
    (nb077AlphaDummy202 x) ∈
      (((Class.cv (nb077AlphaDummy201 x))).fv ∪ ((Class.cv (nb077AlphaDummy202 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0190 (F : Class) (I : Class) :
    (nb077AlphaDummy198 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy198 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy199 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0191 (x : Var) :
    (nb077AlphaDummy201 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy201 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy202 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0192 (F : Class) (I : Class) :
    (nb077AlphaDummy198 F I) ∈
      (((Class.cv (nb077AlphaDummy198 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy198 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0193 (x : Var) :
    (nb077AlphaDummy201 x) ∈
      (((Class.cv (nb077AlphaDummy201 x))).fv ∪ ((Class.cv (nb077AlphaDummy201 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0194 (F : Class) (I : Class) :
    (nb077AlphaDummy199 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy198 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy199 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0195 (x : Var) :
    (nb077AlphaDummy202 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy201 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy202 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0196 (F : Class) (I : Class) :
    (nb077AlphaDummy199 F I) ∈
      (((Class.cv (nb077AlphaDummy199 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy199 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0197 (x : Var) :
    (nb077AlphaDummy202 x) ∈
      (((Class.cv (nb077AlphaDummy202 x))).fv ∪ ((Class.cv (nb077AlphaDummy202 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0198 (F : Class) (I : Class) :
    (nb077AlphaDummy141 F I) ∈
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy141 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0199 (F : Class) (I : Class) :
    (nb077AlphaDummy141 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy183 F I)
              (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                  (synCphi (Class.cv (nb077AlphaDummy184 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy183 F I)
              (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy183 F I) from (by
          unfold nb077AlphaDummy183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy184 F I) from (by
            unfold nb077AlphaDummy184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0200 (x : Var) :
    (nb077AlphaDummy144 x) ∈
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy144 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0201 (x : Var) :
    (nb077AlphaDummy144 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy185 x)
              (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                  (synCphi (Class.cv (nb077AlphaDummy186 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy185 x)
              (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy185 x) from (by
          unfold nb077AlphaDummy185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy186 x) from (by
            unfold nb077AlphaDummy186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0202 (F : Class) (I : Class) :
    (nb077AlphaDummy141 F I) ∈
      (((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy183 F I) from (by
          unfold nb077AlphaDummy183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy184 F I) from (by
            unfold nb077AlphaDummy184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0203 (x : Var) :
    (nb077AlphaDummy144 x) ∈
      (((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy185 x) from (by
          unfold nb077AlphaDummy185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy186 x) from (by
            unfold nb077AlphaDummy186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0204 (F : Class) (I : Class) :
    (nb077AlphaDummy184 F I) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy184 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0205 (x : Var) :
    (nb077AlphaDummy186 x) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy186 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0206 (F : Class) (I : Class) :
    (nb077AlphaDummy184 F I) ∈
      (((synCphi (Class.cv (nb077AlphaDummy184 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy184 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0207 (x : Var) :
    (nb077AlphaDummy186 x) ∈
      (((synCphi (Class.cv (nb077AlphaDummy186 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy186 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0208 (F : Class) (I : Class) :
    (nb077AlphaDummy141 F I) ∈
      (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0209 (F : Class) (I : Class) :
    (nb077AlphaDummy141 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy219 F I)
              (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                  (synCphi (Class.cv (nb077AlphaDummy220 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy219 F I)
              (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy219 F I) from (by
          unfold nb077AlphaDummy219;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy220 F I) from (by
            unfold nb077AlphaDummy220;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0210 (x : Var) :
    (nb077AlphaDummy144 x) ∈
      (((Class.cv (nb077AlphaDummy144 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0211 (x : Var) :
    (nb077AlphaDummy144 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy221 x)
              (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                  (synCphi (Class.cv (nb077AlphaDummy222 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy221 x)
              (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy221 x) from (by
          unfold nb077AlphaDummy221;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy222 x) from (by
            unfold nb077AlphaDummy222;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0212 (F : Class) (I : Class) :
    (nb077AlphaDummy141 F I) ∈
      (((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCphi (Class.cv (nb077AlphaDummy220 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCphi (Class.cv (nb077AlphaDummy220 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy219 F I) from (by
          unfold nb077AlphaDummy219;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy141 F I) ≠ (nb077AlphaDummy220 F I) from (by
            unfold nb077AlphaDummy220;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0213 (x : Var) :
    (nb077AlphaDummy144 x) ∈
      (((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCphi (Class.cv (nb077AlphaDummy222 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCphi (Class.cv (nb077AlphaDummy222 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy221 x) from (by
          unfold nb077AlphaDummy221;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy144 x) ≠ (nb077AlphaDummy222 x) from (by
            unfold nb077AlphaDummy222;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0214 (F : Class) (I : Class) :
    (nb077AlphaDummy220 F I) ∈ (((Class.cv (nb077AlphaDummy220 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0215 (x : Var) :
    (nb077AlphaDummy222 x) ∈ (((Class.cv (nb077AlphaDummy222 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0216 (F : Class) (I : Class) :
    (nb077AlphaDummy227 F I) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy227 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy227 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy227 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0217 (x : Var) :
    (nb077AlphaDummy229 x) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy229 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy229 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy229 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0218 (F : Class) (I : Class) :
    (nb077AlphaDummy227 F I) ∈
      (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0219 (x : Var) :
    (nb077AlphaDummy229 x) ∈
      (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0220 (F : Class) (I : Class) :
    (nb077AlphaDummy234 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy234 F I))
            (Class.cv (nb077AlphaDummy235 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy234 F I))
            (Class.cv (nb077AlphaDummy235 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0221 (x : Var) :
    (nb077AlphaDummy237 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy237 x))
            (Class.cv (nb077AlphaDummy238 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy237 x))
            (Class.cv (nb077AlphaDummy238 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0222 (F : Class) (I : Class) :
    (nb077AlphaDummy234 F I) ∈
      (((Class.cv (nb077AlphaDummy234 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy235 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0223 (x : Var) :
    (nb077AlphaDummy237 x) ∈
      (((Class.cv (nb077AlphaDummy237 x))).fv ∪ ((Class.cv (nb077AlphaDummy238 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0224 (F : Class) (I : Class) :
    (nb077AlphaDummy235 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy234 F I))
            (Class.cv (nb077AlphaDummy235 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy234 F I))
            (Class.cv (nb077AlphaDummy235 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0225 (x : Var) :
    (nb077AlphaDummy238 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy237 x))
            (Class.cv (nb077AlphaDummy238 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy237 x))
            (Class.cv (nb077AlphaDummy238 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0226 (F : Class) (I : Class) :
    (nb077AlphaDummy235 F I) ∈
      (((Class.cv (nb077AlphaDummy234 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy235 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0227 (x : Var) :
    (nb077AlphaDummy238 x) ∈
      (((Class.cv (nb077AlphaDummy237 x))).fv ∪ ((Class.cv (nb077AlphaDummy238 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0228 (F : Class) (I : Class) :
    (nb077AlphaDummy234 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy234 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy235 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0229 (x : Var) :
    (nb077AlphaDummy237 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy237 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy238 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0230 (F : Class) (I : Class) :
    (nb077AlphaDummy234 F I) ∈
      (((Class.cv (nb077AlphaDummy234 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy234 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0231 (x : Var) :
    (nb077AlphaDummy237 x) ∈
      (((Class.cv (nb077AlphaDummy237 x))).fv ∪ ((Class.cv (nb077AlphaDummy237 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0232 (F : Class) (I : Class) :
    (nb077AlphaDummy235 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy234 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy235 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0233 (x : Var) :
    (nb077AlphaDummy238 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy237 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy238 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0234 (F : Class) (I : Class) :
    (nb077AlphaDummy235 F I) ∈
      (((Class.cv (nb077AlphaDummy235 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy235 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0235 (x : Var) :
    (nb077AlphaDummy238 x) ∈
      (((Class.cv (nb077AlphaDummy238 x))).fv ∪ ((Class.cv (nb077AlphaDummy238 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0236 (F : Class) (I : Class) :
    (nb077AlphaDummy140 F I) ∈
      (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0237 (F : Class) (I : Class) :
    (nb077AlphaDummy140 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy219 F I)
              (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                  (synCphi (Class.cv (nb077AlphaDummy220 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy219 F I)
              (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy219 F I) from (by
          unfold nb077AlphaDummy219;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy220 F I) from (by
            unfold nb077AlphaDummy220;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0238 (x : Var) :
    (nb077AlphaDummy143 x) ∈
      (((Class.cv (nb077AlphaDummy144 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0239 (x : Var) :
    (nb077AlphaDummy143 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy221 x)
              (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                  (synCphi (Class.cv (nb077AlphaDummy222 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy221 x)
              (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy221 x) from (by
          unfold nb077AlphaDummy221;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy222 x) from (by
            unfold nb077AlphaDummy222;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0240 (F : Class) (I : Class) :
    (nb077AlphaDummy140 F I) ∈
      (((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy219 F I) from (by
          unfold nb077AlphaDummy219;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy220 F I) from (by
            unfold nb077AlphaDummy220;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0241 (x : Var) :
    (nb077AlphaDummy143 x) ∈
      (((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy221 x) from (by
          unfold nb077AlphaDummy221;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy222 x) from (by
            unfold nb077AlphaDummy222;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0242 (F : Class) (I : Class) :
    (nb077AlphaDummy220 F I) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy220 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0243 (x : Var) :
    (nb077AlphaDummy222 x) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy222 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0244 (F : Class) (I : Class) :
    (nb077AlphaDummy220 F I) ∈
      (((synCphi (Class.cv (nb077AlphaDummy220 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy220 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0245 (x : Var) :
    (nb077AlphaDummy222 x) ∈
      (((synCphi (Class.cv (nb077AlphaDummy222 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy222 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0246 (F : Class) (I : Class) :
    (nb077AlphaDummy000 F I) ∈
      (({(nb077AlphaDummy000 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy255 F I)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb077AlphaDummy000 F I)) (synCvv))
            (Wff.classEq (Class.cv (nb077AlphaDummy255 F I))
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0247 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({(nb077AlphaDummy256 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb077AlphaDummy256 x))
              (synCplc (Class.cv x) (synC1c))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0248 (F : Class) (I : Class) :
    (nb077AlphaDummy255 F I) ∈
      (({(nb077AlphaDummy000 F I)} : Finset Var) ∪
          ({(nb077AlphaDummy255 F I)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb077AlphaDummy000 F I)) (synCvv))
            (Wff.classEq (Class.cv (nb077AlphaDummy255 F I))
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0249 (x : Var) :
    (nb077AlphaDummy256 x) ∈
      (({ x } : Finset Var) ∪ ({(nb077AlphaDummy256 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb077AlphaDummy256 x))
              (synCplc (Class.cv x) (synC1c))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0250 (F : Class) (I : Class) :
    (nb077AlphaDummy000 F I) ∈
      (({(nb077AlphaDummy000 F I)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0251 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCplc (Class.cv x) (synC1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0252 (F : Class) (I : Class) :
    (nb077AlphaDummy000 F I) ∈
      (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy255 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0253 (F : Class) (I : Class) :
    (nb077AlphaDummy000 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy259 F I)
              (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                  (synCphi (Class.cv (nb077AlphaDummy260 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy259 F I)
              (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy000 F I) ≠ (nb077AlphaDummy259 F I) from (by
          unfold nb077AlphaDummy259;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy000 F I) ≠ (nb077AlphaDummy260 F I) from (by
            unfold nb077AlphaDummy260;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0254 (x : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb077AlphaDummy256 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0255 (x : Var) :
    x ∈
      (((synCcompl (Class.cab (nb077AlphaDummy261 x)
              (synWrex (nb077AlphaDummy262 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                  (synCphi (Class.cv (nb077AlphaDummy262 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy261 x)
              (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb077AlphaDummy261 x) from (by
          unfold nb077AlphaDummy261;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb077AlphaDummy262 x) from (by
            unfold nb077AlphaDummy262;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0256 (F : Class) (I : Class) :
    (nb077AlphaDummy000 F I) ∈
      (((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCphi (Class.cv (nb077AlphaDummy260 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCphi (Class.cv (nb077AlphaDummy260 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy000 F I) ≠ (nb077AlphaDummy259 F I) from (by
          unfold nb077AlphaDummy259;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy000 F I) ≠ (nb077AlphaDummy260 F I) from (by
            unfold nb077AlphaDummy260;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0257 (x : Var) :
    x ∈
      (((Class.cab (nb077AlphaDummy261 x) (synWrex (nb077AlphaDummy262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCphi (Class.cv (nb077AlphaDummy262 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy261 x) (synWrex (nb077AlphaDummy262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCphi (Class.cv (nb077AlphaDummy262 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb077AlphaDummy261 x) from (by
          unfold nb077AlphaDummy261;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb077AlphaDummy262 x) from (by
            unfold nb077AlphaDummy262;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0258 (F : Class) (I : Class) :
    (nb077AlphaDummy260 F I) ∈ (((Class.cv (nb077AlphaDummy260 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0259 (x : Var) :
    (nb077AlphaDummy262 x) ∈ (((Class.cv (nb077AlphaDummy262 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0260 (F : Class) (I : Class) :
    (nb077AlphaDummy267 F I) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy267 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy267 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy267 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0261 (x : Var) :
    (nb077AlphaDummy269 x) ∈
      (((Wff.classMem (Class.cv (nb077AlphaDummy269 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy269 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy269 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0262 (F : Class) (I : Class) :
    (nb077AlphaDummy267 F I) ∈
      (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0263 (x : Var) :
    (nb077AlphaDummy269 x) ∈
      (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0264 (F : Class) (I : Class) :
    (nb077AlphaDummy274 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy274 F I))
            (Class.cv (nb077AlphaDummy275 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy274 F I))
            (Class.cv (nb077AlphaDummy275 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0265 (x : Var) :
    (nb077AlphaDummy277 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy277 x))
            (Class.cv (nb077AlphaDummy278 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy277 x))
            (Class.cv (nb077AlphaDummy278 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0266 (F : Class) (I : Class) :
    (nb077AlphaDummy274 F I) ∈
      (((Class.cv (nb077AlphaDummy274 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy275 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0267 (x : Var) :
    (nb077AlphaDummy277 x) ∈
      (((Class.cv (nb077AlphaDummy277 x))).fv ∪ ((Class.cv (nb077AlphaDummy278 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0268 (F : Class) (I : Class) :
    (nb077AlphaDummy275 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy274 F I))
            (Class.cv (nb077AlphaDummy275 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy274 F I))
            (Class.cv (nb077AlphaDummy275 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0269 (x : Var) :
    (nb077AlphaDummy278 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy277 x))
            (Class.cv (nb077AlphaDummy278 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy277 x))
            (Class.cv (nb077AlphaDummy278 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0270 (F : Class) (I : Class) :
    (nb077AlphaDummy275 F I) ∈
      (((Class.cv (nb077AlphaDummy274 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy275 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0271 (x : Var) :
    (nb077AlphaDummy278 x) ∈
      (((Class.cv (nb077AlphaDummy277 x))).fv ∪ ((Class.cv (nb077AlphaDummy278 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0272 (F : Class) (I : Class) :
    (nb077AlphaDummy274 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy274 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy275 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0273 (x : Var) :
    (nb077AlphaDummy277 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy277 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy278 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0274 (F : Class) (I : Class) :
    (nb077AlphaDummy274 F I) ∈
      (((Class.cv (nb077AlphaDummy274 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy274 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0275 (x : Var) :
    (nb077AlphaDummy277 x) ∈
      (((Class.cv (nb077AlphaDummy277 x))).fv ∪ ((Class.cv (nb077AlphaDummy277 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0276 (F : Class) (I : Class) :
    (nb077AlphaDummy275 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy274 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy275 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0277 (x : Var) :
    (nb077AlphaDummy278 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy277 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy278 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0278 (F : Class) (I : Class) :
    (nb077AlphaDummy275 F I) ∈
      (((Class.cv (nb077AlphaDummy275 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy275 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0279 (x : Var) :
    (nb077AlphaDummy278 x) ∈
      (((Class.cv (nb077AlphaDummy278 x))).fv ∪ ((Class.cv (nb077AlphaDummy278 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0280 (F : Class) (I : Class) :
    (nb077AlphaDummy255 F I) ∈
      (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy255 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0281 (F : Class) (I : Class) :
    (nb077AlphaDummy255 F I) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy259 F I)
              (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                  (synCphi (Class.cv (nb077AlphaDummy260 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy259 F I)
              (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy255 F I) ≠ (nb077AlphaDummy259 F I) from (by
          unfold nb077AlphaDummy259;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy255 F I) ≠ (nb077AlphaDummy260 F I) from (by
            unfold nb077AlphaDummy260;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0282 (x : Var) :
    (nb077AlphaDummy256 x) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb077AlphaDummy256 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0283 (x : Var) :
    (nb077AlphaDummy256 x) ∈
      (((synCcompl (Class.cab (nb077AlphaDummy261 x)
              (synWrex (nb077AlphaDummy262 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                  (synCphi (Class.cv (nb077AlphaDummy262 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy261 x)
              (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy261 x) from (by
          unfold nb077AlphaDummy261;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy262 x) from (by
            unfold nb077AlphaDummy262;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0284 (F : Class) (I : Class) :
    (nb077AlphaDummy255 F I) ∈
      (((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy255 F I) ≠ (nb077AlphaDummy259 F I) from (by
          unfold nb077AlphaDummy259;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy255 F I) ≠ (nb077AlphaDummy260 F I) from (by
            unfold nb077AlphaDummy260;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0285 (x : Var) :
    (nb077AlphaDummy256 x) ∈
      (((Class.cab (nb077AlphaDummy261 x)
            (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy261 x)
            (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy261 x) from (by
          unfold nb077AlphaDummy261;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077AlphaDummy256 x) ≠ (nb077AlphaDummy262 x) from (by
            unfold nb077AlphaDummy262;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0286 (F : Class) (I : Class) :
    (nb077AlphaDummy260 F I) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy260 F I))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0287 (x : Var) :
    (nb077AlphaDummy262 x) ∈
      (((synCcompl (synCphi (Class.cv (nb077AlphaDummy262 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0288 (F : Class) (I : Class) :
    (nb077AlphaDummy260 F I) ∈
      (((synCphi (Class.cv (nb077AlphaDummy260 F I)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy260 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0289 (x : Var) :
    (nb077AlphaDummy262 x) ∈
      (((synCphi (Class.cv (nb077AlphaDummy262 x)))).fv ∪
        ((synCphi (Class.cv (nb077AlphaDummy262 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0290 (F : Class) (I : Class) :
    (nb077AlphaDummy000 F I) ∈
      (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0291 (x : Var) : x ∈ (((Class.cv x)).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0292 (F : Class) (I : Class) :
    (nb077AlphaDummy296 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy296 F I))
            (Class.cv (nb077AlphaDummy297 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy296 F I))
            (Class.cv (nb077AlphaDummy297 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0293 (x : Var) :
    (nb077AlphaDummy299 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy299 x))
            (Class.cv (nb077AlphaDummy300 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy299 x))
            (Class.cv (nb077AlphaDummy300 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0294 (F : Class) (I : Class) :
    (nb077AlphaDummy296 F I) ∈
      (((Class.cv (nb077AlphaDummy296 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy297 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0295 (x : Var) :
    (nb077AlphaDummy299 x) ∈
      (((Class.cv (nb077AlphaDummy299 x))).fv ∪ ((Class.cv (nb077AlphaDummy300 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0296 (F : Class) (I : Class) :
    (nb077AlphaDummy297 F I) ∈
      (((synCnin (Class.cv (nb077AlphaDummy296 F I))
            (Class.cv (nb077AlphaDummy297 F I)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy296 F I))
            (Class.cv (nb077AlphaDummy297 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0297 (x : Var) :
    (nb077AlphaDummy300 x) ∈
      (((synCnin (Class.cv (nb077AlphaDummy299 x))
            (Class.cv (nb077AlphaDummy300 x)))).fv ∪
        ((synCnin (Class.cv (nb077AlphaDummy299 x))
            (Class.cv (nb077AlphaDummy300 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0298 (F : Class) (I : Class) :
    (nb077AlphaDummy297 F I) ∈
      (((Class.cv (nb077AlphaDummy296 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy297 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0299 (x : Var) :
    (nb077AlphaDummy300 x) ∈
      (((Class.cv (nb077AlphaDummy299 x))).fv ∪ ((Class.cv (nb077AlphaDummy300 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0300 (F : Class) (I : Class) :
    (nb077AlphaDummy296 F I) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy296 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy297 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0301 (x : Var) :
    (nb077AlphaDummy299 x) ∈
      (((synCcompl (Class.cv (nb077AlphaDummy299 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy300 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0302 (F : Class) (I : Class) :
    (nb077AlphaDummy296 F I) ∈
      (((Class.cv (nb077AlphaDummy296 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy296 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0303 (x : Var) :
    (nb077AlphaDummy299 x) ∈
      (((Class.cv (nb077AlphaDummy299 x))).fv ∪ ((Class.cv (nb077AlphaDummy299 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
