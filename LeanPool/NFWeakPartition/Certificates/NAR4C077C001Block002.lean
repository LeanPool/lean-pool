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
    (nb077_alpha_dummy_305 F I) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_296 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_297 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_305] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_296 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_297 F I)))).fv)
      0

theorem nb077_fresh_357 (x : Var) :
    (nb077_alpha_dummy_306 x) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_299 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_300 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_306] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_299 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_300 x)))).fv)
      0

theorem nb077_fresh_358 (F : Class) (I : Class) :
    (nb077_alpha_dummy_335 F I) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_326 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_327 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_335] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_326 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_327 F I)))).fv)
      0

theorem nb077_fresh_359 (x : Var) :
    (nb077_alpha_dummy_336 x) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_329 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_330 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_336] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_329 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_330 x)))).fv)
      0

theorem nb077_fresh_360 (F : Class) (I : Class) :
    (nb077_alpha_dummy_051 F I) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_051] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_361 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_052 x F I) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_052] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_362 (F : Class) (I : Class) :
    (nb077_alpha_dummy_099 F I) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_099] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_363 (x : Var) :
    (nb077_alpha_dummy_100 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_100] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_364 (F : Class) (I : Class) :
    (nb077_alpha_dummy_135 F I) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_135] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_365 (x : Var) :
    (nb077_alpha_dummy_136 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_136] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_366 (F : Class) (I : Class) :
    (nb077_alpha_dummy_179 F I) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_179] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_367 (x : Var) :
    (nb077_alpha_dummy_180 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_180] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_368 (F : Class) (I : Class) :
    (nb077_alpha_dummy_215 F I) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_215] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_369 (x : Var) :
    (nb077_alpha_dummy_216 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_216] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_370 (F : Class) (I : Class) :
    (nb077_alpha_dummy_251 F I) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_251] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_371 (x : Var) :
    (nb077_alpha_dummy_252 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_252] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_372 (F : Class) (I : Class) :
    (nb077_alpha_dummy_291 F I) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_291] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_373 (x : Var) :
    (nb077_alpha_dummy_292 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_292] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_374 (F : Class) (I : Class) :
    (nb077_alpha_dummy_343 F I) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_343] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_375 (x : Var) :
    (nb077_alpha_dummy_344 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_344] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb077_fresh_376 (F : Class) (I : Class) :
    (nb077_alpha_dummy_013 F I) ∉
      (((syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪
        ((Class.cv (nb077_alpha_dummy_001 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_013] using
    freshVar_not_mem
      (((syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪
        ((Class.cv (nb077_alpha_dummy_001 F I))).fv)
      0

theorem nb077_fresh_377 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_014 x F I) ∉
      (((syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪
        ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_014] using
    freshVar_not_mem
      (((syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪
        ((Class.cv (nb077_alpha_dummy_002 x F I))).fv)
      0

theorem nb077_fresh_378 (F : Class) (I : Class) :
    (nb077_alpha_dummy_139 F I) ∉
      (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪
        ((syn_c1st)).fv) :=
  by
  simpa only [nb077_alpha_dummy_139] using
    freshVar_not_mem
      (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
      0

theorem nb077_fresh_379 (F : Class) (I : Class) :
    (nb077_alpha_dummy_140 F I) ∉
      (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪
        ((syn_c1st)).fv) :=
  by
  simpa only [nb077_alpha_dummy_140] using
    freshVar_not_mem
      (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
      1

theorem nb077_fresh_380 (F : Class) (I : Class) :
    (nb077_alpha_dummy_141 F I) ∉
      (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪
        ((syn_c1st)).fv) :=
  by
  simpa only [nb077_alpha_dummy_141] using
    freshVar_not_mem
      (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
      2

theorem nb077_distinct_381 (F : Class) (I : Class) :
    (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_140 F I) := by
  simpa only [nb077_alpha_dummy_139, nb077_alpha_dummy_140] using
    (freshVar_injective (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_382 (F : Class) (I : Class) :
    (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_141 F I) := by
  simpa only [nb077_alpha_dummy_139, nb077_alpha_dummy_141] using
    (freshVar_injective (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_383 (F : Class) (I : Class) :
    (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_141 F I) := by
  simpa only [nb077_alpha_dummy_140, nb077_alpha_dummy_141] using
    (freshVar_injective (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_384 (x : Var) :
    (nb077_alpha_dummy_142 x) ∉
      (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) :=
  by
  simpa only [nb077_alpha_dummy_142] using
    freshVar_not_mem
      (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 0

theorem nb077_fresh_385 (x : Var) :
    (nb077_alpha_dummy_143 x) ∉
      (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) :=
  by
  simpa only [nb077_alpha_dummy_143] using
    freshVar_not_mem
      (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 1

theorem nb077_fresh_386 (x : Var) :
    (nb077_alpha_dummy_144 x) ∉
      (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) :=
  by
  simpa only [nb077_alpha_dummy_144] using
    freshVar_not_mem
      (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 2

theorem nb077_distinct_387 (x : Var) :
    (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_143 x) := by
  simpa only [nb077_alpha_dummy_142, nb077_alpha_dummy_143] using
    (freshVar_injective
      (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_388 (x : Var) :
    (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_144 x) := by
  simpa only [nb077_alpha_dummy_142, nb077_alpha_dummy_144] using
    (freshVar_injective
      (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_389 (x : Var) :
    (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_144 x) := by
  simpa only [nb077_alpha_dummy_143, nb077_alpha_dummy_144] using
    (freshVar_injective
      (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_390 (F : Class) (I : Class) :
    (nb077_alpha_dummy_039 F I) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I))
            (Class.cv (nb077_alpha_dummy_035 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I))
            (Class.cv (nb077_alpha_dummy_035 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I))
            (Class.cv (nb077_alpha_dummy_035 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I))
            (Class.cv (nb077_alpha_dummy_035 F I)))).fv)
      0

theorem nb077_fresh_391 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_040 x F I) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I))
            (Class.cv (nb077_alpha_dummy_038 x F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I))
            (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I))
            (Class.cv (nb077_alpha_dummy_038 x F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I))
            (Class.cv (nb077_alpha_dummy_038 x F I)))).fv)
      0

theorem nb077_fresh_392 (F : Class) (I : Class) :
    (nb077_alpha_dummy_087 F I) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I))
            (Class.cv (nb077_alpha_dummy_083 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I))
            (Class.cv (nb077_alpha_dummy_083 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_087] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I))
            (Class.cv (nb077_alpha_dummy_083 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I))
            (Class.cv (nb077_alpha_dummy_083 F I)))).fv)
      0

theorem nb077_fresh_393 (x : Var) :
    (nb077_alpha_dummy_088 x) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_085 x))
            (Class.cv (nb077_alpha_dummy_086 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_085 x))
            (Class.cv (nb077_alpha_dummy_086 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_088] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_085 x))
            (Class.cv (nb077_alpha_dummy_086 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_085 x))
            (Class.cv (nb077_alpha_dummy_086 x)))).fv)
      0

theorem nb077_fresh_394 (F : Class) (I : Class) :
    (nb077_alpha_dummy_123 F I) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I))
            (Class.cv (nb077_alpha_dummy_119 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I))
            (Class.cv (nb077_alpha_dummy_119 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_123] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I))
            (Class.cv (nb077_alpha_dummy_119 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I))
            (Class.cv (nb077_alpha_dummy_119 F I)))).fv)
      0

theorem nb077_fresh_395 (x : Var) :
    (nb077_alpha_dummy_124 x) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_121 x))
            (Class.cv (nb077_alpha_dummy_122 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_121 x))
            (Class.cv (nb077_alpha_dummy_122 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_124] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_121 x))
            (Class.cv (nb077_alpha_dummy_122 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_121 x))
            (Class.cv (nb077_alpha_dummy_122 x)))).fv)
      0

theorem nb077_fresh_396 (F : Class) (I : Class) :
    (nb077_alpha_dummy_167 F I) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I))
            (Class.cv (nb077_alpha_dummy_163 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I))
            (Class.cv (nb077_alpha_dummy_163 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_167] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I))
            (Class.cv (nb077_alpha_dummy_163 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I))
            (Class.cv (nb077_alpha_dummy_163 F I)))).fv)
      0

theorem nb077_fresh_397 (x : Var) :
    (nb077_alpha_dummy_168 x) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_165 x))
            (Class.cv (nb077_alpha_dummy_166 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_165 x))
            (Class.cv (nb077_alpha_dummy_166 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_168] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_165 x))
            (Class.cv (nb077_alpha_dummy_166 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_165 x))
            (Class.cv (nb077_alpha_dummy_166 x)))).fv)
      0

theorem nb077_fresh_398 (F : Class) (I : Class) :
    (nb077_alpha_dummy_203 F I) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I))
            (Class.cv (nb077_alpha_dummy_199 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I))
            (Class.cv (nb077_alpha_dummy_199 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_203] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I))
            (Class.cv (nb077_alpha_dummy_199 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I))
            (Class.cv (nb077_alpha_dummy_199 F I)))).fv)
      0

theorem nb077_fresh_399 (x : Var) :
    (nb077_alpha_dummy_204 x) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_201 x))
            (Class.cv (nb077_alpha_dummy_202 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_201 x))
            (Class.cv (nb077_alpha_dummy_202 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_204] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_201 x))
            (Class.cv (nb077_alpha_dummy_202 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_201 x))
            (Class.cv (nb077_alpha_dummy_202 x)))).fv)
      0

theorem nb077_fresh_400 (F : Class) (I : Class) :
    (nb077_alpha_dummy_239 F I) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I))
            (Class.cv (nb077_alpha_dummy_235 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I))
            (Class.cv (nb077_alpha_dummy_235 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_239] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I))
            (Class.cv (nb077_alpha_dummy_235 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I))
            (Class.cv (nb077_alpha_dummy_235 F I)))).fv)
      0

theorem nb077_fresh_401 (x : Var) :
    (nb077_alpha_dummy_240 x) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_237 x))
            (Class.cv (nb077_alpha_dummy_238 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_237 x))
            (Class.cv (nb077_alpha_dummy_238 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_240] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_237 x))
            (Class.cv (nb077_alpha_dummy_238 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_237 x))
            (Class.cv (nb077_alpha_dummy_238 x)))).fv)
      0

theorem nb077_fresh_402 (F : Class) (I : Class) :
    (nb077_alpha_dummy_279 F I) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I))
            (Class.cv (nb077_alpha_dummy_275 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I))
            (Class.cv (nb077_alpha_dummy_275 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_279] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I))
            (Class.cv (nb077_alpha_dummy_275 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I))
            (Class.cv (nb077_alpha_dummy_275 F I)))).fv)
      0

theorem nb077_fresh_403 (x : Var) :
    (nb077_alpha_dummy_280 x) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_277 x))
            (Class.cv (nb077_alpha_dummy_278 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_277 x))
            (Class.cv (nb077_alpha_dummy_278 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_280] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_277 x))
            (Class.cv (nb077_alpha_dummy_278 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_277 x))
            (Class.cv (nb077_alpha_dummy_278 x)))).fv)
      0

theorem nb077_fresh_404 (F : Class) (I : Class) :
    (nb077_alpha_dummy_301 F I) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I))
            (Class.cv (nb077_alpha_dummy_297 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I))
            (Class.cv (nb077_alpha_dummy_297 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_301] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I))
            (Class.cv (nb077_alpha_dummy_297 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I))
            (Class.cv (nb077_alpha_dummy_297 F I)))).fv)
      0

theorem nb077_fresh_405 (x : Var) :
    (nb077_alpha_dummy_302 x) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_299 x))
            (Class.cv (nb077_alpha_dummy_300 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_299 x))
            (Class.cv (nb077_alpha_dummy_300 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_302] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_299 x))
            (Class.cv (nb077_alpha_dummy_300 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_299 x))
            (Class.cv (nb077_alpha_dummy_300 x)))).fv)
      0

theorem nb077_fresh_406 (F : Class) (I : Class) :
    (nb077_alpha_dummy_331 F I) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I))
            (Class.cv (nb077_alpha_dummy_327 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I))
            (Class.cv (nb077_alpha_dummy_327 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_331] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I))
            (Class.cv (nb077_alpha_dummy_327 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I))
            (Class.cv (nb077_alpha_dummy_327 F I)))).fv)
      0

theorem nb077_fresh_407 (x : Var) :
    (nb077_alpha_dummy_332 x) ∉
      (((syn_cnin (Class.cv (nb077_alpha_dummy_329 x))
            (Class.cv (nb077_alpha_dummy_330 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_329 x))
            (Class.cv (nb077_alpha_dummy_330 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_332] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb077_alpha_dummy_329 x))
            (Class.cv (nb077_alpha_dummy_330 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_329 x))
            (Class.cv (nb077_alpha_dummy_330 x)))).fv)
      0

theorem nb077_fresh_408 (F : Class) (I : Class) :
    (nb077_alpha_dummy_055 F I) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin
            (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_055] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin
            (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv)
      0

theorem nb077_fresh_409 (x : Var) (F : Class) :
    (nb077_alpha_dummy_056 x F) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st))
              (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin
            (syn_ccom (syn_ccnv (syn_c1st))
              (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_056] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st))
              (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin
            (syn_ccom (syn_ccnv (syn_c1st))
              (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv)
      0

theorem nb077_fresh_410 (F : Class) (I : Class) :
    (nb077_alpha_dummy_011 F I) ∉
      (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_001 F I)))
            (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_001 F I)))
            (Class.cv (nb077_alpha_dummy_001 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_001 F I)))
            (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_001 F I)))
            (Class.cv (nb077_alpha_dummy_001 F I)))).fv)
      0

theorem nb077_fresh_411 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_012 x F I) ∉
      (((syn_cnin (syn_cima
              (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_002 x F I)))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_cima
              (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_002 x F I)))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_012] using
    freshVar_not_mem
      (((syn_cnin (syn_cima
              (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_002 x F I)))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_cima
              (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_002 x F I)))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv)
      0

theorem nb077_fresh_412 (F : Class) (I : Class) :
    (nb077_alpha_dummy_007 F I) ∉
      (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪
        ((syn_cnin (syn_csn (syn_cop (syn_c0c) I))
            (Class.cv (nb077_alpha_dummy_001 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_007] using
    freshVar_not_mem
      (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪
        ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv)
      0

theorem nb077_fresh_413 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_008 x F I) ∉
      (((syn_cnin (syn_csn (syn_cop (syn_c0c) I))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪
        ((syn_cnin (syn_csn (syn_cop (syn_c0c) I))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_cnin (syn_csn (syn_cop (syn_c0c) I))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪
        ((syn_cnin (syn_csn (syn_cop (syn_c0c) I))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv)
      0

theorem nb077_fresh_414 (F : Class) (I : Class) :
    (nb077_alpha_dummy_053 F I) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_053] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv)
      0

theorem nb077_fresh_415 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_054 x F I) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_054] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv)
      0

theorem nb077_fresh_416 (F : Class) (I : Class) :
    (nb077_alpha_dummy_101 F I) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_101] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv)
      0

theorem nb077_fresh_417 (x : Var) :
    (nb077_alpha_dummy_102 x) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_102] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv)
      0

theorem nb077_fresh_418 (F : Class) (I : Class) :
    (nb077_alpha_dummy_137 F I) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_137] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv)
      0

theorem nb077_fresh_419 (x : Var) :
    (nb077_alpha_dummy_138 x) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_138] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv)
      0

theorem nb077_fresh_420 (F : Class) (I : Class) :
    (nb077_alpha_dummy_181 F I) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_181] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv)
      0

theorem nb077_fresh_421 (x : Var) :
    (nb077_alpha_dummy_182 x) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_182] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv)
      0

theorem nb077_fresh_422 (F : Class) (I : Class) :
    (nb077_alpha_dummy_217 F I) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_217] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv)
      0

theorem nb077_fresh_423 (x : Var) :
    (nb077_alpha_dummy_218 x) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_218] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv)
      0

theorem nb077_fresh_424 (F : Class) (I : Class) :
    (nb077_alpha_dummy_253 F I) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_253] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv)
      0

theorem nb077_fresh_425 (x : Var) :
    (nb077_alpha_dummy_254 x) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_254] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv)
      0

theorem nb077_fresh_426 (F : Class) (I : Class) :
    (nb077_alpha_dummy_293 F I) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_293] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv)
      0

theorem nb077_fresh_427 (x : Var) :
    (nb077_alpha_dummy_294 x) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_294] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv)
      0

theorem nb077_fresh_428 (F : Class) (I : Class) :
    (nb077_alpha_dummy_345 F I) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_345] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv)
      0

theorem nb077_fresh_429 (x : Var) :
    (nb077_alpha_dummy_346 x) ∉
      (((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_346] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv)
      0

theorem nb077_fresh_430 (F : Class) (I : Class) :
    (nb077_alpha_dummy_015 F I) ∉
      (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_001 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_015] using
    freshVar_not_mem
      (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_001 F I))).fv)
      0

theorem nb077_fresh_431 (F : Class) (I : Class) :
    (nb077_alpha_dummy_016 F I) ∉
      (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_001 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_016] using
    freshVar_not_mem
      (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_001 F I))).fv)
      1

theorem nb077_distinct_432 (F : Class) (I : Class) :
    (nb077_alpha_dummy_015 F I) ≠ (nb077_alpha_dummy_016 F I) := by
  simpa only [nb077_alpha_dummy_015, nb077_alpha_dummy_016] using
    (freshVar_injective (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_001 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_433 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_017 x F I) ∉
      (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_017] using
    freshVar_not_mem
      (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_002 x F I))).fv)
      0

theorem nb077_fresh_434 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_018 x F I) ∉
      (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_018] using
    freshVar_not_mem
      (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_002 x F I))).fv)
      1

theorem nb077_distinct_435 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_018 x F I) := by
  simpa only [nb077_alpha_dummy_017, nb077_alpha_dummy_018] using
    (freshVar_injective
      (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_436 (F : Class) (I : Class) :
    (nb077_alpha_dummy_009 F I) ∉
      (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv)
      0

theorem nb077_fresh_437 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_010 x F I) ∉
      (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv)
      0

theorem nb077_fresh_438 (F : Class) (I : Class) :
    (nb077_alpha_dummy_001 F I) ∉
      (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod
            (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv) :=
  by
  simpa only [nb077_alpha_dummy_001] using
    freshVar_not_mem
      (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod
            (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv)
      0

theorem nb077_fresh_439 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_002 x F I) ∉
      (((syn_csn (syn_cop (syn_c0c) I))).fv ∪
        ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv) :=
  by
  simpa only [nb077_alpha_dummy_002] using
    freshVar_not_mem
      (((syn_csn (syn_cop (syn_c0c) I))).fv ∪
        ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv)
      0

theorem nb077_fresh_440 (F : Class) (I : Class) :
    (nb077_alpha_dummy_000 F I) ∉ ((F).fv ∪ (I).fv) := by
  simpa only [nb077_alpha_dummy_000] using freshVar_not_mem ((F).fv ∪ (I).fv) 0

theorem nb077_fresh_441 (F : Class) (I : Class) :
    (nb077_alpha_dummy_255 F I) ∉
      (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))).fv) :=
  by
  simpa only [nb077_alpha_dummy_255] using
    freshVar_not_mem
      (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))).fv)
      0

theorem nb077_fresh_442 (F : Class) (I : Class) :
    (nb077_alpha_dummy_257 F I) ∉
      (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_255 F I)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb077_alpha_dummy_000 F I)) (syn_cvv))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_255 F I))
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_257] using
    freshVar_not_mem
      (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_255 F I)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb077_alpha_dummy_000 F I)) (syn_cvv))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_255 F I))
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))))).fv)
      0

theorem nb077_fresh_443 (F : Class) (I : Class) :
    (nb077_alpha_dummy_065 F I) ∉
      (({(nb077_alpha_dummy_059 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_060 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_061 F I)
            (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_059 F I)) (syn_ccom
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))
                (Class.cv (nb077_alpha_dummy_061 F I)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_061 F I)) (syn_ccnv (syn_c1st))
                (Class.cv (nb077_alpha_dummy_060 F I)))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_065] using
    freshVar_not_mem
      (({(nb077_alpha_dummy_059 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_060 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_061 F I)
            (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_059 F I)) (syn_ccom
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))
                (Class.cv (nb077_alpha_dummy_061 F I)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_061 F I)) (syn_ccnv (syn_c1st))
                (Class.cv (nb077_alpha_dummy_060 F I)))))).fv)
      0

theorem nb077_fresh_444 (x : Var) :
    (nb077_alpha_dummy_066 x) ∉
      (({(nb077_alpha_dummy_062 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_063 x)} : Finset Var) ∪
        ((syn_wex (nb077_alpha_dummy_064 x) (syn_wa
              (syn_wbr (Class.cv (nb077_alpha_dummy_062 x))
                (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))
                (Class.cv (nb077_alpha_dummy_064 x)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_064 x)) (syn_ccnv (syn_c1st))
                (Class.cv (nb077_alpha_dummy_063 x)))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_066] using
    freshVar_not_mem
      (({(nb077_alpha_dummy_062 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_063 x)} : Finset Var) ∪
        ((syn_wex (nb077_alpha_dummy_064 x) (syn_wa
              (syn_wbr (Class.cv (nb077_alpha_dummy_062 x))
                (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))
                (Class.cv (nb077_alpha_dummy_064 x)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_064 x)) (syn_ccnv (syn_c1st))
                (Class.cv (nb077_alpha_dummy_063 x)))))).fv)
      0

theorem nb077_fresh_445 (F : Class) (I : Class) :
    (nb077_alpha_dummy_145 F I) ∉
      (({(nb077_alpha_dummy_139 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_140 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_141 F I)
            (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_139 F I)) (syn_c1st)
                (Class.cv (nb077_alpha_dummy_141 F I)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_141 F I))
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
                (Class.cv (nb077_alpha_dummy_140 F I)))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_145] using
    freshVar_not_mem
      (({(nb077_alpha_dummy_139 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_140 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_141 F I)
            (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_139 F I)) (syn_c1st)
                (Class.cv (nb077_alpha_dummy_141 F I)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_141 F I))
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
                (Class.cv (nb077_alpha_dummy_140 F I)))))).fv)
      0

theorem nb077_fresh_446 (x : Var) :
    (nb077_alpha_dummy_146 x) ∉
      (({(nb077_alpha_dummy_142 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_143 x)} : Finset Var) ∪
        ((syn_wex (nb077_alpha_dummy_144 x) (syn_wa
              (syn_wbr (Class.cv (nb077_alpha_dummy_142 x)) (syn_c1st)
                (Class.cv (nb077_alpha_dummy_144 x)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_144 x))
                (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
                (Class.cv (nb077_alpha_dummy_143 x)))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_146] using
    freshVar_not_mem
      (({(nb077_alpha_dummy_142 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_143 x)} : Finset Var) ∪
        ((syn_wex (nb077_alpha_dummy_144 x) (syn_wa
              (syn_wbr (Class.cv (nb077_alpha_dummy_142 x)) (syn_c1st)
                (Class.cv (nb077_alpha_dummy_144 x)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_144 x))
                (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
                (Class.cv (nb077_alpha_dummy_143 x)))))).fv)
      0

theorem nb077_fresh_447 (x : Var) :
    (nb077_alpha_dummy_256 x) ∉
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (syn_c1c))).fv) :=
  by
  simpa only [nb077_alpha_dummy_256] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (syn_c1c))).fv) 0

theorem nb077_fresh_448 (x : Var) :
    (nb077_alpha_dummy_258 x) ∉
      (({ x } : Finset Var) ∪ ({(nb077_alpha_dummy_256 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_256 x))
              (syn_cplc (Class.cv x) (syn_c1c))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_258] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({(nb077_alpha_dummy_256 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_256 x))
              (syn_cplc (Class.cv x) (syn_c1c))))).fv)
      0

theorem nb077_support_mem_0000 (F : Class) (I : Class) :
    (nb077_alpha_dummy_001 F I) ∈
      (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪
        ((syn_cnin (syn_csn (syn_cop (syn_c0c) I))
            (Class.cv (nb077_alpha_dummy_001 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0001 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_002 x F I) ∈
      (((syn_cnin (syn_csn (syn_cop (syn_c0c) I))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪
        ((syn_cnin (syn_csn (syn_cop (syn_c0c) I))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0002 (F : Class) (I : Class) :
    (nb077_alpha_dummy_001 F I) ∈
      (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0003 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_002 x F I) ∈
      (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0004 (F : Class) (I : Class) :
    (nb077_alpha_dummy_001 F I) ∈
      (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_001 F I)))
            (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_001 F I)))
            (Class.cv (nb077_alpha_dummy_001 F I)))).fv) :=
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
    (nb077_alpha_dummy_002 x F I) ∈
      (((syn_cnin (syn_cima
              (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_002 x F I)))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_cima
              (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_002 x F I)))
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) :=
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
    (nb077_alpha_dummy_001 F I) ∈
      (((syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪
        ((Class.cv (nb077_alpha_dummy_001 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0007 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_002 x F I) ∈
      (((syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪
        ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0008 (F : Class) (I : Class) :
    (nb077_alpha_dummy_001 F I) ∈
      (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_001 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0009 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_002 x F I) ∈
      (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪
        ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0010 (F : Class) (I : Class) :
    (nb077_alpha_dummy_016 F I) ∈
      (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_015 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0011 (F : Class) (I : Class) :
    (nb077_alpha_dummy_016 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I)
              (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_019 F I)
              (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_019 F I) from (by
          unfold nb077_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_020 F I) from (by
            unfold nb077_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0012 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_018 x F I) ∈
      (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0013 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_018 x F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I)
              (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
                (Class.cv (nb077_alpha_dummy_017 x F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_021 x F I) from (by
          unfold nb077_alpha_dummy_021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_022 x F I) from (by
            unfold nb077_alpha_dummy_022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0014 (F : Class) (I : Class) :
    (nb077_alpha_dummy_016 F I) ∈
      (((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_019 F I) from (by
          unfold nb077_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_020 F I) from (by
            unfold nb077_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0015 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_018 x F I) ∈
      (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_018 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_018 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_021 x F I) from (by
          unfold nb077_alpha_dummy_021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_022 x F I) from (by
            unfold nb077_alpha_dummy_022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0016 (F : Class) (I : Class) :
    (nb077_alpha_dummy_020 F I) ∈ (((Class.cv (nb077_alpha_dummy_020 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0017 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_022 x F I) ∈ (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0018 (F : Class) (I : Class) :
    (nb077_alpha_dummy_027 F I) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_027 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_027 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_027 F I))).fv) :=
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
    (nb077_alpha_dummy_029 x F I) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_029 x F I))).fv) :=
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
    (nb077_alpha_dummy_027 F I) ∈
      (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0021 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_029 x F I) ∈
      (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0022 (F : Class) (I : Class) :
    (nb077_alpha_dummy_034 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I))
            (Class.cv (nb077_alpha_dummy_035 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I))
            (Class.cv (nb077_alpha_dummy_035 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0023 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_037 x F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I))
            (Class.cv (nb077_alpha_dummy_038 x F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I))
            (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0024 (F : Class) (I : Class) :
    (nb077_alpha_dummy_034 F I) ∈
      (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_035 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0025 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_037 x F I) ∈
      (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0026 (F : Class) (I : Class) :
    (nb077_alpha_dummy_035 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I))
            (Class.cv (nb077_alpha_dummy_035 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I))
            (Class.cv (nb077_alpha_dummy_035 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0027 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_038 x F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I))
            (Class.cv (nb077_alpha_dummy_038 x F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I))
            (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0028 (F : Class) (I : Class) :
    (nb077_alpha_dummy_035 F I) ∈
      (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_035 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0029 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_038 x F I) ∈
      (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0030 (F : Class) (I : Class) :
    (nb077_alpha_dummy_034 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_034 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_035 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0031 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_037 x F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_037 x F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0032 (F : Class) (I : Class) :
    (nb077_alpha_dummy_034 F I) ∈
      (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_034 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0033 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_037 x F I) ∈
      (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_037 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0034 (F : Class) (I : Class) :
    (nb077_alpha_dummy_035 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_034 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_035 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0035 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_038 x F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_037 x F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0036 (F : Class) (I : Class) :
    (nb077_alpha_dummy_035 F I) ∈
      (((Class.cv (nb077_alpha_dummy_035 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_035 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0037 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_038 x F I) ∈
      (((Class.cv (nb077_alpha_dummy_038 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0038 (F : Class) (I : Class) :
    (nb077_alpha_dummy_015 F I) ∈
      (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_015 F I))).fv) :=
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
    (nb077_alpha_dummy_015 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I)
              (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_019 F I)
              (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_015 F I) ≠ (nb077_alpha_dummy_019 F I) from (by
          unfold nb077_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_015 F I) ≠ (nb077_alpha_dummy_020 F I) from (by
            unfold nb077_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0040 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_017 x F I) ∈
      (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0041 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_017 x F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I)
              (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
                (Class.cv (nb077_alpha_dummy_017 x F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_021 x F I) from (by
          unfold nb077_alpha_dummy_021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_022 x F I) from (by
            unfold nb077_alpha_dummy_022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0042 (F : Class) (I : Class) :
    (nb077_alpha_dummy_015 F I) ∈
      (((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_015 F I) ≠ (nb077_alpha_dummy_019 F I) from (by
          unfold nb077_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_015 F I) ≠ (nb077_alpha_dummy_020 F I) from (by
            unfold nb077_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0043 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_017 x F I) ∈
      (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_017 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I)
            (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_021 x F I) from (by
          unfold nb077_alpha_dummy_021;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_022 x F I) from (by
            unfold nb077_alpha_dummy_022;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0044 (F : Class) (I : Class) :
    (nb077_alpha_dummy_020 F I) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0045 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_022 x F I) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0046 (F : Class) (I : Class) :
    (nb077_alpha_dummy_020 F I) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0047 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_022 x F I) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0048 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ∈
      (({(nb077_alpha_dummy_059 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_060 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_061 F I)
            (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_059 F I)) (syn_ccom
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))
                (Class.cv (nb077_alpha_dummy_061 F I)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_061 F I)) (syn_ccnv (syn_c1st))
                (Class.cv (nb077_alpha_dummy_060 F I)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0049 (x : Var) :
    (nb077_alpha_dummy_062 x) ∈
      (({(nb077_alpha_dummy_062 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_063 x)} : Finset Var) ∪
        ((syn_wex (nb077_alpha_dummy_064 x) (syn_wa
              (syn_wbr (Class.cv (nb077_alpha_dummy_062 x))
                (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))
                (Class.cv (nb077_alpha_dummy_064 x)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_064 x)) (syn_ccnv (syn_c1st))
                (Class.cv (nb077_alpha_dummy_063 x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0050 (F : Class) (I : Class) :
    (nb077_alpha_dummy_060 F I) ∈
      (({(nb077_alpha_dummy_059 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_060 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_061 F I)
            (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_059 F I)) (syn_ccom
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))
                (Class.cv (nb077_alpha_dummy_061 F I)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_061 F I)) (syn_ccnv (syn_c1st))
                (Class.cv (nb077_alpha_dummy_060 F I)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0051 (x : Var) :
    (nb077_alpha_dummy_063 x) ∈
      (({(nb077_alpha_dummy_062 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_063 x)} : Finset Var) ∪
        ((syn_wex (nb077_alpha_dummy_064 x) (syn_wa
              (syn_wbr (Class.cv (nb077_alpha_dummy_062 x))
                (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))
                (Class.cv (nb077_alpha_dummy_064 x)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_064 x)) (syn_ccnv (syn_c1st))
                (Class.cv (nb077_alpha_dummy_063 x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0052 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ∈
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0053 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I)
              (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_067 F I)
              (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_067 F I) from (by
          unfold nb077_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_068 F I) from (by
            unfold nb077_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0054 (x : Var) :
    (nb077_alpha_dummy_062 x) ∈
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0055 (x : Var) :
    (nb077_alpha_dummy_062 x) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x)
              (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_069 x)
              (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_069 x) from (by
          unfold nb077_alpha_dummy_069;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_070 x) from (by
            unfold nb077_alpha_dummy_070;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0056 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ∈
      (((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_067 F I) from (by
          unfold nb077_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_068 F I) from (by
            unfold nb077_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0057 (x : Var) :
    (nb077_alpha_dummy_062 x) ∈
      (((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_069 x) from (by
          unfold nb077_alpha_dummy_069;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_070 x) from (by
            unfold nb077_alpha_dummy_070;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0058 (F : Class) (I : Class) :
    (nb077_alpha_dummy_068 F I) ∈ (((Class.cv (nb077_alpha_dummy_068 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0059 (x : Var) :
    (nb077_alpha_dummy_070 x) ∈ (((Class.cv (nb077_alpha_dummy_070 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0060 (F : Class) (I : Class) :
    (nb077_alpha_dummy_075 F I) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_075 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_075 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_075 F I))).fv) :=
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
    (nb077_alpha_dummy_077 x) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_077 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_077 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_077 x))).fv) :=
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
    (nb077_alpha_dummy_075 F I) ∈
      (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0063 (x : Var) :
    (nb077_alpha_dummy_077 x) ∈
      (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0064 (F : Class) (I : Class) :
    (nb077_alpha_dummy_082 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I))
            (Class.cv (nb077_alpha_dummy_083 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I))
            (Class.cv (nb077_alpha_dummy_083 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0065 (x : Var) :
    (nb077_alpha_dummy_085 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_085 x))
            (Class.cv (nb077_alpha_dummy_086 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_085 x))
            (Class.cv (nb077_alpha_dummy_086 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0066 (F : Class) (I : Class) :
    (nb077_alpha_dummy_082 F I) ∈
      (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_083 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0067 (x : Var) :
    (nb077_alpha_dummy_085 x) ∈
      (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0068 (F : Class) (I : Class) :
    (nb077_alpha_dummy_083 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I))
            (Class.cv (nb077_alpha_dummy_083 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I))
            (Class.cv (nb077_alpha_dummy_083 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0069 (x : Var) :
    (nb077_alpha_dummy_086 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_085 x))
            (Class.cv (nb077_alpha_dummy_086 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_085 x))
            (Class.cv (nb077_alpha_dummy_086 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0070 (F : Class) (I : Class) :
    (nb077_alpha_dummy_083 F I) ∈
      (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_083 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0071 (x : Var) :
    (nb077_alpha_dummy_086 x) ∈
      (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0072 (F : Class) (I : Class) :
    (nb077_alpha_dummy_082 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_082 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_083 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0073 (x : Var) :
    (nb077_alpha_dummy_085 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_085 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_086 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0074 (F : Class) (I : Class) :
    (nb077_alpha_dummy_082 F I) ∈
      (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_082 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0075 (x : Var) :
    (nb077_alpha_dummy_085 x) ∈
      (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_085 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0076 (F : Class) (I : Class) :
    (nb077_alpha_dummy_083 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_082 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_083 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0077 (x : Var) :
    (nb077_alpha_dummy_086 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_085 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_086 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0078 (F : Class) (I : Class) :
    (nb077_alpha_dummy_083 F I) ∈
      (((Class.cv (nb077_alpha_dummy_083 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_083 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0079 (x : Var) :
    (nb077_alpha_dummy_086 x) ∈
      (((Class.cv (nb077_alpha_dummy_086 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0080 (F : Class) (I : Class) :
    (nb077_alpha_dummy_060 F I) ∈
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0081 (F : Class) (I : Class) :
    (nb077_alpha_dummy_060 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I)
              (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_067 F I)
              (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_067 F I) from (by
          unfold nb077_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_068 F I) from (by
            unfold nb077_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0082 (x : Var) :
    (nb077_alpha_dummy_063 x) ∈
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0083 (x : Var) :
    (nb077_alpha_dummy_063 x) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x)
              (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_069 x)
              (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_069 x) from (by
          unfold nb077_alpha_dummy_069;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_070 x) from (by
            unfold nb077_alpha_dummy_070;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0084 (F : Class) (I : Class) :
    (nb077_alpha_dummy_060 F I) ∈
      (((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_067 F I) from (by
          unfold nb077_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_068 F I) from (by
            unfold nb077_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0085 (x : Var) :
    (nb077_alpha_dummy_063 x) ∈
      (((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_069 x) from (by
          unfold nb077_alpha_dummy_069;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_070 x) from (by
            unfold nb077_alpha_dummy_070;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0086 (F : Class) (I : Class) :
    (nb077_alpha_dummy_068 F I) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0087 (x : Var) :
    (nb077_alpha_dummy_070 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0088 (F : Class) (I : Class) :
    (nb077_alpha_dummy_068 F I) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0089 (x : Var) :
    (nb077_alpha_dummy_070 x) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0090 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ∈
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_061 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0091 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I)
              (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_103 F I)
              (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_103 F I) from (by
          unfold nb077_alpha_dummy_103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_104 F I) from (by
            unfold nb077_alpha_dummy_104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0092 (x : Var) :
    (nb077_alpha_dummy_062 x) ∈
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0093 (x : Var) :
    (nb077_alpha_dummy_062 x) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x)
              (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_105 x)
              (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_105 x) from (by
          unfold nb077_alpha_dummy_105;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_106 x) from (by
            unfold nb077_alpha_dummy_106;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0094 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ∈
      (((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_103 F I) from (by
          unfold nb077_alpha_dummy_103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_104 F I) from (by
            unfold nb077_alpha_dummy_104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0095 (x : Var) :
    (nb077_alpha_dummy_062 x) ∈
      (((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_105 x) from (by
          unfold nb077_alpha_dummy_105;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_106 x) from (by
            unfold nb077_alpha_dummy_106;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0096 (F : Class) (I : Class) :
    (nb077_alpha_dummy_104 F I) ∈ (((Class.cv (nb077_alpha_dummy_104 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0097 (x : Var) :
    (nb077_alpha_dummy_106 x) ∈ (((Class.cv (nb077_alpha_dummy_106 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0098 (F : Class) (I : Class) :
    (nb077_alpha_dummy_111 F I) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_111 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_111 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_111 F I))).fv) :=
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
    (nb077_alpha_dummy_113 x) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_113 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_113 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_113 x))).fv) :=
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
    (nb077_alpha_dummy_111 F I) ∈
      (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0101 (x : Var) :
    (nb077_alpha_dummy_113 x) ∈
      (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0102 (F : Class) (I : Class) :
    (nb077_alpha_dummy_118 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I))
            (Class.cv (nb077_alpha_dummy_119 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I))
            (Class.cv (nb077_alpha_dummy_119 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0103 (x : Var) :
    (nb077_alpha_dummy_121 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_121 x))
            (Class.cv (nb077_alpha_dummy_122 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_121 x))
            (Class.cv (nb077_alpha_dummy_122 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0104 (F : Class) (I : Class) :
    (nb077_alpha_dummy_118 F I) ∈
      (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_119 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0105 (x : Var) :
    (nb077_alpha_dummy_121 x) ∈
      (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0106 (F : Class) (I : Class) :
    (nb077_alpha_dummy_119 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I))
            (Class.cv (nb077_alpha_dummy_119 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I))
            (Class.cv (nb077_alpha_dummy_119 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0107 (x : Var) :
    (nb077_alpha_dummy_122 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_121 x))
            (Class.cv (nb077_alpha_dummy_122 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_121 x))
            (Class.cv (nb077_alpha_dummy_122 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0108 (F : Class) (I : Class) :
    (nb077_alpha_dummy_119 F I) ∈
      (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_119 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0109 (x : Var) :
    (nb077_alpha_dummy_122 x) ∈
      (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0110 (F : Class) (I : Class) :
    (nb077_alpha_dummy_118 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_118 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_119 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0111 (x : Var) :
    (nb077_alpha_dummy_121 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_121 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_122 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0112 (F : Class) (I : Class) :
    (nb077_alpha_dummy_118 F I) ∈
      (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_118 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0113 (x : Var) :
    (nb077_alpha_dummy_121 x) ∈
      (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_121 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0114 (F : Class) (I : Class) :
    (nb077_alpha_dummy_119 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_118 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_119 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0115 (x : Var) :
    (nb077_alpha_dummy_122 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_121 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_122 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0116 (F : Class) (I : Class) :
    (nb077_alpha_dummy_119 F I) ∈
      (((Class.cv (nb077_alpha_dummy_119 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_119 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0117 (x : Var) :
    (nb077_alpha_dummy_122 x) ∈
      (((Class.cv (nb077_alpha_dummy_122 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0118 (F : Class) (I : Class) :
    (nb077_alpha_dummy_061 F I) ∈
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_061 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0119 (F : Class) (I : Class) :
    (nb077_alpha_dummy_061 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I)
              (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_103 F I)
              (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_103 F I) from (by
          unfold nb077_alpha_dummy_103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_104 F I) from (by
            unfold nb077_alpha_dummy_104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0120 (x : Var) :
    (nb077_alpha_dummy_064 x) ∈
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0121 (x : Var) :
    (nb077_alpha_dummy_064 x) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x)
              (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_105 x)
              (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_105 x) from (by
          unfold nb077_alpha_dummy_105;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_106 x) from (by
            unfold nb077_alpha_dummy_106;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0122 (F : Class) (I : Class) :
    (nb077_alpha_dummy_061 F I) ∈
      (((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_103 F I) from (by
          unfold nb077_alpha_dummy_103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_104 F I) from (by
            unfold nb077_alpha_dummy_104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0123 (x : Var) :
    (nb077_alpha_dummy_064 x) ∈
      (((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_105 x) from (by
          unfold nb077_alpha_dummy_105;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_106 x) from (by
            unfold nb077_alpha_dummy_106;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0124 (F : Class) (I : Class) :
    (nb077_alpha_dummy_104 F I) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0125 (x : Var) :
    (nb077_alpha_dummy_106 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0126 (F : Class) (I : Class) :
    (nb077_alpha_dummy_104 F I) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0127 (x : Var) :
    (nb077_alpha_dummy_106 x) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0128 (F : Class) (I : Class) :
    (nb077_alpha_dummy_139 F I) ∈
      (({(nb077_alpha_dummy_139 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_140 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_141 F I)
            (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_139 F I)) (syn_c1st)
                (Class.cv (nb077_alpha_dummy_141 F I)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_141 F I))
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
                (Class.cv (nb077_alpha_dummy_140 F I)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0129 (x : Var) :
    (nb077_alpha_dummy_142 x) ∈
      (({(nb077_alpha_dummy_142 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_143 x)} : Finset Var) ∪
        ((syn_wex (nb077_alpha_dummy_144 x) (syn_wa
              (syn_wbr (Class.cv (nb077_alpha_dummy_142 x)) (syn_c1st)
                (Class.cv (nb077_alpha_dummy_144 x)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_144 x))
                (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
                (Class.cv (nb077_alpha_dummy_143 x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0130 (F : Class) (I : Class) :
    (nb077_alpha_dummy_140 F I) ∈
      (({(nb077_alpha_dummy_139 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_140 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_141 F I)
            (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_139 F I)) (syn_c1st)
                (Class.cv (nb077_alpha_dummy_141 F I)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_141 F I))
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
                (Class.cv (nb077_alpha_dummy_140 F I)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0131 (x : Var) :
    (nb077_alpha_dummy_143 x) ∈
      (({(nb077_alpha_dummy_142 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_143 x)} : Finset Var) ∪
        ((syn_wex (nb077_alpha_dummy_144 x) (syn_wa
              (syn_wbr (Class.cv (nb077_alpha_dummy_142 x)) (syn_c1st)
                (Class.cv (nb077_alpha_dummy_144 x)))
              (syn_wbr (Class.cv (nb077_alpha_dummy_144 x))
                (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
                (Class.cv (nb077_alpha_dummy_143 x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0132 (F : Class) (I : Class) :
    (nb077_alpha_dummy_139 F I) ∈
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0133 (F : Class) (I : Class) :
    (nb077_alpha_dummy_139 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I)
              (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_147 F I)
              (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_147 F I) from (by
          unfold nb077_alpha_dummy_147;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_148 F I) from (by
            unfold nb077_alpha_dummy_148;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0134 (x : Var) :
    (nb077_alpha_dummy_142 x) ∈
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0135 (x : Var) :
    (nb077_alpha_dummy_142 x) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x)
              (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_149 x)
              (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_149 x) from (by
          unfold nb077_alpha_dummy_149;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_150 x) from (by
            unfold nb077_alpha_dummy_150;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0136 (F : Class) (I : Class) :
    (nb077_alpha_dummy_139 F I) ∈
      (((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_147 F I) from (by
          unfold nb077_alpha_dummy_147;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_148 F I) from (by
            unfold nb077_alpha_dummy_148;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0137 (x : Var) :
    (nb077_alpha_dummy_142 x) ∈
      (((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_149 x) from (by
          unfold nb077_alpha_dummy_149;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_150 x) from (by
            unfold nb077_alpha_dummy_150;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0138 (F : Class) (I : Class) :
    (nb077_alpha_dummy_148 F I) ∈ (((Class.cv (nb077_alpha_dummy_148 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0139 (x : Var) :
    (nb077_alpha_dummy_150 x) ∈ (((Class.cv (nb077_alpha_dummy_150 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0140 (F : Class) (I : Class) :
    (nb077_alpha_dummy_155 F I) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_155 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_155 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_155 F I))).fv) :=
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
    (nb077_alpha_dummy_157 x) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_157 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_157 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_157 x))).fv) :=
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
    (nb077_alpha_dummy_155 F I) ∈
      (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0143 (x : Var) :
    (nb077_alpha_dummy_157 x) ∈
      (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0144 (F : Class) (I : Class) :
    (nb077_alpha_dummy_162 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I))
            (Class.cv (nb077_alpha_dummy_163 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I))
            (Class.cv (nb077_alpha_dummy_163 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0145 (x : Var) :
    (nb077_alpha_dummy_165 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_165 x))
            (Class.cv (nb077_alpha_dummy_166 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_165 x))
            (Class.cv (nb077_alpha_dummy_166 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0146 (F : Class) (I : Class) :
    (nb077_alpha_dummy_162 F I) ∈
      (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_163 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0147 (x : Var) :
    (nb077_alpha_dummy_165 x) ∈
      (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0148 (F : Class) (I : Class) :
    (nb077_alpha_dummy_163 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I))
            (Class.cv (nb077_alpha_dummy_163 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I))
            (Class.cv (nb077_alpha_dummy_163 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0149 (x : Var) :
    (nb077_alpha_dummy_166 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_165 x))
            (Class.cv (nb077_alpha_dummy_166 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_165 x))
            (Class.cv (nb077_alpha_dummy_166 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0150 (F : Class) (I : Class) :
    (nb077_alpha_dummy_163 F I) ∈
      (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_163 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0151 (x : Var) :
    (nb077_alpha_dummy_166 x) ∈
      (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0152 (F : Class) (I : Class) :
    (nb077_alpha_dummy_162 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_162 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_163 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0153 (x : Var) :
    (nb077_alpha_dummy_165 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_165 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_166 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0154 (F : Class) (I : Class) :
    (nb077_alpha_dummy_162 F I) ∈
      (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_162 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0155 (x : Var) :
    (nb077_alpha_dummy_165 x) ∈
      (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_165 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0156 (F : Class) (I : Class) :
    (nb077_alpha_dummy_163 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_162 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_163 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0157 (x : Var) :
    (nb077_alpha_dummy_166 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_165 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_166 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0158 (F : Class) (I : Class) :
    (nb077_alpha_dummy_163 F I) ∈
      (((Class.cv (nb077_alpha_dummy_163 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_163 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0159 (x : Var) :
    (nb077_alpha_dummy_166 x) ∈
      (((Class.cv (nb077_alpha_dummy_166 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0160 (F : Class) (I : Class) :
    (nb077_alpha_dummy_140 F I) ∈
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0161 (F : Class) (I : Class) :
    (nb077_alpha_dummy_140 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I)
              (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_147 F I)
              (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_147 F I) from (by
          unfold nb077_alpha_dummy_147;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0160 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_148 F I) from (by
            unfold nb077_alpha_dummy_148;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0160 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0162 (x : Var) :
    (nb077_alpha_dummy_143 x) ∈
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0163 (x : Var) :
    (nb077_alpha_dummy_143 x) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x)
              (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_149 x)
              (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_149 x) from (by
          unfold nb077_alpha_dummy_149;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_150 x) from (by
            unfold nb077_alpha_dummy_150;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0164 (F : Class) (I : Class) :
    (nb077_alpha_dummy_140 F I) ∈
      (((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_147 F I) from (by
          unfold nb077_alpha_dummy_147;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0160 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_148 F I) from (by
            unfold nb077_alpha_dummy_148;
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
    (nb077_alpha_dummy_143 x) ∈
      (((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_149 x) from (by
          unfold nb077_alpha_dummy_149;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_150 x) from (by
            unfold nb077_alpha_dummy_150;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0166 (F : Class) (I : Class) :
    (nb077_alpha_dummy_148 F I) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0167 (x : Var) :
    (nb077_alpha_dummy_150 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0168 (F : Class) (I : Class) :
    (nb077_alpha_dummy_148 F I) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0169 (x : Var) :
    (nb077_alpha_dummy_150 x) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0170 (F : Class) (I : Class) :
    (nb077_alpha_dummy_139 F I) ∈
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_141 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0171 (F : Class) (I : Class) :
    (nb077_alpha_dummy_139 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I)
              (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_183 F I)
              (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_183 F I) from (by
          unfold nb077_alpha_dummy_183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_184 F I) from (by
            unfold nb077_alpha_dummy_184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0172 (x : Var) :
    (nb077_alpha_dummy_142 x) ∈
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0173 (x : Var) :
    (nb077_alpha_dummy_142 x) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x)
              (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_185 x)
              (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_185 x) from (by
          unfold nb077_alpha_dummy_185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_186 x) from (by
            unfold nb077_alpha_dummy_186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0174 (F : Class) (I : Class) :
    (nb077_alpha_dummy_139 F I) ∈
      (((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_183 F I) from (by
          unfold nb077_alpha_dummy_183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_184 F I) from (by
            unfold nb077_alpha_dummy_184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0175 (x : Var) :
    (nb077_alpha_dummy_142 x) ∈
      (((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_185 x) from (by
          unfold nb077_alpha_dummy_185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_186 x) from (by
            unfold nb077_alpha_dummy_186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0176 (F : Class) (I : Class) :
    (nb077_alpha_dummy_184 F I) ∈ (((Class.cv (nb077_alpha_dummy_184 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0177 (x : Var) :
    (nb077_alpha_dummy_186 x) ∈ (((Class.cv (nb077_alpha_dummy_186 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0178 (F : Class) (I : Class) :
    (nb077_alpha_dummy_191 F I) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_191 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_191 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_191 F I))).fv) :=
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
    (nb077_alpha_dummy_193 x) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_193 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_193 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_193 x))).fv) :=
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
    (nb077_alpha_dummy_191 F I) ∈
      (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0181 (x : Var) :
    (nb077_alpha_dummy_193 x) ∈
      (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0182 (F : Class) (I : Class) :
    (nb077_alpha_dummy_198 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I))
            (Class.cv (nb077_alpha_dummy_199 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I))
            (Class.cv (nb077_alpha_dummy_199 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0183 (x : Var) :
    (nb077_alpha_dummy_201 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_201 x))
            (Class.cv (nb077_alpha_dummy_202 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_201 x))
            (Class.cv (nb077_alpha_dummy_202 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0184 (F : Class) (I : Class) :
    (nb077_alpha_dummy_198 F I) ∈
      (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_199 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0185 (x : Var) :
    (nb077_alpha_dummy_201 x) ∈
      (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0186 (F : Class) (I : Class) :
    (nb077_alpha_dummy_199 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I))
            (Class.cv (nb077_alpha_dummy_199 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I))
            (Class.cv (nb077_alpha_dummy_199 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0187 (x : Var) :
    (nb077_alpha_dummy_202 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_201 x))
            (Class.cv (nb077_alpha_dummy_202 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_201 x))
            (Class.cv (nb077_alpha_dummy_202 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0188 (F : Class) (I : Class) :
    (nb077_alpha_dummy_199 F I) ∈
      (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_199 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0189 (x : Var) :
    (nb077_alpha_dummy_202 x) ∈
      (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0190 (F : Class) (I : Class) :
    (nb077_alpha_dummy_198 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_198 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_199 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0191 (x : Var) :
    (nb077_alpha_dummy_201 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_201 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_202 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0192 (F : Class) (I : Class) :
    (nb077_alpha_dummy_198 F I) ∈
      (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_198 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0193 (x : Var) :
    (nb077_alpha_dummy_201 x) ∈
      (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_201 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0194 (F : Class) (I : Class) :
    (nb077_alpha_dummy_199 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_198 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_199 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0195 (x : Var) :
    (nb077_alpha_dummy_202 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_201 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_202 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0196 (F : Class) (I : Class) :
    (nb077_alpha_dummy_199 F I) ∈
      (((Class.cv (nb077_alpha_dummy_199 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_199 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0197 (x : Var) :
    (nb077_alpha_dummy_202 x) ∈
      (((Class.cv (nb077_alpha_dummy_202 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0198 (F : Class) (I : Class) :
    (nb077_alpha_dummy_141 F I) ∈
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_141 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0199 (F : Class) (I : Class) :
    (nb077_alpha_dummy_141 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I)
              (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_183 F I)
              (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_183 F I) from (by
          unfold nb077_alpha_dummy_183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_184 F I) from (by
            unfold nb077_alpha_dummy_184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0200 (x : Var) :
    (nb077_alpha_dummy_144 x) ∈
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0201 (x : Var) :
    (nb077_alpha_dummy_144 x) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x)
              (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_185 x)
              (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_185 x) from (by
          unfold nb077_alpha_dummy_185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_186 x) from (by
            unfold nb077_alpha_dummy_186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0202 (F : Class) (I : Class) :
    (nb077_alpha_dummy_141 F I) ∈
      (((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_183 F I) from (by
          unfold nb077_alpha_dummy_183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_184 F I) from (by
            unfold nb077_alpha_dummy_184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0203 (x : Var) :
    (nb077_alpha_dummy_144 x) ∈
      (((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_185 x) from (by
          unfold nb077_alpha_dummy_185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_186 x) from (by
            unfold nb077_alpha_dummy_186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0204 (F : Class) (I : Class) :
    (nb077_alpha_dummy_184 F I) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0205 (x : Var) :
    (nb077_alpha_dummy_186 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0206 (F : Class) (I : Class) :
    (nb077_alpha_dummy_184 F I) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0207 (x : Var) :
    (nb077_alpha_dummy_186 x) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0208 (F : Class) (I : Class) :
    (nb077_alpha_dummy_141 F I) ∈
      (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0209 (F : Class) (I : Class) :
    (nb077_alpha_dummy_141 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I)
              (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_219 F I)
              (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_219 F I) from (by
          unfold nb077_alpha_dummy_219;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_220 F I) from (by
            unfold nb077_alpha_dummy_220;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0210 (x : Var) :
    (nb077_alpha_dummy_144 x) ∈
      (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0211 (x : Var) :
    (nb077_alpha_dummy_144 x) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x)
              (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_221 x)
              (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_221 x) from (by
          unfold nb077_alpha_dummy_221;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_222 x) from (by
            unfold nb077_alpha_dummy_222;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0212 (F : Class) (I : Class) :
    (nb077_alpha_dummy_141 F I) ∈
      (((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_219 F I) from (by
          unfold nb077_alpha_dummy_219;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_220 F I) from (by
            unfold nb077_alpha_dummy_220;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0213 (x : Var) :
    (nb077_alpha_dummy_144 x) ∈
      (((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_221 x) from (by
          unfold nb077_alpha_dummy_221;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_222 x) from (by
            unfold nb077_alpha_dummy_222;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0214 (F : Class) (I : Class) :
    (nb077_alpha_dummy_220 F I) ∈ (((Class.cv (nb077_alpha_dummy_220 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0215 (x : Var) :
    (nb077_alpha_dummy_222 x) ∈ (((Class.cv (nb077_alpha_dummy_222 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0216 (F : Class) (I : Class) :
    (nb077_alpha_dummy_227 F I) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_227 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_227 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_227 F I))).fv) :=
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
    (nb077_alpha_dummy_229 x) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_229 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_229 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_229 x))).fv) :=
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
    (nb077_alpha_dummy_227 F I) ∈
      (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0219 (x : Var) :
    (nb077_alpha_dummy_229 x) ∈
      (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0220 (F : Class) (I : Class) :
    (nb077_alpha_dummy_234 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I))
            (Class.cv (nb077_alpha_dummy_235 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I))
            (Class.cv (nb077_alpha_dummy_235 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0221 (x : Var) :
    (nb077_alpha_dummy_237 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_237 x))
            (Class.cv (nb077_alpha_dummy_238 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_237 x))
            (Class.cv (nb077_alpha_dummy_238 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0222 (F : Class) (I : Class) :
    (nb077_alpha_dummy_234 F I) ∈
      (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_235 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0223 (x : Var) :
    (nb077_alpha_dummy_237 x) ∈
      (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0224 (F : Class) (I : Class) :
    (nb077_alpha_dummy_235 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I))
            (Class.cv (nb077_alpha_dummy_235 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I))
            (Class.cv (nb077_alpha_dummy_235 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0225 (x : Var) :
    (nb077_alpha_dummy_238 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_237 x))
            (Class.cv (nb077_alpha_dummy_238 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_237 x))
            (Class.cv (nb077_alpha_dummy_238 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0226 (F : Class) (I : Class) :
    (nb077_alpha_dummy_235 F I) ∈
      (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_235 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0227 (x : Var) :
    (nb077_alpha_dummy_238 x) ∈
      (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0228 (F : Class) (I : Class) :
    (nb077_alpha_dummy_234 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_234 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_235 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0229 (x : Var) :
    (nb077_alpha_dummy_237 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_237 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_238 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0230 (F : Class) (I : Class) :
    (nb077_alpha_dummy_234 F I) ∈
      (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_234 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0231 (x : Var) :
    (nb077_alpha_dummy_237 x) ∈
      (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_237 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0232 (F : Class) (I : Class) :
    (nb077_alpha_dummy_235 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_234 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_235 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0233 (x : Var) :
    (nb077_alpha_dummy_238 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_237 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_238 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0234 (F : Class) (I : Class) :
    (nb077_alpha_dummy_235 F I) ∈
      (((Class.cv (nb077_alpha_dummy_235 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_235 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0235 (x : Var) :
    (nb077_alpha_dummy_238 x) ∈
      (((Class.cv (nb077_alpha_dummy_238 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0236 (F : Class) (I : Class) :
    (nb077_alpha_dummy_140 F I) ∈
      (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0237 (F : Class) (I : Class) :
    (nb077_alpha_dummy_140 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I)
              (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_219 F I)
              (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_219 F I) from (by
          unfold nb077_alpha_dummy_219;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_220 F I) from (by
            unfold nb077_alpha_dummy_220;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0238 (x : Var) :
    (nb077_alpha_dummy_143 x) ∈
      (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0239 (x : Var) :
    (nb077_alpha_dummy_143 x) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x)
              (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_221 x)
              (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_221 x) from (by
          unfold nb077_alpha_dummy_221;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_222 x) from (by
            unfold nb077_alpha_dummy_222;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0240 (F : Class) (I : Class) :
    (nb077_alpha_dummy_140 F I) ∈
      (((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_219 F I) from (by
          unfold nb077_alpha_dummy_219;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_220 F I) from (by
            unfold nb077_alpha_dummy_220;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0241 (x : Var) :
    (nb077_alpha_dummy_143 x) ∈
      (((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_221 x) from (by
          unfold nb077_alpha_dummy_221;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_222 x) from (by
            unfold nb077_alpha_dummy_222;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0242 (F : Class) (I : Class) :
    (nb077_alpha_dummy_220 F I) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0243 (x : Var) :
    (nb077_alpha_dummy_222 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0244 (F : Class) (I : Class) :
    (nb077_alpha_dummy_220 F I) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0245 (x : Var) :
    (nb077_alpha_dummy_222 x) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0246 (F : Class) (I : Class) :
    (nb077_alpha_dummy_000 F I) ∈
      (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_255 F I)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb077_alpha_dummy_000 F I)) (syn_cvv))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_255 F I))
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0247 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({(nb077_alpha_dummy_256 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_256 x))
              (syn_cplc (Class.cv x) (syn_c1c))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0248 (F : Class) (I : Class) :
    (nb077_alpha_dummy_255 F I) ∈
      (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪
          ({(nb077_alpha_dummy_255 F I)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb077_alpha_dummy_000 F I)) (syn_cvv))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_255 F I))
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0249 (x : Var) :
    (nb077_alpha_dummy_256 x) ∈
      (({ x } : Finset Var) ∪ ({(nb077_alpha_dummy_256 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_256 x))
              (syn_cplc (Class.cv x) (syn_c1c))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0250 (F : Class) (I : Class) :
    (nb077_alpha_dummy_000 F I) ∈
      (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0251 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (syn_c1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0252 (F : Class) (I : Class) :
    (nb077_alpha_dummy_000 F I) ∈
      (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_255 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0253 (F : Class) (I : Class) :
    (nb077_alpha_dummy_000 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I)
              (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_259 F I)
              (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_259 F I) from (by
          unfold nb077_alpha_dummy_259;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_260 F I) from (by
            unfold nb077_alpha_dummy_260;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0254 (x : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0255 (x : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x)
              (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_261 x)
              (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb077_alpha_dummy_261 x) from (by
          unfold nb077_alpha_dummy_261;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb077_alpha_dummy_262 x) from (by
            unfold nb077_alpha_dummy_262;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0256 (F : Class) (I : Class) :
    (nb077_alpha_dummy_000 F I) ∈
      (((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_259 F I) from (by
          unfold nb077_alpha_dummy_259;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_260 F I) from (by
            unfold nb077_alpha_dummy_260;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0257 (x : Var) :
    x ∈
      (((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb077_alpha_dummy_261 x) from (by
          unfold nb077_alpha_dummy_261;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb077_alpha_dummy_262 x) from (by
            unfold nb077_alpha_dummy_262;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0258 (F : Class) (I : Class) :
    (nb077_alpha_dummy_260 F I) ∈ (((Class.cv (nb077_alpha_dummy_260 F I))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0259 (x : Var) :
    (nb077_alpha_dummy_262 x) ∈ (((Class.cv (nb077_alpha_dummy_262 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0260 (F : Class) (I : Class) :
    (nb077_alpha_dummy_267 F I) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_267 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_267 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_267 F I))).fv) :=
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
    (nb077_alpha_dummy_269 x) ∈
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_269 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_269 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_269 x))).fv) :=
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
    (nb077_alpha_dummy_267 F I) ∈
      (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0263 (x : Var) :
    (nb077_alpha_dummy_269 x) ∈
      (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0264 (F : Class) (I : Class) :
    (nb077_alpha_dummy_274 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I))
            (Class.cv (nb077_alpha_dummy_275 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I))
            (Class.cv (nb077_alpha_dummy_275 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0265 (x : Var) :
    (nb077_alpha_dummy_277 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_277 x))
            (Class.cv (nb077_alpha_dummy_278 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_277 x))
            (Class.cv (nb077_alpha_dummy_278 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0266 (F : Class) (I : Class) :
    (nb077_alpha_dummy_274 F I) ∈
      (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_275 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0267 (x : Var) :
    (nb077_alpha_dummy_277 x) ∈
      (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0268 (F : Class) (I : Class) :
    (nb077_alpha_dummy_275 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I))
            (Class.cv (nb077_alpha_dummy_275 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I))
            (Class.cv (nb077_alpha_dummy_275 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0269 (x : Var) :
    (nb077_alpha_dummy_278 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_277 x))
            (Class.cv (nb077_alpha_dummy_278 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_277 x))
            (Class.cv (nb077_alpha_dummy_278 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0270 (F : Class) (I : Class) :
    (nb077_alpha_dummy_275 F I) ∈
      (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_275 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0271 (x : Var) :
    (nb077_alpha_dummy_278 x) ∈
      (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0272 (F : Class) (I : Class) :
    (nb077_alpha_dummy_274 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_274 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_275 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0273 (x : Var) :
    (nb077_alpha_dummy_277 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_277 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_278 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0274 (F : Class) (I : Class) :
    (nb077_alpha_dummy_274 F I) ∈
      (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_274 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0275 (x : Var) :
    (nb077_alpha_dummy_277 x) ∈
      (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_277 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0276 (F : Class) (I : Class) :
    (nb077_alpha_dummy_275 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_274 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_275 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0277 (x : Var) :
    (nb077_alpha_dummy_278 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_277 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_278 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0278 (F : Class) (I : Class) :
    (nb077_alpha_dummy_275 F I) ∈
      (((Class.cv (nb077_alpha_dummy_275 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_275 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0279 (x : Var) :
    (nb077_alpha_dummy_278 x) ∈
      (((Class.cv (nb077_alpha_dummy_278 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0280 (F : Class) (I : Class) :
    (nb077_alpha_dummy_255 F I) ∈
      (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_255 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0281 (F : Class) (I : Class) :
    (nb077_alpha_dummy_255 F I) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I)
              (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_259 F I)
              (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_255 F I) ≠ (nb077_alpha_dummy_259 F I) from (by
          unfold nb077_alpha_dummy_259;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_255 F I) ≠ (nb077_alpha_dummy_260 F I) from (by
            unfold nb077_alpha_dummy_260;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0282 (x : Var) :
    (nb077_alpha_dummy_256 x) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0283 (x : Var) :
    (nb077_alpha_dummy_256 x) ∈
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x)
              (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_261 x)
              (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_256 x) ≠ (nb077_alpha_dummy_261 x) from (by
          unfold nb077_alpha_dummy_261;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_256 x) ≠ (nb077_alpha_dummy_262 x) from (by
            unfold nb077_alpha_dummy_262;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0284 (F : Class) (I : Class) :
    (nb077_alpha_dummy_255 F I) ∈
      (((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_255 F I) ≠ (nb077_alpha_dummy_259 F I) from (by
          unfold nb077_alpha_dummy_259;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_255 F I) ≠ (nb077_alpha_dummy_260 F I) from (by
            unfold nb077_alpha_dummy_260;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0285 (x : Var) :
    (nb077_alpha_dummy_256 x) ∈
      (((Class.cab (nb077_alpha_dummy_261 x)
            (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x)
            (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb077_alpha_dummy_256 x) ≠ (nb077_alpha_dummy_261 x) from (by
          unfold nb077_alpha_dummy_261;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb077_alpha_dummy_256 x) ≠ (nb077_alpha_dummy_262 x) from (by
            unfold nb077_alpha_dummy_262;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0286 (F : Class) (I : Class) :
    (nb077_alpha_dummy_260 F I) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0287 (x : Var) :
    (nb077_alpha_dummy_262 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0288 (F : Class) (I : Class) :
    (nb077_alpha_dummy_260 F I) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0289 (x : Var) :
    (nb077_alpha_dummy_262 x) ∈
      (((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv ∪
        ((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0290 (F : Class) (I : Class) :
    (nb077_alpha_dummy_000 F I) ∈
      (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0291 (x : Var) : x ∈ (((Class.cv x)).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0292 (F : Class) (I : Class) :
    (nb077_alpha_dummy_296 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I))
            (Class.cv (nb077_alpha_dummy_297 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I))
            (Class.cv (nb077_alpha_dummy_297 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0293 (x : Var) :
    (nb077_alpha_dummy_299 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_299 x))
            (Class.cv (nb077_alpha_dummy_300 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_299 x))
            (Class.cv (nb077_alpha_dummy_300 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0294 (F : Class) (I : Class) :
    (nb077_alpha_dummy_296 F I) ∈
      (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_297 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0295 (x : Var) :
    (nb077_alpha_dummy_299 x) ∈
      (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0296 (F : Class) (I : Class) :
    (nb077_alpha_dummy_297 F I) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I))
            (Class.cv (nb077_alpha_dummy_297 F I)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I))
            (Class.cv (nb077_alpha_dummy_297 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0297 (x : Var) :
    (nb077_alpha_dummy_300 x) ∈
      (((syn_cnin (Class.cv (nb077_alpha_dummy_299 x))
            (Class.cv (nb077_alpha_dummy_300 x)))).fv ∪
        ((syn_cnin (Class.cv (nb077_alpha_dummy_299 x))
            (Class.cv (nb077_alpha_dummy_300 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0298 (F : Class) (I : Class) :
    (nb077_alpha_dummy_297 F I) ∈
      (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_297 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0299 (x : Var) :
    (nb077_alpha_dummy_300 x) ∈
      (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0300 (F : Class) (I : Class) :
    (nb077_alpha_dummy_296 F I) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_296 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_297 F I)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0301 (x : Var) :
    (nb077_alpha_dummy_299 x) ∈
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_299 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_300 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0302 (F : Class) (I : Class) :
    (nb077_alpha_dummy_296 F I) ∈
      (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_296 F I))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0303 (x : Var) :
    (nb077_alpha_dummy_299 x) ∈
      (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_299 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
