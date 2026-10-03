/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C067C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C067C001Part006`. -/


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

theorem nb067_fresh_371 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_068 x y f) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_061 x y f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_068] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_061 x y f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_062 x y f)))).fv)
      0

theorem nb067_fresh_372 :
    (nb067_alpha_dummy_115) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_106)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_107)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_115] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_106)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_107)))).fv)
      0

theorem nb067_fresh_373 (f : Var) :
    (nb067_alpha_dummy_116 f) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_109 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_110 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_116] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_109 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_110 f)))).fv)
      0

theorem nb067_fresh_374 :
    (nb067_alpha_dummy_151) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_142)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_143)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_151] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_142)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_143)))).fv)
      0

theorem nb067_fresh_375 (f : Var) :
    (nb067_alpha_dummy_152 f) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_145 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_146 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_152] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_145 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_146 f)))).fv)
      0

theorem nb067_fresh_376 :
    (nb067_alpha_dummy_193) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_184)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_185)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_193] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_184)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_185)))).fv)
      0

theorem nb067_fresh_377 (f : Var) :
    (nb067_alpha_dummy_194 f) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_187 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_188 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_194] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_187 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_188 f)))).fv)
      0

theorem nb067_fresh_378 :
    (nb067_alpha_dummy_229) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_220)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_221)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_229] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_220)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_221)))).fv)
      0

theorem nb067_fresh_379 (f : Var) :
    (nb067_alpha_dummy_230 f) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_223 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_224 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_230] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_223 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_224 f)))).fv)
      0

theorem nb067_fresh_380 :
    (nb067_alpha_dummy_265) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_256)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_257)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_265] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_256)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_257)))).fv)
      0

theorem nb067_fresh_381 (f : Var) :
    (nb067_alpha_dummy_266 f) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_259 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_260 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_266] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_259 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_260 f)))).fv)
      0

theorem nb067_fresh_382 :
    (nb067_alpha_dummy_305) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_296)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_297)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_305] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_296)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_297)))).fv)
      0

theorem nb067_fresh_383 (f : Var) :
    (nb067_alpha_dummy_306 f) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_299 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_300 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_306] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_299 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_300 f)))).fv)
      0

theorem nb067_fresh_384 :
    (nb067_alpha_dummy_349) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_340)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_341)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_349] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_340)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_341)))).fv)
      0

theorem nb067_fresh_385 (f : Var) :
    (nb067_alpha_dummy_350 f) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_343 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_344 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_350] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_343 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_344 f)))).fv)
      0

theorem nb067_fresh_386 :
    (nb067_alpha_dummy_075) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_008))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_075] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_008))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_387 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_076 x y f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_076] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_388 :
    (nb067_alpha_dummy_047) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_016))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_016))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_389 (x : Var) (y : Var) :
    (nb067_alpha_dummy_048 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_390 :
    (nb067_alpha_dummy_123) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_092))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_123] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_092))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_391 (f : Var) :
    (nb067_alpha_dummy_124 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_124] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_392 :
    (nb067_alpha_dummy_159) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_128))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_159] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_128))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_393 (f : Var) :
    (nb067_alpha_dummy_160 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_160] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_394 :
    (nb067_alpha_dummy_201) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_170))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_201] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_170))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_395 (f : Var) :
    (nb067_alpha_dummy_202 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_202] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_396 :
    (nb067_alpha_dummy_237) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_206))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_237] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_206))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_397 (f : Var) :
    (nb067_alpha_dummy_238 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_238] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_398 :
    (nb067_alpha_dummy_273) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_242))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_273] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_242))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_399 (f : Var) :
    (nb067_alpha_dummy_274 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_274] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_400 :
    (nb067_alpha_dummy_313) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_282))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_313] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_282))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_401 (f : Var) :
    (nb067_alpha_dummy_314 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_314] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_402 :
    (nb067_alpha_dummy_357) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_326))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_357] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_326))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_403 (f : Var) :
    (nb067_alpha_dummy_358 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_358] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb067_fresh_404 :
    (nb067_alpha_dummy_035) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_030))
            (Class.cv (nb067_alpha_dummy_031)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_035] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv)
      0

theorem nb067_fresh_405 (x : Var) (y : Var) :
    (nb067_alpha_dummy_036 x y) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y))
            (Class.cv (nb067_alpha_dummy_034 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y))
            (Class.cv (nb067_alpha_dummy_034 x y)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_036] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y))
            (Class.cv (nb067_alpha_dummy_034 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y))
            (Class.cv (nb067_alpha_dummy_034 x y)))).fv)
      0

theorem nb067_fresh_406 :
    (nb067_alpha_dummy_063) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_058))
            (Class.cv (nb067_alpha_dummy_059)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_063] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv)
      0

theorem nb067_fresh_407 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_064 x y f) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f))
            (Class.cv (nb067_alpha_dummy_062 x y f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f))
            (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_064] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f))
            (Class.cv (nb067_alpha_dummy_062 x y f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f))
            (Class.cv (nb067_alpha_dummy_062 x y f)))).fv)
      0

theorem nb067_fresh_408 :
    (nb067_alpha_dummy_111) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_106))
            (Class.cv (nb067_alpha_dummy_107)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_111] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv)
      0

theorem nb067_fresh_409 (f : Var) :
    (nb067_alpha_dummy_112 f) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_112] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f)))).fv)
      0

theorem nb067_fresh_410 :
    (nb067_alpha_dummy_147) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_142))
            (Class.cv (nb067_alpha_dummy_143)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_147] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv)
      0

theorem nb067_fresh_411 (f : Var) :
    (nb067_alpha_dummy_148 f) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_148] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f)))).fv)
      0

theorem nb067_fresh_412 :
    (nb067_alpha_dummy_189) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_184))
            (Class.cv (nb067_alpha_dummy_185)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_189] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv)
      0

theorem nb067_fresh_413 (f : Var) :
    (nb067_alpha_dummy_190 f) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_190] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f)))).fv)
      0

theorem nb067_fresh_414 :
    (nb067_alpha_dummy_225) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_220))
            (Class.cv (nb067_alpha_dummy_221)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_225] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv)
      0

theorem nb067_fresh_415 (f : Var) :
    (nb067_alpha_dummy_226 f) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_226] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f)))).fv)
      0

theorem nb067_fresh_416 :
    (nb067_alpha_dummy_261) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_256))
            (Class.cv (nb067_alpha_dummy_257)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_261] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv)
      0

theorem nb067_fresh_417 (f : Var) :
    (nb067_alpha_dummy_262 f) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_262] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f)))).fv)
      0

theorem nb067_fresh_418 :
    (nb067_alpha_dummy_301) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_296))
            (Class.cv (nb067_alpha_dummy_297)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_301] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv)
      0

theorem nb067_fresh_419 (f : Var) :
    (nb067_alpha_dummy_302 f) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_299 f))
            (Class.cv (nb067_alpha_dummy_300 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_299 f))
            (Class.cv (nb067_alpha_dummy_300 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_302] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_299 f))
            (Class.cv (nb067_alpha_dummy_300 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_299 f))
            (Class.cv (nb067_alpha_dummy_300 f)))).fv)
      0

theorem nb067_fresh_420 :
    (nb067_alpha_dummy_345) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_340))
            (Class.cv (nb067_alpha_dummy_341)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_345] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv)
      0

theorem nb067_fresh_421 (f : Var) :
    (nb067_alpha_dummy_346 f) ∉
      (((syn_cnin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_346] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f)))).fv)
      0

theorem nb067_fresh_422 :
    (nb067_alpha_dummy_079) ∉
      (((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb067_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv) :=
  by
  simpa only [nb067_alpha_dummy_079] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb067_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv)
      0

theorem nb067_fresh_423 (f : Var) :
    (nb067_alpha_dummy_080 f) ∉
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) :=
  by
  simpa only [nb067_alpha_dummy_080] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv)
      0

theorem nb067_fresh_424 :
    (nb067_alpha_dummy_317) ∉
      (((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000)))
            (Class.cv (nb067_alpha_dummy_001)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000)))
            (Class.cv (nb067_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_317] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000)))
            (Class.cv (nb067_alpha_dummy_001)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000)))
            (Class.cv (nb067_alpha_dummy_001)))).fv)
      0

theorem nb067_fresh_425 (x : Var) (f : Var) :
    (nb067_alpha_dummy_318 x f) ∉
      (((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv) :=
  by
  simpa only [nb067_alpha_dummy_318] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv)
      0

theorem nb067_fresh_426 :
    (nb067_alpha_dummy_007) ∉
      (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪
        ((Class.cv (nb067_alpha_dummy_003))).fv) :=
  by
  simpa only [nb067_alpha_dummy_007] using
    freshVar_not_mem
      (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪
        ((Class.cv (nb067_alpha_dummy_003))).fv)
      0

theorem nb067_fresh_427 :
    (nb067_alpha_dummy_008) ∉
      (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪
        ((Class.cv (nb067_alpha_dummy_003))).fv) :=
  by
  simpa only [nb067_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪
        ((Class.cv (nb067_alpha_dummy_003))).fv)
      1

theorem nb067_distinct_428 : (nb067_alpha_dummy_007) ≠ (nb067_alpha_dummy_008) := by
  simpa only [nb067_alpha_dummy_007, nb067_alpha_dummy_008] using
    (freshVar_injective (((syn_cop (Class.cv (nb067_alpha_dummy_001))
            (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_429 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_009 x y f) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv)
      0

theorem nb067_fresh_430 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_010 x y f) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv)
      1

theorem nb067_distinct_431 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_009 x y f) ≠ (nb067_alpha_dummy_010 x y f) := by
  simpa only [nb067_alpha_dummy_009, nb067_alpha_dummy_010] using
    (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_432 :
    (nb067_alpha_dummy_077) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv)
      0

theorem nb067_fresh_433 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_078 x y f) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_078] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv)
      0

theorem nb067_fresh_434 :
    (nb067_alpha_dummy_049) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv)
      0

theorem nb067_fresh_435 (x : Var) (y : Var) :
    (nb067_alpha_dummy_050 x y) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_050] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv)
      0

theorem nb067_fresh_436 :
    (nb067_alpha_dummy_125) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_125] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv)
      0

theorem nb067_fresh_437 (f : Var) :
    (nb067_alpha_dummy_126 f) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_126] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv)
      0

theorem nb067_fresh_438 :
    (nb067_alpha_dummy_161) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_161] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv)
      0

theorem nb067_fresh_439 (f : Var) :
    (nb067_alpha_dummy_162 f) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_162] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv)
      0

theorem nb067_fresh_440 :
    (nb067_alpha_dummy_203) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_203] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv)
      0

theorem nb067_fresh_441 (f : Var) :
    (nb067_alpha_dummy_204 f) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_204] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv)
      0

theorem nb067_fresh_442 :
    (nb067_alpha_dummy_239) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_239] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv)
      0

theorem nb067_fresh_443 (f : Var) :
    (nb067_alpha_dummy_240 f) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_240] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv)
      0

theorem nb067_fresh_444 :
    (nb067_alpha_dummy_275) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_275] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv)
      0

theorem nb067_fresh_445 (f : Var) :
    (nb067_alpha_dummy_276 f) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_276] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv)
      0

theorem nb067_fresh_446 :
    (nb067_alpha_dummy_315) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_315] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv)
      0

theorem nb067_fresh_447 (f : Var) :
    (nb067_alpha_dummy_316 f) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_316] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv)
      0

theorem nb067_fresh_448 :
    (nb067_alpha_dummy_359) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_359] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv)
      0

theorem nb067_fresh_449 (f : Var) :
    (nb067_alpha_dummy_360 f) ∉
      (((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_360] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv)
      0

theorem nb067_fresh_450 :
    (nb067_alpha_dummy_319) ∉
      (((syn_crn (Class.cv (nb067_alpha_dummy_000)))).fv ∪
        ((Class.cv (nb067_alpha_dummy_001))).fv) :=
  by
  simpa only [nb067_alpha_dummy_319] using
    freshVar_not_mem
      (((syn_crn (Class.cv (nb067_alpha_dummy_000)))).fv ∪
        ((Class.cv (nb067_alpha_dummy_001))).fv)
      0

theorem nb067_fresh_451 (x : Var) (f : Var) :
    (nb067_alpha_dummy_320 x f) ∉ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb067_alpha_dummy_320] using
    freshVar_not_mem (((syn_crn (Class.cv f))).fv ∪ ((Class.cv x)).fv) 0

theorem nb067_fresh_452 :
    (nb067_alpha_dummy_003) ∉
      (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((Class.cab (nb067_alpha_dummy_000)
            (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
              (Class.cv (nb067_alpha_dummy_001))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_003] using
    freshVar_not_mem
      (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((Class.cab (nb067_alpha_dummy_000)
            (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
              (Class.cv (nb067_alpha_dummy_001))))).fv)
      0

theorem nb067_fresh_453 :
    (nb067_alpha_dummy_005) ∉
      (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪
          ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv))
              (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000)
                (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
                  (Class.cv (nb067_alpha_dummy_001))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_005] using
    freshVar_not_mem
      (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪
          ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv))
              (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000)
                (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
                  (Class.cv (nb067_alpha_dummy_001))))))).fv)
      0

theorem nb067_fresh_454 :
    (nb067_alpha_dummy_089) ∉
      (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪
        ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083))
                (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))
                (Class.cv (nb067_alpha_dummy_085))) (syn_wbr (Class.cv (nb067_alpha_dummy_085))
                (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_084)))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_089] using
    freshVar_not_mem
      (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪
        ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083))
                (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))
                (Class.cv (nb067_alpha_dummy_085))) (syn_wbr (Class.cv (nb067_alpha_dummy_085))
                (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_084)))))).fv)
      0

theorem nb067_fresh_455 (f : Var) :
    (nb067_alpha_dummy_090 f) ∉
      (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪
        ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa
              (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb067_alpha_dummy_088 f)))
              (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f)
                (Class.cv (nb067_alpha_dummy_087 f)))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_090] using
    freshVar_not_mem
      (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪
        ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa
              (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb067_alpha_dummy_088 f)))
              (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f)
                (Class.cv (nb067_alpha_dummy_087 f)))))).fv)
      0

theorem nb067_fresh_456 :
    (nb067_alpha_dummy_167) ∉
      (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000))
            (Class.cv (nb067_alpha_dummy_163)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_167] using
    freshVar_not_mem
      (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000))
            (Class.cv (nb067_alpha_dummy_163)))).fv)
      0

theorem nb067_fresh_457 (f : Var) :
    (nb067_alpha_dummy_168 f) ∉
      (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f)
            (Class.cv (nb067_alpha_dummy_165 f)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_168] using
    freshVar_not_mem
      (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f)
            (Class.cv (nb067_alpha_dummy_165 f)))).fv)
      0

theorem nb067_fresh_458 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_004 x y f) ∉
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))).fv)
      0

theorem nb067_fresh_459 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_006 x y f) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f))
              (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_006] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f))
              (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv)
      0

theorem nb067_fresh_460 : (nb067_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb067_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb067_fresh_461 : (nb067_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb067_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb067_fresh_462 : (nb067_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb067_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb067_distinct_463 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_001) := by
  simpa only [nb067_alpha_dummy_000, nb067_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_464 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_002) := by
  simpa only [nb067_alpha_dummy_000, nb067_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_465 : (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_002) := by
  simpa only [nb067_alpha_dummy_001, nb067_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb067_support_mem_0000 :
    (nb067_alpha_dummy_001) ∈
      (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪
          ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv))
              (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000)
                (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
                  (Class.cv (nb067_alpha_dummy_001))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0001 (x : Var) (y : Var) (f : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f))
              (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0002 :
    (nb067_alpha_dummy_002) ∈
      (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪
          ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv))
              (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000)
                (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
                  (Class.cv (nb067_alpha_dummy_001))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0003 (x : Var) (y : Var) (f : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f))
              (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0004 :
    (nb067_alpha_dummy_003) ∈
      (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪
          ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv))
              (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000)
                (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
                  (Class.cv (nb067_alpha_dummy_001))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0005 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_004 x y f) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f))
              (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0006 :
    (nb067_alpha_dummy_001) ∈
      (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((Class.cab (nb067_alpha_dummy_000)
            (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
              (Class.cv (nb067_alpha_dummy_001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0007 (x : Var) (y : Var) (f : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0008 :
    (nb067_alpha_dummy_001) ∈
      (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪
        ((Class.cv (nb067_alpha_dummy_003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0009 :
    (nb067_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
                (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_007)
              (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0010 (x : Var) (y : Var) (f : Var) :
    x ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0011 (x : Var) (y : Var) (f : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f)
              (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f)
                (Class.cv (nb067_alpha_dummy_004 x y f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0012 :
    (nb067_alpha_dummy_001) ∈
      (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
              (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
              (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0013 (x : Var) (y : Var) (f : Var) :
    x ∈
      (((Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0014 :
    (nb067_alpha_dummy_001) ∈
      (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0015 :
    (nb067_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_015)
              (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_016)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_015)
              (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0016 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0017 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y)
              (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_017 x y)
              (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0018 :
    (nb067_alpha_dummy_001) ∈
      (((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0019 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0020 :
    (nb067_alpha_dummy_016) ∈ (((Class.cv (nb067_alpha_dummy_016))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0021 (x : Var) (y : Var) :
    (nb067_alpha_dummy_018 x y) ∈ (((Class.cv (nb067_alpha_dummy_018 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0022 :
    (nb067_alpha_dummy_023) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_023)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_023)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_023))).fv) :=
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

theorem nb067_support_mem_0023 (x : Var) (y : Var) :
    (nb067_alpha_dummy_025 x y) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_025 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_025 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_025 x y))).fv) :=
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

theorem nb067_support_mem_0024 :
    (nb067_alpha_dummy_023) ∈
      (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0025 (x : Var) (y : Var) :
    (nb067_alpha_dummy_025 x y) ∈
      (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0026 :
    (nb067_alpha_dummy_030) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_030))
            (Class.cv (nb067_alpha_dummy_031)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0027 (x : Var) (y : Var) :
    (nb067_alpha_dummy_033 x y) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y))
            (Class.cv (nb067_alpha_dummy_034 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y))
            (Class.cv (nb067_alpha_dummy_034 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0028 :
    (nb067_alpha_dummy_030) ∈
      (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0029 (x : Var) (y : Var) :
    (nb067_alpha_dummy_033 x y) ∈
      (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_034 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0030 :
    (nb067_alpha_dummy_031) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_030))
            (Class.cv (nb067_alpha_dummy_031)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0031 (x : Var) (y : Var) :
    (nb067_alpha_dummy_034 x y) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y))
            (Class.cv (nb067_alpha_dummy_034 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y))
            (Class.cv (nb067_alpha_dummy_034 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0032 :
    (nb067_alpha_dummy_031) ∈
      (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0033 (x : Var) (y : Var) :
    (nb067_alpha_dummy_034 x y) ∈
      (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_034 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0034 :
    (nb067_alpha_dummy_030) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_030)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_031)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0035 (x : Var) (y : Var) :
    (nb067_alpha_dummy_033 x y) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_033 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_034 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0036 :
    (nb067_alpha_dummy_030) ∈
      (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0037 (x : Var) (y : Var) :
    (nb067_alpha_dummy_033 x y) ∈
      (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0038 :
    (nb067_alpha_dummy_031) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_030)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_031)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0039 (x : Var) (y : Var) :
    (nb067_alpha_dummy_034 x y) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_033 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_034 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0040 :
    (nb067_alpha_dummy_031) ∈
      (((Class.cv (nb067_alpha_dummy_031))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0041 (x : Var) (y : Var) :
    (nb067_alpha_dummy_034 x y) ∈
      (((Class.cv (nb067_alpha_dummy_034 x y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_034 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0042 :
    (nb067_alpha_dummy_002) ∈
      (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((Class.cab (nb067_alpha_dummy_000)
            (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
              (Class.cv (nb067_alpha_dummy_001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0043 (x : Var) (y : Var) (f : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0044 :
    (nb067_alpha_dummy_002) ∈
      (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪
        ((Class.cv (nb067_alpha_dummy_003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part007`. -/


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

theorem nb067_support_mem_0045 :
    (nb067_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
                (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_007)
              (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0046 (x : Var) (y : Var) (f : Var) :
    y ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0047 (x : Var) (y : Var) (f : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f)
              (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f)
                (Class.cv (nb067_alpha_dummy_004 x y f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0048 :
    (nb067_alpha_dummy_002) ∈
      (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
              (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
              (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0049 (x : Var) (y : Var) (f : Var) :
    y ∈
      (((Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0050 :
    (nb067_alpha_dummy_002) ∈
      (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0051 :
    (nb067_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_015)
              (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_016)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_015)
              (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0052 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0053 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y)
              (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_017 x y)
              (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0054 :
    (nb067_alpha_dummy_002) ∈
      (((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0055 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0056 :
    (nb067_alpha_dummy_016) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_016))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0057 (x : Var) (y : Var) :
    (nb067_alpha_dummy_018 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0058 :
    (nb067_alpha_dummy_016) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0059 (x : Var) (y : Var) :
    (nb067_alpha_dummy_018 x y) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0060 :
    (nb067_alpha_dummy_008) ∈ (((Class.cv (nb067_alpha_dummy_008))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0061 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_010 x y f) ∈ (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0062 :
    (nb067_alpha_dummy_051) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_051)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_051)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_051))).fv) :=
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

theorem nb067_support_mem_0063 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_053 x y f) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_053 x y f))).fv) :=
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

theorem nb067_support_mem_0064 :
    (nb067_alpha_dummy_051) ∈
      (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0065 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_053 x y f) ∈
      (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0066 :
    (nb067_alpha_dummy_058) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_058))
            (Class.cv (nb067_alpha_dummy_059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0067 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_061 x y f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f))
            (Class.cv (nb067_alpha_dummy_062 x y f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f))
            (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0068 :
    (nb067_alpha_dummy_058) ∈
      (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0069 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_061 x y f) ∈
      (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0070 :
    (nb067_alpha_dummy_059) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_058))
            (Class.cv (nb067_alpha_dummy_059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0071 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_062 x y f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f))
            (Class.cv (nb067_alpha_dummy_062 x y f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f))
            (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0072 :
    (nb067_alpha_dummy_059) ∈
      (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0073 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_062 x y f) ∈
      (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0074 :
    (nb067_alpha_dummy_058) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_058)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0075 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_061 x y f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_061 x y f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0076 :
    (nb067_alpha_dummy_058) ∈
      (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0077 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_061 x y f) ∈
      (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_061 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0078 :
    (nb067_alpha_dummy_059) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_058)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0079 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_062 x y f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_061 x y f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0080 :
    (nb067_alpha_dummy_059) ∈
      (((Class.cv (nb067_alpha_dummy_059))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0081 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_062 x y f) ∈
      (((Class.cv (nb067_alpha_dummy_062 x y f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0082 :
    (nb067_alpha_dummy_003) ∈
      (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪
        ((Class.cv (nb067_alpha_dummy_003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0083 :
    (nb067_alpha_dummy_003) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
                (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_007)
              (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0084 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_004 x y f) ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0085 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_004 x y f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f)
              (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f)
                (Class.cv (nb067_alpha_dummy_004 x y f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0086 :
    (nb067_alpha_dummy_003) ∈
      (((Class.cab (nb067_alpha_dummy_007)
            (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007)
            (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0087 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_004 x y f) ∈
      (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f)
              (Class.cv (nb067_alpha_dummy_004 x y f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0088 :
    (nb067_alpha_dummy_008) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_008))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0089 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_010 x y f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0090 :
    (nb067_alpha_dummy_008) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0091 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_010 x y f) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0092 :
    (nb067_alpha_dummy_083) ∈
      (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪
        ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083))
                (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))
                (Class.cv (nb067_alpha_dummy_085))) (syn_wbr (Class.cv (nb067_alpha_dummy_085))
                (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_084)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0093 (f : Var) :
    (nb067_alpha_dummy_086 f) ∈
      (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪
        ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa
              (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb067_alpha_dummy_088 f)))
              (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f)
                (Class.cv (nb067_alpha_dummy_087 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0094 :
    (nb067_alpha_dummy_084) ∈
      (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪
        ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083))
                (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))
                (Class.cv (nb067_alpha_dummy_085))) (syn_wbr (Class.cv (nb067_alpha_dummy_085))
                (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_084)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0095 (f : Var) :
    (nb067_alpha_dummy_087 f) ∈
      (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪
        ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa
              (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb067_alpha_dummy_088 f)))
              (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f)
                (Class.cv (nb067_alpha_dummy_087 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0096 :
    (nb067_alpha_dummy_083) ∈
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0097 :
    (nb067_alpha_dummy_083) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_091)
              (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_091)
              (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0098 (f : Var) :
    (nb067_alpha_dummy_086 f) ∈
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0099 (f : Var) :
    (nb067_alpha_dummy_086 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f)
              (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_093 f)
              (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0100 :
    (nb067_alpha_dummy_083) ∈
      (((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0101 (f : Var) :
    (nb067_alpha_dummy_086 f) ∈
      (((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0102 :
    (nb067_alpha_dummy_092) ∈ (((Class.cv (nb067_alpha_dummy_092))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0103 (f : Var) :
    (nb067_alpha_dummy_094 f) ∈ (((Class.cv (nb067_alpha_dummy_094 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0104 :
    (nb067_alpha_dummy_099) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_099))).fv) :=
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

theorem nb067_support_mem_0105 (f : Var) :
    (nb067_alpha_dummy_101 f) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_101 f))).fv) :=
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

theorem nb067_support_mem_0106 :
    (nb067_alpha_dummy_099) ∈
      (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0107 (f : Var) :
    (nb067_alpha_dummy_101 f) ∈
      (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0108 :
    (nb067_alpha_dummy_106) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_106))
            (Class.cv (nb067_alpha_dummy_107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0109 (f : Var) :
    (nb067_alpha_dummy_109 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0110 :
    (nb067_alpha_dummy_106) ∈
      (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0111 (f : Var) :
    (nb067_alpha_dummy_109 f) ∈
      (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0112 :
    (nb067_alpha_dummy_107) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_106))
            (Class.cv (nb067_alpha_dummy_107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0113 (f : Var) :
    (nb067_alpha_dummy_110 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0114 :
    (nb067_alpha_dummy_107) ∈
      (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0115 (f : Var) :
    (nb067_alpha_dummy_110 f) ∈
      (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0116 :
    (nb067_alpha_dummy_106) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_106)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0117 (f : Var) :
    (nb067_alpha_dummy_109 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_109 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0118 :
    (nb067_alpha_dummy_106) ∈
      (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_106))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0119 (f : Var) :
    (nb067_alpha_dummy_109 f) ∈
      (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_109 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0120 :
    (nb067_alpha_dummy_107) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_106)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0121 (f : Var) :
    (nb067_alpha_dummy_110 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_109 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0122 :
    (nb067_alpha_dummy_107) ∈
      (((Class.cv (nb067_alpha_dummy_107))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0123 (f : Var) :
    (nb067_alpha_dummy_110 f) ∈
      (((Class.cv (nb067_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0124 :
    (nb067_alpha_dummy_084) ∈
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0125 :
    (nb067_alpha_dummy_084) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_091)
              (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_091)
              (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0126 (f : Var) :
    (nb067_alpha_dummy_087 f) ∈
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0127 (f : Var) :
    (nb067_alpha_dummy_087 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f)
              (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_093 f)
              (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0128 :
    (nb067_alpha_dummy_084) ∈
      (((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0129 (f : Var) :
    (nb067_alpha_dummy_087 f) ∈
      (((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0130 :
    (nb067_alpha_dummy_092) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_092))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0131 (f : Var) :
    (nb067_alpha_dummy_094 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0132 :
    (nb067_alpha_dummy_092) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0133 (f : Var) :
    (nb067_alpha_dummy_094 f) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0134 :
    (nb067_alpha_dummy_083) ∈
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0135 :
    (nb067_alpha_dummy_083) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_127)
              (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_127)
              (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0136 (f : Var) :
    (nb067_alpha_dummy_086 f) ∈
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0137 (f : Var) :
    (nb067_alpha_dummy_086 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f)
              (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_129 f)
              (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0138 :
    (nb067_alpha_dummy_083) ∈
      (((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0139 (f : Var) :
    (nb067_alpha_dummy_086 f) ∈
      (((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0140 :
    (nb067_alpha_dummy_128) ∈ (((Class.cv (nb067_alpha_dummy_128))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0141 (f : Var) :
    (nb067_alpha_dummy_130 f) ∈ (((Class.cv (nb067_alpha_dummy_130 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0142 :
    (nb067_alpha_dummy_135) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_135))).fv) :=
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

theorem nb067_support_mem_0143 (f : Var) :
    (nb067_alpha_dummy_137 f) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_137 f))).fv) :=
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

theorem nb067_support_mem_0144 :
    (nb067_alpha_dummy_135) ∈
      (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0145 (f : Var) :
    (nb067_alpha_dummy_137 f) ∈
      (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0146 :
    (nb067_alpha_dummy_142) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_142))
            (Class.cv (nb067_alpha_dummy_143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0147 (f : Var) :
    (nb067_alpha_dummy_145 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0148 :
    (nb067_alpha_dummy_142) ∈
      (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0149 (f : Var) :
    (nb067_alpha_dummy_145 f) ∈
      (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0150 :
    (nb067_alpha_dummy_143) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_142))
            (Class.cv (nb067_alpha_dummy_143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0151 (f : Var) :
    (nb067_alpha_dummy_146 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0152 :
    (nb067_alpha_dummy_143) ∈
      (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0153 (f : Var) :
    (nb067_alpha_dummy_146 f) ∈
      (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0154 :
    (nb067_alpha_dummy_142) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_142)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0155 (f : Var) :
    (nb067_alpha_dummy_145 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_145 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0156 :
    (nb067_alpha_dummy_142) ∈
      (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_142))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0157 (f : Var) :
    (nb067_alpha_dummy_145 f) ∈
      (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_145 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0158 :
    (nb067_alpha_dummy_143) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_142)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0159 (f : Var) :
    (nb067_alpha_dummy_146 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_145 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0160 :
    (nb067_alpha_dummy_143) ∈
      (((Class.cv (nb067_alpha_dummy_143))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0161 (f : Var) :
    (nb067_alpha_dummy_146 f) ∈
      (((Class.cv (nb067_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0162 :
    (nb067_alpha_dummy_085) ∈
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0163 :
    (nb067_alpha_dummy_085) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_127)
              (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_127)
              (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0164 (f : Var) :
    (nb067_alpha_dummy_088 f) ∈
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0165 (f : Var) :
    (nb067_alpha_dummy_088 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f)
              (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_129 f)
              (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0166 :
    (nb067_alpha_dummy_085) ∈
      (((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0167 (f : Var) :
    (nb067_alpha_dummy_088 f) ∈
      (((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0168 :
    (nb067_alpha_dummy_128) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_128))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0169 (f : Var) :
    (nb067_alpha_dummy_130 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0170 :
    (nb067_alpha_dummy_128) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0171 (f : Var) :
    (nb067_alpha_dummy_130 f) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0172 :
    (nb067_alpha_dummy_163) ∈
      (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000))
            (Class.cv (nb067_alpha_dummy_163)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0173 (f : Var) :
    (nb067_alpha_dummy_165 f) ∈
      (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f)
            (Class.cv (nb067_alpha_dummy_165 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0174 :
    (nb067_alpha_dummy_164) ∈
      (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000))
            (Class.cv (nb067_alpha_dummy_163)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0175 (f : Var) :
    (nb067_alpha_dummy_166 f) ∈
      (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f)
            (Class.cv (nb067_alpha_dummy_165 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0176 :
    (nb067_alpha_dummy_163) ∈
      (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0177 :
    (nb067_alpha_dummy_163) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_169)
              (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_170)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_169)
              (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part008`. -/


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

theorem nb067_support_mem_0178 (f : Var) :
    (nb067_alpha_dummy_165 f) ∈
      (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0179 (f : Var) :
    (nb067_alpha_dummy_165 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f)
              (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_171 f)
              (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0180 :
    (nb067_alpha_dummy_163) ∈
      (((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0181 (f : Var) :
    (nb067_alpha_dummy_165 f) ∈
      (((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0182 :
    (nb067_alpha_dummy_170) ∈ (((Class.cv (nb067_alpha_dummy_170))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0183 (f : Var) :
    (nb067_alpha_dummy_172 f) ∈ (((Class.cv (nb067_alpha_dummy_172 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0184 :
    (nb067_alpha_dummy_177) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_177))).fv) :=
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

theorem nb067_support_mem_0185 (f : Var) :
    (nb067_alpha_dummy_179 f) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_179 f))).fv) :=
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

theorem nb067_support_mem_0186 :
    (nb067_alpha_dummy_177) ∈
      (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0187 (f : Var) :
    (nb067_alpha_dummy_179 f) ∈
      (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0188 :
    (nb067_alpha_dummy_184) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_184))
            (Class.cv (nb067_alpha_dummy_185)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0189 (f : Var) :
    (nb067_alpha_dummy_187 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0190 :
    (nb067_alpha_dummy_184) ∈
      (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0191 (f : Var) :
    (nb067_alpha_dummy_187 f) ∈
      (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0192 :
    (nb067_alpha_dummy_185) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_184))
            (Class.cv (nb067_alpha_dummy_185)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0193 (f : Var) :
    (nb067_alpha_dummy_188 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0194 :
    (nb067_alpha_dummy_185) ∈
      (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0195 (f : Var) :
    (nb067_alpha_dummy_188 f) ∈
      (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0196 :
    (nb067_alpha_dummy_184) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_184)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_185)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0197 (f : Var) :
    (nb067_alpha_dummy_187 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_187 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0198 :
    (nb067_alpha_dummy_184) ∈
      (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_184))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0199 (f : Var) :
    (nb067_alpha_dummy_187 f) ∈
      (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_187 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0200 :
    (nb067_alpha_dummy_185) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_184)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_185)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0201 (f : Var) :
    (nb067_alpha_dummy_188 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_187 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0202 :
    (nb067_alpha_dummy_185) ∈
      (((Class.cv (nb067_alpha_dummy_185))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0203 (f : Var) :
    (nb067_alpha_dummy_188 f) ∈
      (((Class.cv (nb067_alpha_dummy_188 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0204 :
    (nb067_alpha_dummy_164) ∈
      (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0205 :
    (nb067_alpha_dummy_164) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_169)
              (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_170)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_169)
              (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0206 (f : Var) :
    (nb067_alpha_dummy_166 f) ∈
      (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0207 (f : Var) :
    (nb067_alpha_dummy_166 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f)
              (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_171 f)
              (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0208 :
    (nb067_alpha_dummy_164) ∈
      (((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0209 (f : Var) :
    (nb067_alpha_dummy_166 f) ∈
      (((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0210 :
    (nb067_alpha_dummy_170) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_170))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0211 (f : Var) :
    (nb067_alpha_dummy_172 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0212 :
    (nb067_alpha_dummy_170) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0213 (f : Var) :
    (nb067_alpha_dummy_172 f) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0214 :
    (nb067_alpha_dummy_164) ∈
      (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0215 :
    (nb067_alpha_dummy_164) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_205)
              (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_206)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_205)
              (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0216 (f : Var) :
    (nb067_alpha_dummy_166 f) ∈
      (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0217 (f : Var) :
    (nb067_alpha_dummy_166 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f)
              (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_207 f)
              (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0218 :
    (nb067_alpha_dummy_164) ∈
      (((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0219 (f : Var) :
    (nb067_alpha_dummy_166 f) ∈
      (((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0220 :
    (nb067_alpha_dummy_206) ∈ (((Class.cv (nb067_alpha_dummy_206))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0221 (f : Var) :
    (nb067_alpha_dummy_208 f) ∈ (((Class.cv (nb067_alpha_dummy_208 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0222 :
    (nb067_alpha_dummy_213) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_213))).fv) :=
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

theorem nb067_support_mem_0223 (f : Var) :
    (nb067_alpha_dummy_215 f) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_215 f))).fv) :=
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

theorem nb067_support_mem_0224 :
    (nb067_alpha_dummy_213) ∈
      (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0225 (f : Var) :
    (nb067_alpha_dummy_215 f) ∈
      (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0226 :
    (nb067_alpha_dummy_220) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_220))
            (Class.cv (nb067_alpha_dummy_221)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0227 (f : Var) :
    (nb067_alpha_dummy_223 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0228 :
    (nb067_alpha_dummy_220) ∈
      (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0229 (f : Var) :
    (nb067_alpha_dummy_223 f) ∈
      (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0230 :
    (nb067_alpha_dummy_221) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_220))
            (Class.cv (nb067_alpha_dummy_221)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0231 (f : Var) :
    (nb067_alpha_dummy_224 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0232 :
    (nb067_alpha_dummy_221) ∈
      (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0233 (f : Var) :
    (nb067_alpha_dummy_224 f) ∈
      (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0234 :
    (nb067_alpha_dummy_220) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_220)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_221)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0235 (f : Var) :
    (nb067_alpha_dummy_223 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_223 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_224 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0236 :
    (nb067_alpha_dummy_220) ∈
      (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_220))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0237 (f : Var) :
    (nb067_alpha_dummy_223 f) ∈
      (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_223 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0238 :
    (nb067_alpha_dummy_221) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_220)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_221)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0239 (f : Var) :
    (nb067_alpha_dummy_224 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_223 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_224 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0240 :
    (nb067_alpha_dummy_221) ∈
      (((Class.cv (nb067_alpha_dummy_221))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0241 (f : Var) :
    (nb067_alpha_dummy_224 f) ∈
      (((Class.cv (nb067_alpha_dummy_224 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0242 :
    (nb067_alpha_dummy_163) ∈
      (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0243 :
    (nb067_alpha_dummy_163) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_205)
              (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_206)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_205)
              (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0244 (f : Var) :
    (nb067_alpha_dummy_165 f) ∈
      (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0245 (f : Var) :
    (nb067_alpha_dummy_165 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f)
              (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_207 f)
              (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0246 :
    (nb067_alpha_dummy_163) ∈
      (((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0247 (f : Var) :
    (nb067_alpha_dummy_165 f) ∈
      (((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0248 :
    (nb067_alpha_dummy_206) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_206))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0249 (f : Var) :
    (nb067_alpha_dummy_208 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0250 :
    (nb067_alpha_dummy_206) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0251 (f : Var) :
    (nb067_alpha_dummy_208 f) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0252 :
    (nb067_alpha_dummy_000) ∈
      (((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb067_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0253 (f : Var) :
    f ∈
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0254 :
    (nb067_alpha_dummy_000) ∈
      (((syn_ccom (Class.cv (nb067_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb067_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0255 (f : Var) :
    f ∈ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0256 :
    (nb067_alpha_dummy_000) ∈
      (((Class.cv (nb067_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0257 :
    (nb067_alpha_dummy_000) ∈
      (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪
        ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083))
                (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))
                (Class.cv (nb067_alpha_dummy_085))) (syn_wbr (Class.cv (nb067_alpha_dummy_085))
                (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_084)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 2))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb067_support_mem_0258 (f : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0259 (f : Var) :
    f ∈
      (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪
        ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa
              (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb067_alpha_dummy_088 f)))
              (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f)
                (Class.cv (nb067_alpha_dummy_087 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · unfold nb067_alpha_dummy_088
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 2))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb067_support_mem_0260 :
    (nb067_alpha_dummy_000) ∈
      (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000))
            (Class.cv (nb067_alpha_dummy_163)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0261 (f : Var) :
    f ∈
      (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f)
            (Class.cv (nb067_alpha_dummy_165 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0262 :
    (nb067_alpha_dummy_000) ∈ (((Class.cv (nb067_alpha_dummy_000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0263 (f : Var) : f ∈ (((Class.cv f)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0264 :
    (nb067_alpha_dummy_085) ∈
      (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0265 :
    (nb067_alpha_dummy_085) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_241)
              (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_242)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_241)
              (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0266 (f : Var) :
    (nb067_alpha_dummy_088 f) ∈
      (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0267 (f : Var) :
    (nb067_alpha_dummy_088 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f)
              (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_243 f)
              (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0268 :
    (nb067_alpha_dummy_085) ∈
      (((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0269 (f : Var) :
    (nb067_alpha_dummy_088 f) ∈
      (((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0270 :
    (nb067_alpha_dummy_242) ∈ (((Class.cv (nb067_alpha_dummy_242))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0271 (f : Var) :
    (nb067_alpha_dummy_244 f) ∈ (((Class.cv (nb067_alpha_dummy_244 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0272 :
    (nb067_alpha_dummy_249) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_249))).fv) :=
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

theorem nb067_support_mem_0273 (f : Var) :
    (nb067_alpha_dummy_251 f) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_251 f))).fv) :=
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

theorem nb067_support_mem_0274 :
    (nb067_alpha_dummy_249) ∈
      (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0275 (f : Var) :
    (nb067_alpha_dummy_251 f) ∈
      (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0276 :
    (nb067_alpha_dummy_256) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_256))
            (Class.cv (nb067_alpha_dummy_257)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0277 (f : Var) :
    (nb067_alpha_dummy_259 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0278 :
    (nb067_alpha_dummy_256) ∈
      (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0279 (f : Var) :
    (nb067_alpha_dummy_259 f) ∈
      (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0280 :
    (nb067_alpha_dummy_257) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_256))
            (Class.cv (nb067_alpha_dummy_257)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0281 (f : Var) :
    (nb067_alpha_dummy_260 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0282 :
    (nb067_alpha_dummy_257) ∈
      (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0283 (f : Var) :
    (nb067_alpha_dummy_260 f) ∈
      (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0284 :
    (nb067_alpha_dummy_256) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_256)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_257)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0285 (f : Var) :
    (nb067_alpha_dummy_259 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_259 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_260 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0286 :
    (nb067_alpha_dummy_256) ∈
      (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_256))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0287 (f : Var) :
    (nb067_alpha_dummy_259 f) ∈
      (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_259 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0288 :
    (nb067_alpha_dummy_257) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_256)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_257)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0289 (f : Var) :
    (nb067_alpha_dummy_260 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_259 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_260 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0290 :
    (nb067_alpha_dummy_257) ∈
      (((Class.cv (nb067_alpha_dummy_257))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0291 (f : Var) :
    (nb067_alpha_dummy_260 f) ∈
      (((Class.cv (nb067_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0292 :
    (nb067_alpha_dummy_084) ∈
      (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0293 :
    (nb067_alpha_dummy_084) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_241)
              (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_242)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_241)
              (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0294 (f : Var) :
    (nb067_alpha_dummy_087 f) ∈
      (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0295 (f : Var) :
    (nb067_alpha_dummy_087 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f)
              (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_243 f)
              (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0296 :
    (nb067_alpha_dummy_084) ∈
      (((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0297 (f : Var) :
    (nb067_alpha_dummy_087 f) ∈
      (((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0298 :
    (nb067_alpha_dummy_242) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_242))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0299 (f : Var) :
    (nb067_alpha_dummy_244 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0300 :
    (nb067_alpha_dummy_242) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0301 (f : Var) :
    (nb067_alpha_dummy_244 f) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0302 :
    (nb067_alpha_dummy_278) ∈
      (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0303 :
    (nb067_alpha_dummy_278) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_281)
              (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_282)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_281)
              (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0304 (f : Var) :
    (nb067_alpha_dummy_280 f) ∈
      (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0305 (f : Var) :
    (nb067_alpha_dummy_280 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f)
              (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_283 f)
              (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0306 :
    (nb067_alpha_dummy_278) ∈
      (((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0307 (f : Var) :
    (nb067_alpha_dummy_280 f) ∈
      (((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0308 :
    (nb067_alpha_dummy_282) ∈ (((Class.cv (nb067_alpha_dummy_282))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0309 (f : Var) :
    (nb067_alpha_dummy_284 f) ∈ (((Class.cv (nb067_alpha_dummy_284 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0310 :
    (nb067_alpha_dummy_289) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_289)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_289)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_289))).fv) :=
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

theorem nb067_support_mem_0311 (f : Var) :
    (nb067_alpha_dummy_291 f) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_291 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_291 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_291 f))).fv) :=
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

theorem nb067_support_mem_0312 :
    (nb067_alpha_dummy_289) ∈
      (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0313 (f : Var) :
    (nb067_alpha_dummy_291 f) ∈
      (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0314 :
    (nb067_alpha_dummy_296) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_296))
            (Class.cv (nb067_alpha_dummy_297)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0315 (f : Var) :
    (nb067_alpha_dummy_299 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_299 f))
            (Class.cv (nb067_alpha_dummy_300 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_299 f))
            (Class.cv (nb067_alpha_dummy_300 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0316 :
    (nb067_alpha_dummy_296) ∈
      (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0317 (f : Var) :
    (nb067_alpha_dummy_299 f) ∈
      (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0318 :
    (nb067_alpha_dummy_297) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_296))
            (Class.cv (nb067_alpha_dummy_297)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0319 (f : Var) :
    (nb067_alpha_dummy_300 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_299 f))
            (Class.cv (nb067_alpha_dummy_300 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_299 f))
            (Class.cv (nb067_alpha_dummy_300 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
