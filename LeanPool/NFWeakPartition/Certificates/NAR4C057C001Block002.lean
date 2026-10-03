/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C057C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C057C001Part005`. -/


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

theorem nb057_fresh_322 :
    (nb057_alpha_dummy_072) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_067))
            (Class.cv (nb057_alpha_dummy_068)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_072] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv)
      0

theorem nb057_fresh_323 (f : Var) :
    (nb057_alpha_dummy_073 f) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_070 f))
            (Class.cv (nb057_alpha_dummy_071 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_070 f))
            (Class.cv (nb057_alpha_dummy_071 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_073] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_070 f))
            (Class.cv (nb057_alpha_dummy_071 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_070 f))
            (Class.cv (nb057_alpha_dummy_071 f)))).fv)
      0

theorem nb057_fresh_324 :
    (nb057_alpha_dummy_108) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_103))
            (Class.cv (nb057_alpha_dummy_104)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_108] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv)
      0

theorem nb057_fresh_325 (f : Var) :
    (nb057_alpha_dummy_109 f) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_106 f))
            (Class.cv (nb057_alpha_dummy_107 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_106 f))
            (Class.cv (nb057_alpha_dummy_107 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_109] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_106 f))
            (Class.cv (nb057_alpha_dummy_107 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_106 f))
            (Class.cv (nb057_alpha_dummy_107 f)))).fv)
      0

theorem nb057_fresh_326 :
    (nb057_alpha_dummy_150) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_145))
            (Class.cv (nb057_alpha_dummy_146)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_150] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv)
      0

theorem nb057_fresh_327 (f : Var) :
    (nb057_alpha_dummy_151 f) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_151] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f)))).fv)
      0

theorem nb057_fresh_328 :
    (nb057_alpha_dummy_186) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_181))
            (Class.cv (nb057_alpha_dummy_182)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_186] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv)
      0

theorem nb057_fresh_329 (f : Var) :
    (nb057_alpha_dummy_187 f) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_187] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f)))).fv)
      0

theorem nb057_fresh_330 :
    (nb057_alpha_dummy_222) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_217))
            (Class.cv (nb057_alpha_dummy_218)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_222] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv)
      0

theorem nb057_fresh_331 (f : Var) :
    (nb057_alpha_dummy_223 f) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_220 f))
            (Class.cv (nb057_alpha_dummy_221 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_220 f))
            (Class.cv (nb057_alpha_dummy_221 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_223] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_220 f))
            (Class.cv (nb057_alpha_dummy_221 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_220 f))
            (Class.cv (nb057_alpha_dummy_221 f)))).fv)
      0

theorem nb057_fresh_332 :
    (nb057_alpha_dummy_262) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_257))
            (Class.cv (nb057_alpha_dummy_258)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_262] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv)
      0

theorem nb057_fresh_333 (f : Var) :
    (nb057_alpha_dummy_263 f) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_260 f))
            (Class.cv (nb057_alpha_dummy_261 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_260 f))
            (Class.cv (nb057_alpha_dummy_261 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_263] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_260 f))
            (Class.cv (nb057_alpha_dummy_261 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_260 f))
            (Class.cv (nb057_alpha_dummy_261 f)))).fv)
      0

theorem nb057_fresh_334 :
    (nb057_alpha_dummy_040) ∉
      (((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb057_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv) :=
  by
  simpa only [nb057_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb057_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv)
      0

theorem nb057_fresh_335 (f : Var) :
    (nb057_alpha_dummy_041 f) ∉
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) :=
  by
  simpa only [nb057_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv)
      0

theorem nb057_fresh_336 :
    (nb057_alpha_dummy_038) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv)
      0

theorem nb057_fresh_337 (f : Var) (a : Var) :
    (nb057_alpha_dummy_039 f a) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv)
      0

theorem nb057_fresh_338 :
    (nb057_alpha_dummy_086) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_086] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv)
      0

theorem nb057_fresh_339 (f : Var) :
    (nb057_alpha_dummy_087 f) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_087] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv)
      0

theorem nb057_fresh_340 :
    (nb057_alpha_dummy_122) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_122] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv)
      0

theorem nb057_fresh_341 (f : Var) :
    (nb057_alpha_dummy_123 f) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_123] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv)
      0

theorem nb057_fresh_342 :
    (nb057_alpha_dummy_164) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_164] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv)
      0

theorem nb057_fresh_343 (f : Var) :
    (nb057_alpha_dummy_165 f) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_165] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv)
      0

theorem nb057_fresh_344 :
    (nb057_alpha_dummy_200) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_200] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv)
      0

theorem nb057_fresh_345 (f : Var) :
    (nb057_alpha_dummy_201 f) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_201] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv)
      0

theorem nb057_fresh_346 :
    (nb057_alpha_dummy_236) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_236] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv)
      0

theorem nb057_fresh_347 (f : Var) :
    (nb057_alpha_dummy_237 f) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_237] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv)
      0

theorem nb057_fresh_348 :
    (nb057_alpha_dummy_276) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_276] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv)
      0

theorem nb057_fresh_349 (f : Var) :
    (nb057_alpha_dummy_277 f) ∉
      (((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_277] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv)
      0

theorem nb057_fresh_350 :
    (nb057_alpha_dummy_002) ∉
      (({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_002] using
    freshVar_not_mem
      (({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv)
      0

theorem nb057_fresh_351 :
    (nb057_alpha_dummy_050) ∉
      (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪
        ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044))
                (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))
                (Class.cv (nb057_alpha_dummy_046))) (syn_wbr (Class.cv (nb057_alpha_dummy_046))
                (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045)))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_050] using
    freshVar_not_mem
      (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪
        ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044))
                (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))
                (Class.cv (nb057_alpha_dummy_046))) (syn_wbr (Class.cv (nb057_alpha_dummy_046))
                (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045)))))).fv)
      0

theorem nb057_fresh_352 (f : Var) :
    (nb057_alpha_dummy_051 f) ∉
      (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪
        ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa
              (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb057_alpha_dummy_049 f)))
              (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f)
                (Class.cv (nb057_alpha_dummy_048 f)))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_051] using
    freshVar_not_mem
      (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪
        ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa
              (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb057_alpha_dummy_049 f)))
              (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f)
                (Class.cv (nb057_alpha_dummy_048 f)))))).fv)
      0

theorem nb057_fresh_353 :
    (nb057_alpha_dummy_128) ∉
      (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001))
            (Class.cv (nb057_alpha_dummy_124)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_128] using
    freshVar_not_mem
      (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001))
            (Class.cv (nb057_alpha_dummy_124)))).fv)
      0

theorem nb057_fresh_354 (f : Var) :
    (nb057_alpha_dummy_129 f) ∉
      (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f)
            (Class.cv (nb057_alpha_dummy_126 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_129] using
    freshVar_not_mem
      (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f)
            (Class.cv (nb057_alpha_dummy_126 f)))).fv)
      0

theorem nb057_fresh_355 (f : Var) (a : Var) :
    (nb057_alpha_dummy_003 f a) ∉
      (({ f } : Finset Var) ∪ ({ a } : Finset Var) ∪
        ((syn_wfn (Class.cv f) (Class.cv a))).fv) :=
  by
  simpa only [nb057_alpha_dummy_003] using
    freshVar_not_mem
      (({ f } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wfn (Class.cv f) (Class.cv a))).fv)
      0

theorem nb057_fresh_356 : (nb057_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb057_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb057_fresh_357 : (nb057_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb057_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb057_distinct_358 : (nb057_alpha_dummy_000) ≠ (nb057_alpha_dummy_001) := by
  simpa only [nb057_alpha_dummy_000, nb057_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb057_support_mem_0000 :
    (nb057_alpha_dummy_001) ∈
      (({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb057_alpha_dummy_001)) (s :=
        ({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var))
        (((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv)
        ?_
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0001 (f : Var) (a : Var) :
    f ∈
      (({ f } : Finset Var) ∪ ({ a } : Finset Var) ∪
        ((syn_wfn (Class.cv f) (Class.cv a))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := f) (s := ({ f } : Finset Var) ∪ ({ a } : Finset Var))
        (((syn_wfn (Class.cv f) (Class.cv a))).fv) ?_
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0002 :
    (nb057_alpha_dummy_000) ∈
      (({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb057_alpha_dummy_000)) (s :=
        ({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var))
        (((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv)
        ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0003 (f : Var) (a : Var) :
    a ∈
      (({ f } : Finset Var) ∪ ({ a } : Finset Var) ∪
        ((syn_wfn (Class.cv f) (Class.cv a))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := a) (s := ({ f } : Finset Var) ∪ ({ a } : Finset Var))
        (((syn_wfn (Class.cv f) (Class.cv a))).fv) ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0004 :
    (nb057_alpha_dummy_001) ∈
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0005 :
    (nb057_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_004)
              (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_004)
              (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0006 (f : Var) (a : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0007 (f : Var) (a : Var) :
    f ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a)
              (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
                (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_006 f a)
              (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
                (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0008 :
    (nb057_alpha_dummy_001) ∈
      (((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0009 (f : Var) (a : Var) :
    f ∈
      (((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0010 :
    (nb057_alpha_dummy_005) ∈ (((Class.cv (nb057_alpha_dummy_005))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0011 (f : Var) (a : Var) :
    (nb057_alpha_dummy_007 f a) ∈ (((Class.cv (nb057_alpha_dummy_007 f a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0012 :
    (nb057_alpha_dummy_012) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_012)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_012)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_012))).fv) :=
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

theorem nb057_support_mem_0013 (f : Var) (a : Var) :
    (nb057_alpha_dummy_014 f a) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_014 f a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_014 f a)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_014 f a))).fv) :=
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

theorem nb057_support_mem_0014 :
    (nb057_alpha_dummy_012) ∈
      (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0015 (f : Var) (a : Var) :
    (nb057_alpha_dummy_014 f a) ∈
      (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0016 :
    (nb057_alpha_dummy_019) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_019))
            (Class.cv (nb057_alpha_dummy_020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0017 (f : Var) (a : Var) :
    (nb057_alpha_dummy_022 f a) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a))
            (Class.cv (nb057_alpha_dummy_023 f a)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a))
            (Class.cv (nb057_alpha_dummy_023 f a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0018 :
    (nb057_alpha_dummy_019) ∈
      (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0019 (f : Var) (a : Var) :
    (nb057_alpha_dummy_022 f a) ∈
      (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪
        ((Class.cv (nb057_alpha_dummy_023 f a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0020 :
    (nb057_alpha_dummy_020) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_019))
            (Class.cv (nb057_alpha_dummy_020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0021 (f : Var) (a : Var) :
    (nb057_alpha_dummy_023 f a) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a))
            (Class.cv (nb057_alpha_dummy_023 f a)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a))
            (Class.cv (nb057_alpha_dummy_023 f a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0022 :
    (nb057_alpha_dummy_020) ∈
      (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0023 (f : Var) (a : Var) :
    (nb057_alpha_dummy_023 f a) ∈
      (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪
        ((Class.cv (nb057_alpha_dummy_023 f a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0024 :
    (nb057_alpha_dummy_019) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_019)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0025 (f : Var) (a : Var) :
    (nb057_alpha_dummy_022 f a) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_022 f a)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_023 f a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0026 :
    (nb057_alpha_dummy_019) ∈
      (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_019))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0027 (f : Var) (a : Var) :
    (nb057_alpha_dummy_022 f a) ∈
      (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪
        ((Class.cv (nb057_alpha_dummy_022 f a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0028 :
    (nb057_alpha_dummy_020) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_019)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0029 (f : Var) (a : Var) :
    (nb057_alpha_dummy_023 f a) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_022 f a)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_023 f a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0030 :
    (nb057_alpha_dummy_020) ∈
      (((Class.cv (nb057_alpha_dummy_020))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0031 (f : Var) (a : Var) :
    (nb057_alpha_dummy_023 f a) ∈
      (((Class.cv (nb057_alpha_dummy_023 f a))).fv ∪
        ((Class.cv (nb057_alpha_dummy_023 f a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0032 :
    (nb057_alpha_dummy_000) ∈
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0033 :
    (nb057_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_004)
              (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_004)
              (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0034 (f : Var) (a : Var) :
    a ∈ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0035 (f : Var) (a : Var) :
    a ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a)
              (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
                (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_006 f a)
              (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
                (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0036 :
    (nb057_alpha_dummy_000) ∈
      (((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0037 (f : Var) (a : Var) :
    a ∈
      (((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0038 :
    (nb057_alpha_dummy_005) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_005))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0039 (f : Var) (a : Var) :
    (nb057_alpha_dummy_007 f a) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0040 :
    (nb057_alpha_dummy_005) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0041 (f : Var) (a : Var) :
    (nb057_alpha_dummy_007 f a) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0042 :
    (nb057_alpha_dummy_044) ∈
      (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪
        ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044))
                (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))
                (Class.cv (nb057_alpha_dummy_046))) (syn_wbr (Class.cv (nb057_alpha_dummy_046))
                (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0043 (f : Var) :
    (nb057_alpha_dummy_047 f) ∈
      (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪
        ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa
              (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb057_alpha_dummy_049 f)))
              (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f)
                (Class.cv (nb057_alpha_dummy_048 f)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb057_alpha_dummy_047 f)) (s :=
        ({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var))
        (((syn_wex (nb057_alpha_dummy_049 f) (syn_wa
              (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb057_alpha_dummy_049 f)))
              (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f)
                (Class.cv (nb057_alpha_dummy_048 f)))))).fv)
        ?_
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0044 :
    (nb057_alpha_dummy_045) ∈
      (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪
        ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044))
                (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))
                (Class.cv (nb057_alpha_dummy_046))) (syn_wbr (Class.cv (nb057_alpha_dummy_046))
                (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0045 (f : Var) :
    (nb057_alpha_dummy_048 f) ∈
      (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪
        ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa
              (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb057_alpha_dummy_049 f)))
              (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f)
                (Class.cv (nb057_alpha_dummy_048 f)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb057_alpha_dummy_048 f)) (s :=
        ({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var))
        (((syn_wex (nb057_alpha_dummy_049 f) (syn_wa
              (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb057_alpha_dummy_049 f)))
              (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f)
                (Class.cv (nb057_alpha_dummy_048 f)))))).fv)
        ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0046 :
    (nb057_alpha_dummy_044) ∈
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0047 :
    (nb057_alpha_dummy_044) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_052)
              (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_053)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_052)
              (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0048 (f : Var) :
    (nb057_alpha_dummy_047 f) ∈
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0049 (f : Var) :
    (nb057_alpha_dummy_047 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f)
              (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_054 f)
              (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0050 :
    (nb057_alpha_dummy_044) ∈
      (((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0051 (f : Var) :
    (nb057_alpha_dummy_047 f) ∈
      (((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0052 :
    (nb057_alpha_dummy_053) ∈ (((Class.cv (nb057_alpha_dummy_053))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0053 (f : Var) :
    (nb057_alpha_dummy_055 f) ∈ (((Class.cv (nb057_alpha_dummy_055 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0054 :
    (nb057_alpha_dummy_060) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_060)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_060)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_060))).fv) :=
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

theorem nb057_support_mem_0055 (f : Var) :
    (nb057_alpha_dummy_062 f) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_062 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_062 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_062 f))).fv) :=
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

theorem nb057_support_mem_0056 :
    (nb057_alpha_dummy_060) ∈
      (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0057 (f : Var) :
    (nb057_alpha_dummy_062 f) ∈
      (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0058 :
    (nb057_alpha_dummy_067) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_067))
            (Class.cv (nb057_alpha_dummy_068)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0059 (f : Var) :
    (nb057_alpha_dummy_070 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_070 f))
            (Class.cv (nb057_alpha_dummy_071 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_070 f))
            (Class.cv (nb057_alpha_dummy_071 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0060 :
    (nb057_alpha_dummy_067) ∈
      (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0061 (f : Var) :
    (nb057_alpha_dummy_070 f) ∈
      (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0062 :
    (nb057_alpha_dummy_068) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_067))
            (Class.cv (nb057_alpha_dummy_068)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0063 (f : Var) :
    (nb057_alpha_dummy_071 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_070 f))
            (Class.cv (nb057_alpha_dummy_071 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_070 f))
            (Class.cv (nb057_alpha_dummy_071 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0064 :
    (nb057_alpha_dummy_068) ∈
      (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0065 (f : Var) :
    (nb057_alpha_dummy_071 f) ∈
      (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0066 :
    (nb057_alpha_dummy_067) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_067)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_068)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0067 (f : Var) :
    (nb057_alpha_dummy_070 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_070 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_071 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0068 :
    (nb057_alpha_dummy_067) ∈
      (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_067))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0069 (f : Var) :
    (nb057_alpha_dummy_070 f) ∈
      (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_070 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0070 :
    (nb057_alpha_dummy_068) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_067)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_068)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0071 (f : Var) :
    (nb057_alpha_dummy_071 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_070 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_071 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0072 :
    (nb057_alpha_dummy_068) ∈
      (((Class.cv (nb057_alpha_dummy_068))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0073 (f : Var) :
    (nb057_alpha_dummy_071 f) ∈
      (((Class.cv (nb057_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0074 :
    (nb057_alpha_dummy_045) ∈
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0075 :
    (nb057_alpha_dummy_045) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_052)
              (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_053)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_052)
              (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0076 (f : Var) :
    (nb057_alpha_dummy_048 f) ∈
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0077 (f : Var) :
    (nb057_alpha_dummy_048 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f)
              (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_054 f)
              (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0078 :
    (nb057_alpha_dummy_045) ∈
      (((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0079 (f : Var) :
    (nb057_alpha_dummy_048 f) ∈
      (((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0080 :
    (nb057_alpha_dummy_053) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_053))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0081 (f : Var) :
    (nb057_alpha_dummy_055 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0082 :
    (nb057_alpha_dummy_053) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0083 (f : Var) :
    (nb057_alpha_dummy_055 f) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0084 :
    (nb057_alpha_dummy_044) ∈
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0085 :
    (nb057_alpha_dummy_044) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_088)
              (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_089)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_088)
              (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0086 (f : Var) :
    (nb057_alpha_dummy_047 f) ∈
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0087 (f : Var) :
    (nb057_alpha_dummy_047 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f)
              (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_090 f)
              (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0088 :
    (nb057_alpha_dummy_044) ∈
      (((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0089 (f : Var) :
    (nb057_alpha_dummy_047 f) ∈
      (((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0090 :
    (nb057_alpha_dummy_089) ∈ (((Class.cv (nb057_alpha_dummy_089))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0091 (f : Var) :
    (nb057_alpha_dummy_091 f) ∈ (((Class.cv (nb057_alpha_dummy_091 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0092 :
    (nb057_alpha_dummy_096) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_096)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_096))).fv) :=
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

theorem nb057_support_mem_0093 (f : Var) :
    (nb057_alpha_dummy_098 f) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_098 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_098 f))).fv) :=
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

theorem nb057_support_mem_0094 :
    (nb057_alpha_dummy_096) ∈
      (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0095 (f : Var) :
    (nb057_alpha_dummy_098 f) ∈
      (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0096 :
    (nb057_alpha_dummy_103) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_103))
            (Class.cv (nb057_alpha_dummy_104)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0097 (f : Var) :
    (nb057_alpha_dummy_106 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_106 f))
            (Class.cv (nb057_alpha_dummy_107 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_106 f))
            (Class.cv (nb057_alpha_dummy_107 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0098 :
    (nb057_alpha_dummy_103) ∈
      (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0099 (f : Var) :
    (nb057_alpha_dummy_106 f) ∈
      (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0100 :
    (nb057_alpha_dummy_104) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_103))
            (Class.cv (nb057_alpha_dummy_104)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0101 (f : Var) :
    (nb057_alpha_dummy_107 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_106 f))
            (Class.cv (nb057_alpha_dummy_107 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_106 f))
            (Class.cv (nb057_alpha_dummy_107 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0102 :
    (nb057_alpha_dummy_104) ∈
      (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part006`. -/


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

theorem nb057_support_mem_0103 (f : Var) :
    (nb057_alpha_dummy_107 f) ∈
      (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0104 :
    (nb057_alpha_dummy_103) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_103)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_104)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0105 (f : Var) :
    (nb057_alpha_dummy_106 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_106 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_107 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0106 :
    (nb057_alpha_dummy_103) ∈
      (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_103))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0107 (f : Var) :
    (nb057_alpha_dummy_106 f) ∈
      (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_106 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0108 :
    (nb057_alpha_dummy_104) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_103)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_104)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0109 (f : Var) :
    (nb057_alpha_dummy_107 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_106 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_107 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0110 :
    (nb057_alpha_dummy_104) ∈
      (((Class.cv (nb057_alpha_dummy_104))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0111 (f : Var) :
    (nb057_alpha_dummy_107 f) ∈
      (((Class.cv (nb057_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0112 :
    (nb057_alpha_dummy_046) ∈
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0113 :
    (nb057_alpha_dummy_046) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_088)
              (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_089)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_088)
              (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0114 (f : Var) :
    (nb057_alpha_dummy_049 f) ∈
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0115 (f : Var) :
    (nb057_alpha_dummy_049 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f)
              (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_090 f)
              (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0116 :
    (nb057_alpha_dummy_046) ∈
      (((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0117 (f : Var) :
    (nb057_alpha_dummy_049 f) ∈
      (((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0118 :
    (nb057_alpha_dummy_089) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_089))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0119 (f : Var) :
    (nb057_alpha_dummy_091 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0120 :
    (nb057_alpha_dummy_089) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0121 (f : Var) :
    (nb057_alpha_dummy_091 f) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0122 :
    (nb057_alpha_dummy_124) ∈
      (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001))
            (Class.cv (nb057_alpha_dummy_124)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0123 (f : Var) :
    (nb057_alpha_dummy_126 f) ∈
      (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f)
            (Class.cv (nb057_alpha_dummy_126 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0124 :
    (nb057_alpha_dummy_125) ∈
      (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001))
            (Class.cv (nb057_alpha_dummy_124)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0125 (f : Var) :
    (nb057_alpha_dummy_127 f) ∈
      (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f)
            (Class.cv (nb057_alpha_dummy_126 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0126 :
    (nb057_alpha_dummy_124) ∈
      (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0127 :
    (nb057_alpha_dummy_124) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_130)
              (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_131)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_130)
              (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0128 (f : Var) :
    (nb057_alpha_dummy_126 f) ∈
      (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0129 (f : Var) :
    (nb057_alpha_dummy_126 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f)
              (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_132 f)
              (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0130 :
    (nb057_alpha_dummy_124) ∈
      (((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0131 (f : Var) :
    (nb057_alpha_dummy_126 f) ∈
      (((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0132 :
    (nb057_alpha_dummy_131) ∈ (((Class.cv (nb057_alpha_dummy_131))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0133 (f : Var) :
    (nb057_alpha_dummy_133 f) ∈ (((Class.cv (nb057_alpha_dummy_133 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0134 :
    (nb057_alpha_dummy_138) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_138))).fv) :=
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

theorem nb057_support_mem_0135 (f : Var) :
    (nb057_alpha_dummy_140 f) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_140 f))).fv) :=
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

theorem nb057_support_mem_0136 :
    (nb057_alpha_dummy_138) ∈
      (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0137 (f : Var) :
    (nb057_alpha_dummy_140 f) ∈
      (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0138 :
    (nb057_alpha_dummy_145) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_145))
            (Class.cv (nb057_alpha_dummy_146)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0139 (f : Var) :
    (nb057_alpha_dummy_148 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0140 :
    (nb057_alpha_dummy_145) ∈
      (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0141 (f : Var) :
    (nb057_alpha_dummy_148 f) ∈
      (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0142 :
    (nb057_alpha_dummy_146) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_145))
            (Class.cv (nb057_alpha_dummy_146)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0143 (f : Var) :
    (nb057_alpha_dummy_149 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0144 :
    (nb057_alpha_dummy_146) ∈
      (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0145 (f : Var) :
    (nb057_alpha_dummy_149 f) ∈
      (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0146 :
    (nb057_alpha_dummy_145) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_145)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_146)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0147 (f : Var) :
    (nb057_alpha_dummy_148 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_148 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_149 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0148 :
    (nb057_alpha_dummy_145) ∈
      (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_145))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0149 (f : Var) :
    (nb057_alpha_dummy_148 f) ∈
      (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_148 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0150 :
    (nb057_alpha_dummy_146) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_145)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_146)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0151 (f : Var) :
    (nb057_alpha_dummy_149 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_148 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_149 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0152 :
    (nb057_alpha_dummy_146) ∈
      (((Class.cv (nb057_alpha_dummy_146))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0153 (f : Var) :
    (nb057_alpha_dummy_149 f) ∈
      (((Class.cv (nb057_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0154 :
    (nb057_alpha_dummy_125) ∈
      (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0155 :
    (nb057_alpha_dummy_125) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_130)
              (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_131)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_130)
              (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0156 (f : Var) :
    (nb057_alpha_dummy_127 f) ∈
      (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0157 (f : Var) :
    (nb057_alpha_dummy_127 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f)
              (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_132 f)
              (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0158 :
    (nb057_alpha_dummy_125) ∈
      (((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0159 (f : Var) :
    (nb057_alpha_dummy_127 f) ∈
      (((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0160 :
    (nb057_alpha_dummy_131) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_131))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0161 (f : Var) :
    (nb057_alpha_dummy_133 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0162 :
    (nb057_alpha_dummy_131) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0163 (f : Var) :
    (nb057_alpha_dummy_133 f) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0164 :
    (nb057_alpha_dummy_125) ∈
      (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0165 :
    (nb057_alpha_dummy_125) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_166)
              (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_167)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_166)
              (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0166 (f : Var) :
    (nb057_alpha_dummy_127 f) ∈
      (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0167 (f : Var) :
    (nb057_alpha_dummy_127 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f)
              (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_168 f)
              (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0168 :
    (nb057_alpha_dummy_125) ∈
      (((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0169 (f : Var) :
    (nb057_alpha_dummy_127 f) ∈
      (((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0170 :
    (nb057_alpha_dummy_167) ∈ (((Class.cv (nb057_alpha_dummy_167))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0171 (f : Var) :
    (nb057_alpha_dummy_169 f) ∈ (((Class.cv (nb057_alpha_dummy_169 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0172 :
    (nb057_alpha_dummy_174) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_174)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_174)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_174))).fv) :=
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

theorem nb057_support_mem_0173 (f : Var) :
    (nb057_alpha_dummy_176 f) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_176 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_176 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_176 f))).fv) :=
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

theorem nb057_support_mem_0174 :
    (nb057_alpha_dummy_174) ∈
      (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0175 (f : Var) :
    (nb057_alpha_dummy_176 f) ∈
      (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0176 :
    (nb057_alpha_dummy_181) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_181))
            (Class.cv (nb057_alpha_dummy_182)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0177 (f : Var) :
    (nb057_alpha_dummy_184 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0178 :
    (nb057_alpha_dummy_181) ∈
      (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0179 (f : Var) :
    (nb057_alpha_dummy_184 f) ∈
      (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0180 :
    (nb057_alpha_dummy_182) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_181))
            (Class.cv (nb057_alpha_dummy_182)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0181 (f : Var) :
    (nb057_alpha_dummy_185 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0182 :
    (nb057_alpha_dummy_182) ∈
      (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0183 (f : Var) :
    (nb057_alpha_dummy_185 f) ∈
      (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0184 :
    (nb057_alpha_dummy_181) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_181)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_182)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0185 (f : Var) :
    (nb057_alpha_dummy_184 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_184 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_185 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0186 :
    (nb057_alpha_dummy_181) ∈
      (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_181))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0187 (f : Var) :
    (nb057_alpha_dummy_184 f) ∈
      (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_184 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0188 :
    (nb057_alpha_dummy_182) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_181)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_182)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0189 (f : Var) :
    (nb057_alpha_dummy_185 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_184 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_185 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0190 :
    (nb057_alpha_dummy_182) ∈
      (((Class.cv (nb057_alpha_dummy_182))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0191 (f : Var) :
    (nb057_alpha_dummy_185 f) ∈
      (((Class.cv (nb057_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0192 :
    (nb057_alpha_dummy_124) ∈
      (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0193 :
    (nb057_alpha_dummy_124) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_166)
              (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_167)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_166)
              (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0194 (f : Var) :
    (nb057_alpha_dummy_126 f) ∈
      (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0195 (f : Var) :
    (nb057_alpha_dummy_126 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f)
              (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_168 f)
              (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0196 :
    (nb057_alpha_dummy_124) ∈
      (((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0197 (f : Var) :
    (nb057_alpha_dummy_126 f) ∈
      (((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0198 :
    (nb057_alpha_dummy_167) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_167))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0199 (f : Var) :
    (nb057_alpha_dummy_169 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0200 :
    (nb057_alpha_dummy_167) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0201 (f : Var) :
    (nb057_alpha_dummy_169 f) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0202 :
    (nb057_alpha_dummy_001) ∈
      (((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb057_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv) :=
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

theorem nb057_support_mem_0203 (f : Var) :
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

theorem nb057_support_mem_0204 :
    (nb057_alpha_dummy_001) ∈
      (((syn_ccom (Class.cv (nb057_alpha_dummy_001))
            (syn_ccnv (Class.cv (nb057_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0205 (f : Var) :
    f ∈ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0206 :
    (nb057_alpha_dummy_001) ∈
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0207 :
    (nb057_alpha_dummy_001) ∈
      (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪
        ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044))
                (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))
                (Class.cv (nb057_alpha_dummy_046))) (syn_wbr (Class.cv (nb057_alpha_dummy_046))
                (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 2))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb057_support_mem_0208 (f : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0209 (f : Var) :
    f ∈
      (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪
        ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa
              (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb057_alpha_dummy_049 f)))
              (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f)
                (Class.cv (nb057_alpha_dummy_048 f)))))).fv) :=
  by
  have fresh : f ≠ nb057_alpha_dummy_049 f :=
    by
    unfold nb057_alpha_dummy_049
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 2))
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · with_reducible exact fresh
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb057_support_mem_0210 :
    (nb057_alpha_dummy_001) ∈
      (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001))
            (Class.cv (nb057_alpha_dummy_124)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0211 (f : Var) :
    f ∈
      (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f)
            (Class.cv (nb057_alpha_dummy_126 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0212 :
    (nb057_alpha_dummy_001) ∈ (((Class.cv (nb057_alpha_dummy_001))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0213 (f : Var) : f ∈ (((Class.cv f)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0214 :
    (nb057_alpha_dummy_046) ∈
      (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0215 :
    (nb057_alpha_dummy_046) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_202)
              (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_203)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_202)
              (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0216 (f : Var) :
    (nb057_alpha_dummy_049 f) ∈
      (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0217 (f : Var) :
    (nb057_alpha_dummy_049 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f)
              (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_204 f)
              (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0218 :
    (nb057_alpha_dummy_046) ∈
      (((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0219 (f : Var) :
    (nb057_alpha_dummy_049 f) ∈
      (((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0220 :
    (nb057_alpha_dummy_203) ∈ (((Class.cv (nb057_alpha_dummy_203))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0221 (f : Var) :
    (nb057_alpha_dummy_205 f) ∈ (((Class.cv (nb057_alpha_dummy_205 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0222 :
    (nb057_alpha_dummy_210) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_210)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_210)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_210))).fv) :=
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

theorem nb057_support_mem_0223 (f : Var) :
    (nb057_alpha_dummy_212 f) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_212 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_212 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_212 f))).fv) :=
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

theorem nb057_support_mem_0224 :
    (nb057_alpha_dummy_210) ∈
      (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0225 (f : Var) :
    (nb057_alpha_dummy_212 f) ∈
      (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0226 :
    (nb057_alpha_dummy_217) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_217))
            (Class.cv (nb057_alpha_dummy_218)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0227 (f : Var) :
    (nb057_alpha_dummy_220 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_220 f))
            (Class.cv (nb057_alpha_dummy_221 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_220 f))
            (Class.cv (nb057_alpha_dummy_221 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0228 :
    (nb057_alpha_dummy_217) ∈
      (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0229 (f : Var) :
    (nb057_alpha_dummy_220 f) ∈
      (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0230 :
    (nb057_alpha_dummy_218) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_217))
            (Class.cv (nb057_alpha_dummy_218)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0231 (f : Var) :
    (nb057_alpha_dummy_221 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_220 f))
            (Class.cv (nb057_alpha_dummy_221 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_220 f))
            (Class.cv (nb057_alpha_dummy_221 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0232 :
    (nb057_alpha_dummy_218) ∈
      (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0233 (f : Var) :
    (nb057_alpha_dummy_221 f) ∈
      (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0234 :
    (nb057_alpha_dummy_217) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_217)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_218)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0235 (f : Var) :
    (nb057_alpha_dummy_220 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_220 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_221 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0236 :
    (nb057_alpha_dummy_217) ∈
      (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_217))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0237 (f : Var) :
    (nb057_alpha_dummy_220 f) ∈
      (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_220 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0238 :
    (nb057_alpha_dummy_218) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_217)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_218)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0239 (f : Var) :
    (nb057_alpha_dummy_221 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_220 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_221 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0240 :
    (nb057_alpha_dummy_218) ∈
      (((Class.cv (nb057_alpha_dummy_218))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0241 (f : Var) :
    (nb057_alpha_dummy_221 f) ∈
      (((Class.cv (nb057_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0242 :
    (nb057_alpha_dummy_045) ∈
      (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0243 :
    (nb057_alpha_dummy_045) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_202)
              (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_203)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_202)
              (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0244 (f : Var) :
    (nb057_alpha_dummy_048 f) ∈
      (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0245 (f : Var) :
    (nb057_alpha_dummy_048 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f)
              (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_204 f)
              (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
