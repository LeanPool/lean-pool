/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part012`. -/


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

theorem nb078_fresh_254 (h : Var) :
    (nb078_alpha_dummy_1020 h) ∉ (((Class.cv (nb078_alpha_dummy_1012 h))).fv) := by
  simpa only [nb078_alpha_dummy_1020] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1012 h))).fv) 1

theorem nb078_distinct_255 (h : Var) :
    (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1020 h) := by
  simpa only [nb078_alpha_dummy_1019, nb078_alpha_dummy_1020] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1012 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_256 :
    (nb078_alpha_dummy_1023) ∉
      (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1023] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_257 :
    (nb078_alpha_dummy_1024) ∉
      (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1024] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_258 :
    (nb078_alpha_dummy_1025) ∉
      (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1025] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_259 : (nb078_alpha_dummy_1023) ≠ (nb078_alpha_dummy_1024) := by
  simpa only [nb078_alpha_dummy_1023, nb078_alpha_dummy_1024] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_260 : (nb078_alpha_dummy_1023) ≠ (nb078_alpha_dummy_1025) := by
  simpa only [nb078_alpha_dummy_1023, nb078_alpha_dummy_1025] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_261 : (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1025) := by
  simpa only [nb078_alpha_dummy_1024, nb078_alpha_dummy_1025] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_262 (h : Var) :
    (nb078_alpha_dummy_1026 h) ∉
      (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1026] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_263 (h : Var) :
    (nb078_alpha_dummy_1027 h) ∉
      (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1027] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_264 (h : Var) :
    (nb078_alpha_dummy_1028 h) ∉
      (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1028] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_265 (h : Var) :
    (nb078_alpha_dummy_1026 h) ≠ (nb078_alpha_dummy_1027 h) := by
  simpa only [nb078_alpha_dummy_1026, nb078_alpha_dummy_1027] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_266 (h : Var) :
    (nb078_alpha_dummy_1026 h) ≠ (nb078_alpha_dummy_1028 h) := by
  simpa only [nb078_alpha_dummy_1026, nb078_alpha_dummy_1028] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_267 (h : Var) :
    (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1028 h) := by
  simpa only [nb078_alpha_dummy_1027, nb078_alpha_dummy_1028] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_268 :
    (nb078_alpha_dummy_1035) ∉
      (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1024))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1035] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1024))).fv)
      0

theorem nb078_fresh_269 :
    (nb078_alpha_dummy_1031) ∉
      (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1031] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv)
      0

theorem nb078_fresh_270 :
    (nb078_alpha_dummy_1037) ∉
      (((Class.cv (nb078_alpha_dummy_1025))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1037] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1025))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv)
      0

theorem nb078_fresh_271 (h : Var) :
    (nb078_alpha_dummy_1036 h) ∉
      (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1027 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1036] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1027 h))).fv)
      0

theorem nb078_fresh_272 (h : Var) :
    (nb078_alpha_dummy_1032 h) ∉
      (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1028 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1032] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1028 h))).fv)
      0

theorem nb078_fresh_273 (h : Var) :
    (nb078_alpha_dummy_1038 h) ∉
      (((Class.cv (nb078_alpha_dummy_1028 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1028 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1038] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1028 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1028 h))).fv)
      0

theorem nb078_fresh_274 :
    (nb078_alpha_dummy_109) ∉
      (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_109] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_275 :
    (nb078_alpha_dummy_110) ∉
      (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_110] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_276 :
    (nb078_alpha_dummy_111) ∉
      (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_111] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_277 : (nb078_alpha_dummy_109) ≠ (nb078_alpha_dummy_110) := by
  simpa only [nb078_alpha_dummy_109, nb078_alpha_dummy_110] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_278 : (nb078_alpha_dummy_109) ≠ (nb078_alpha_dummy_111) := by
  simpa only [nb078_alpha_dummy_109, nb078_alpha_dummy_111] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_279 : (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_111) := by
  simpa only [nb078_alpha_dummy_110, nb078_alpha_dummy_111] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_280 :
    (nb078_alpha_dummy_1057) ∉
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1057] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv)
      0

theorem nb078_fresh_281 :
    (nb078_alpha_dummy_1058) ∉
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1058] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv)
      1

theorem nb078_distinct_282 : (nb078_alpha_dummy_1057) ≠ (nb078_alpha_dummy_1058) := by
  simpa only [nb078_alpha_dummy_1057, nb078_alpha_dummy_1058] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1049))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1050))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_283 :
    (nb078_alpha_dummy_1093) ∉
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1093] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv)
      0

theorem nb078_fresh_284 :
    (nb078_alpha_dummy_1094) ∉
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1094] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv)
      1

theorem nb078_distinct_285 : (nb078_alpha_dummy_1093) ≠ (nb078_alpha_dummy_1094) := by
  simpa only [nb078_alpha_dummy_1093, nb078_alpha_dummy_1094] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1049))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1051))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_286 (f : Var) :
    (nb078_alpha_dummy_112 f) ∉
      (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_112] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_287 (f : Var) :
    (nb078_alpha_dummy_113 f) ∉
      (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_113] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_288 (f : Var) :
    (nb078_alpha_dummy_114 f) ∉
      (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_114] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_289 (f : Var) :
    (nb078_alpha_dummy_112 f) ≠ (nb078_alpha_dummy_113 f) := by
  simpa only [nb078_alpha_dummy_112, nb078_alpha_dummy_113] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_290 (f : Var) :
    (nb078_alpha_dummy_112 f) ≠ (nb078_alpha_dummy_114 f) := by
  simpa only [nb078_alpha_dummy_112, nb078_alpha_dummy_114] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_291 (f : Var) :
    (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_114 f) := by
  simpa only [nb078_alpha_dummy_113, nb078_alpha_dummy_114] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_292 :
    (nb078_alpha_dummy_1207) ∉
      (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1207] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv)
      0

theorem nb078_fresh_293 :
    (nb078_alpha_dummy_1208) ∉
      (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1208] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv)
      1

theorem nb078_distinct_294 : (nb078_alpha_dummy_1207) ≠ (nb078_alpha_dummy_1208) := by
  simpa only [nb078_alpha_dummy_1207, nb078_alpha_dummy_1208] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1051))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1050))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_295 (h : Var) :
    (nb078_alpha_dummy_1059 h) ∉
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1059] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv)
      0

theorem nb078_fresh_296 (h : Var) :
    (nb078_alpha_dummy_1060 h) ∉
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1060] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv)
      1

theorem nb078_distinct_297 (h : Var) :
    (nb078_alpha_dummy_1059 h) ≠ (nb078_alpha_dummy_1060 h) := by
  simpa only [nb078_alpha_dummy_1059, nb078_alpha_dummy_1060] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_298 (h : Var) :
    (nb078_alpha_dummy_1095 h) ∉
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1054 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1095] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1054 h))).fv)
      0

theorem nb078_fresh_299 (h : Var) :
    (nb078_alpha_dummy_1096 h) ∉
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1054 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1096] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1054 h))).fv)
      1

theorem nb078_distinct_300 (h : Var) :
    (nb078_alpha_dummy_1095 h) ≠ (nb078_alpha_dummy_1096 h) := by
  simpa only [nb078_alpha_dummy_1095, nb078_alpha_dummy_1096] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1054 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_301 (h : Var) :
    (nb078_alpha_dummy_1209 h) ∉
      (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1209] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv)
      0

theorem nb078_fresh_302 (h : Var) :
    (nb078_alpha_dummy_1210 h) ∉
      (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1210] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv)
      1

theorem nb078_distinct_303 (h : Var) :
    (nb078_alpha_dummy_1209 h) ≠ (nb078_alpha_dummy_1210 h) := by
  simpa only [nb078_alpha_dummy_1209, nb078_alpha_dummy_1210] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_304 :
    (nb078_alpha_dummy_1065) ∉ (((Class.cv (nb078_alpha_dummy_1058))).fv) := by
  simpa only [nb078_alpha_dummy_1065] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1058))).fv) 0

theorem nb078_fresh_305 :
    (nb078_alpha_dummy_1066) ∉ (((Class.cv (nb078_alpha_dummy_1058))).fv) := by
  simpa only [nb078_alpha_dummy_1066] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1058))).fv) 1

theorem nb078_distinct_306 : (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1066) := by
  simpa only [nb078_alpha_dummy_1065, nb078_alpha_dummy_1066] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1058))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_307 (h : Var) :
    (nb078_alpha_dummy_1067 h) ∉ (((Class.cv (nb078_alpha_dummy_1060 h))).fv) := by
  simpa only [nb078_alpha_dummy_1067] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1060 h))).fv) 0

theorem nb078_fresh_308 (h : Var) :
    (nb078_alpha_dummy_1068 h) ∉ (((Class.cv (nb078_alpha_dummy_1060 h))).fv) := by
  simpa only [nb078_alpha_dummy_1068] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1060 h))).fv) 1

theorem nb078_distinct_309 (h : Var) :
    (nb078_alpha_dummy_1067 h) ≠ (nb078_alpha_dummy_1068 h) := by
  simpa only [nb078_alpha_dummy_1067, nb078_alpha_dummy_1068] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1060 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_310 :
    (nb078_alpha_dummy_1071) ∉
      (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1071] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_311 :
    (nb078_alpha_dummy_1072) ∉
      (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1072] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_312 :
    (nb078_alpha_dummy_1073) ∉
      (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1073] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_313 : (nb078_alpha_dummy_1071) ≠ (nb078_alpha_dummy_1072) := by
  simpa only [nb078_alpha_dummy_1071, nb078_alpha_dummy_1072] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_314 : (nb078_alpha_dummy_1071) ≠ (nb078_alpha_dummy_1073) := by
  simpa only [nb078_alpha_dummy_1071, nb078_alpha_dummy_1073] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_315 : (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1073) := by
  simpa only [nb078_alpha_dummy_1072, nb078_alpha_dummy_1073] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_316 (h : Var) :
    (nb078_alpha_dummy_1074 h) ∉
      (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1074] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_317 (h : Var) :
    (nb078_alpha_dummy_1075 h) ∉
      (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1075] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_318 (h : Var) :
    (nb078_alpha_dummy_1076 h) ∉
      (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1076] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_319 (h : Var) :
    (nb078_alpha_dummy_1074 h) ≠ (nb078_alpha_dummy_1075 h) := by
  simpa only [nb078_alpha_dummy_1074, nb078_alpha_dummy_1075] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_320 (h : Var) :
    (nb078_alpha_dummy_1074 h) ≠ (nb078_alpha_dummy_1076 h) := by
  simpa only [nb078_alpha_dummy_1074, nb078_alpha_dummy_1076] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_321 (h : Var) :
    (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1076 h) := by
  simpa only [nb078_alpha_dummy_1075, nb078_alpha_dummy_1076] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_322 :
    (nb078_alpha_dummy_1083) ∉
      (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1072))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1083] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1072))).fv)
      0

theorem nb078_fresh_323 :
    (nb078_alpha_dummy_1079) ∉
      (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1079] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv)
      0

theorem nb078_fresh_324 :
    (nb078_alpha_dummy_1085) ∉
      (((Class.cv (nb078_alpha_dummy_1073))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1085] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1073))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv)
      0

theorem nb078_fresh_325 (h : Var) :
    (nb078_alpha_dummy_1084 h) ∉
      (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1075 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1084] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1075 h))).fv)
      0

theorem nb078_fresh_326 (h : Var) :
    (nb078_alpha_dummy_1080 h) ∉
      (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1076 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1080] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1076 h))).fv)
      0

theorem nb078_fresh_327 (h : Var) :
    (nb078_alpha_dummy_1086 h) ∉
      (((Class.cv (nb078_alpha_dummy_1076 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1076 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1086] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1076 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1076 h))).fv)
      0

theorem nb078_fresh_328 :
    (nb078_alpha_dummy_1101) ∉ (((Class.cv (nb078_alpha_dummy_1094))).fv) := by
  simpa only [nb078_alpha_dummy_1101] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1094))).fv) 0

theorem nb078_fresh_329 :
    (nb078_alpha_dummy_1102) ∉ (((Class.cv (nb078_alpha_dummy_1094))).fv) := by
  simpa only [nb078_alpha_dummy_1102] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1094))).fv) 1

theorem nb078_distinct_330 : (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1102) := by
  simpa only [nb078_alpha_dummy_1101, nb078_alpha_dummy_1102] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1094))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_331 (h : Var) :
    (nb078_alpha_dummy_1103 h) ∉ (((Class.cv (nb078_alpha_dummy_1096 h))).fv) := by
  simpa only [nb078_alpha_dummy_1103] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1096 h))).fv) 0

theorem nb078_fresh_332 (h : Var) :
    (nb078_alpha_dummy_1104 h) ∉ (((Class.cv (nb078_alpha_dummy_1096 h))).fv) := by
  simpa only [nb078_alpha_dummy_1104] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1096 h))).fv) 1

theorem nb078_distinct_333 (h : Var) :
    (nb078_alpha_dummy_1103 h) ≠ (nb078_alpha_dummy_1104 h) := by
  simpa only [nb078_alpha_dummy_1103, nb078_alpha_dummy_1104] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1096 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_334 :
    (nb078_alpha_dummy_121) ∉
      (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_110))).fv) :=
  by
  simpa only [nb078_alpha_dummy_121] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_110))).fv)
      0

theorem nb078_fresh_335 :
    (nb078_alpha_dummy_117) ∉
      (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) :=
  by
  simpa only [nb078_alpha_dummy_117] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv)
      0

theorem nb078_fresh_336 :
    (nb078_alpha_dummy_1107) ∉
      (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1107] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_337 :
    (nb078_alpha_dummy_1108) ∉
      (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1108] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_338 :
    (nb078_alpha_dummy_1109) ∉
      (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1109] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_339 : (nb078_alpha_dummy_1107) ≠ (nb078_alpha_dummy_1108) := by
  simpa only [nb078_alpha_dummy_1107, nb078_alpha_dummy_1108] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_340 : (nb078_alpha_dummy_1107) ≠ (nb078_alpha_dummy_1109) := by
  simpa only [nb078_alpha_dummy_1107, nb078_alpha_dummy_1109] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_341 : (nb078_alpha_dummy_1108) ≠ (nb078_alpha_dummy_1109) := by
  simpa only [nb078_alpha_dummy_1108, nb078_alpha_dummy_1109] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_342 (h : Var) :
    (nb078_alpha_dummy_1110 h) ∉
      (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1110] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_343 (h : Var) :
    (nb078_alpha_dummy_1111 h) ∉
      (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1111] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_344 (h : Var) :
    (nb078_alpha_dummy_1112 h) ∉
      (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1112] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_345 (h : Var) :
    (nb078_alpha_dummy_1110 h) ≠ (nb078_alpha_dummy_1111 h) := by
  simpa only [nb078_alpha_dummy_1110, nb078_alpha_dummy_1111] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_346 (h : Var) :
    (nb078_alpha_dummy_1110 h) ≠ (nb078_alpha_dummy_1112 h) := by
  simpa only [nb078_alpha_dummy_1110, nb078_alpha_dummy_1112] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_347 (h : Var) :
    (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1112 h) := by
  simpa only [nb078_alpha_dummy_1111, nb078_alpha_dummy_1112] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_348 :
    (nb078_alpha_dummy_1119) ∉
      (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1108))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1119] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1108))).fv)
      0

theorem nb078_fresh_349 :
    (nb078_alpha_dummy_1115) ∉
      (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1115] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv)
      0

theorem nb078_fresh_350 :
    (nb078_alpha_dummy_1121) ∉
      (((Class.cv (nb078_alpha_dummy_1109))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1121] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1109))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv)
      0

theorem nb078_fresh_351 :
    (nb078_alpha_dummy_123) ∉
      (((Class.cv (nb078_alpha_dummy_111))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) :=
  by
  simpa only [nb078_alpha_dummy_123] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_111))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv)
      0

theorem nb078_fresh_352 (h : Var) :
    (nb078_alpha_dummy_1120 h) ∉
      (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1111 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1120] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1111 h))).fv)
      0

theorem nb078_fresh_353 (h : Var) :
    (nb078_alpha_dummy_1116 h) ∉
      (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1112 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1116] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1112 h))).fv)
      0

theorem nb078_fresh_354 (h : Var) :
    (nb078_alpha_dummy_1122 h) ∉
      (((Class.cv (nb078_alpha_dummy_1112 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1112 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1122] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1112 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1112 h))).fv)
      0

theorem nb078_fresh_355 :
    (nb078_alpha_dummy_1135) ∉
      (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1135] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv)
      0

theorem nb078_fresh_356 :
    (nb078_alpha_dummy_1136) ∉
      (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1136] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv)
      1

theorem nb078_distinct_357 : (nb078_alpha_dummy_1135) ≠ (nb078_alpha_dummy_1136) := by
  simpa only [nb078_alpha_dummy_1135, nb078_alpha_dummy_1136] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1129))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1130))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_358 (f : Var) :
    (nb078_alpha_dummy_122 f) ∉
      (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_113 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_122] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_113 f))).fv)
      0

theorem nb078_fresh_359 (f : Var) :
    (nb078_alpha_dummy_118 f) ∉
      (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_118] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv)
      0

theorem nb078_fresh_360 :
    (nb078_alpha_dummy_1171) ∉
      (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1171] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv)
      0

theorem nb078_fresh_361 :
    (nb078_alpha_dummy_1172) ∉
      (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1172] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv)
      1

theorem nb078_distinct_362 : (nb078_alpha_dummy_1171) ≠ (nb078_alpha_dummy_1172) := by
  simpa only [nb078_alpha_dummy_1171, nb078_alpha_dummy_1172] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1130))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1129))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_363 (h : Var) :
    (nb078_alpha_dummy_1137 h) ∉
      (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1132 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1137] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1132 h))).fv)
      0

theorem nb078_fresh_364 (h : Var) :
    (nb078_alpha_dummy_1138 h) ∉
      (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1132 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1138] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1132 h))).fv)
      1

theorem nb078_distinct_365 (h : Var) :
    (nb078_alpha_dummy_1137 h) ≠ (nb078_alpha_dummy_1138 h) := by
  simpa only [nb078_alpha_dummy_1137, nb078_alpha_dummy_1138] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1132 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_366 (h : Var) :
    (nb078_alpha_dummy_1173 h) ∉
      (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1131 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1173] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1131 h))).fv)
      0

theorem nb078_fresh_367 (h : Var) :
    (nb078_alpha_dummy_1174 h) ∉
      (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1131 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1174] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1131 h))).fv)
      1

theorem nb078_distinct_368 (h : Var) :
    (nb078_alpha_dummy_1173 h) ≠ (nb078_alpha_dummy_1174 h) := by
  simpa only [nb078_alpha_dummy_1173, nb078_alpha_dummy_1174] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1131 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_369 :
    (nb078_alpha_dummy_1143) ∉ (((Class.cv (nb078_alpha_dummy_1136))).fv) := by
  simpa only [nb078_alpha_dummy_1143] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1136))).fv) 0

theorem nb078_fresh_370 :
    (nb078_alpha_dummy_1144) ∉ (((Class.cv (nb078_alpha_dummy_1136))).fv) := by
  simpa only [nb078_alpha_dummy_1144] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1136))).fv) 1

theorem nb078_distinct_371 : (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1144) := by
  simpa only [nb078_alpha_dummy_1143, nb078_alpha_dummy_1144] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1136))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_372 (h : Var) :
    (nb078_alpha_dummy_1145 h) ∉ (((Class.cv (nb078_alpha_dummy_1138 h))).fv) := by
  simpa only [nb078_alpha_dummy_1145] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1138 h))).fv) 0

theorem nb078_fresh_373 (h : Var) :
    (nb078_alpha_dummy_1146 h) ∉ (((Class.cv (nb078_alpha_dummy_1138 h))).fv) := by
  simpa only [nb078_alpha_dummy_1146] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1138 h))).fv) 1

theorem nb078_distinct_374 (h : Var) :
    (nb078_alpha_dummy_1145 h) ≠ (nb078_alpha_dummy_1146 h) := by
  simpa only [nb078_alpha_dummy_1145, nb078_alpha_dummy_1146] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1138 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_375 (f : Var) :
    (nb078_alpha_dummy_124 f) ∉
      (((Class.cv (nb078_alpha_dummy_114 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_124] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_114 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv)
      0

theorem nb078_fresh_376 :
    (nb078_alpha_dummy_1149) ∉
      (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1149] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_377 :
    (nb078_alpha_dummy_1150) ∉
      (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1150] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_378 :
    (nb078_alpha_dummy_1151) ∉
      (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1151] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_379 : (nb078_alpha_dummy_1149) ≠ (nb078_alpha_dummy_1150) := by
  simpa only [nb078_alpha_dummy_1149, nb078_alpha_dummy_1150] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_380 : (nb078_alpha_dummy_1149) ≠ (nb078_alpha_dummy_1151) := by
  simpa only [nb078_alpha_dummy_1149, nb078_alpha_dummy_1151] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_381 : (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1151) := by
  simpa only [nb078_alpha_dummy_1150, nb078_alpha_dummy_1151] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_382 (h : Var) :
    (nb078_alpha_dummy_1152 h) ∉
      (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1152] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_383 (h : Var) :
    (nb078_alpha_dummy_1153 h) ∉
      (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1153] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_384 (h : Var) :
    (nb078_alpha_dummy_1154 h) ∉
      (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1154] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_385 (h : Var) :
    (nb078_alpha_dummy_1152 h) ≠ (nb078_alpha_dummy_1153 h) := by
  simpa only [nb078_alpha_dummy_1152, nb078_alpha_dummy_1153] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_386 (h : Var) :
    (nb078_alpha_dummy_1152 h) ≠ (nb078_alpha_dummy_1154 h) := by
  simpa only [nb078_alpha_dummy_1152, nb078_alpha_dummy_1154] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_387 (h : Var) :
    (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1154 h) := by
  simpa only [nb078_alpha_dummy_1153, nb078_alpha_dummy_1154] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_388 :
    (nb078_alpha_dummy_1161) ∉
      (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1150))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1161] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1150))).fv)
      0

theorem nb078_fresh_389 :
    (nb078_alpha_dummy_1157) ∉
      (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1157] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv)
      0

theorem nb078_fresh_390 :
    (nb078_alpha_dummy_1163) ∉
      (((Class.cv (nb078_alpha_dummy_1151))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1163] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1151))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv)
      0

theorem nb078_fresh_391 (h : Var) :
    (nb078_alpha_dummy_1162 h) ∉
      (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1153 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1162] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1153 h))).fv)
      0

theorem nb078_fresh_392 (h : Var) :
    (nb078_alpha_dummy_1158 h) ∉
      (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1154 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1158] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1154 h))).fv)
      0

theorem nb078_fresh_393 (h : Var) :
    (nb078_alpha_dummy_1164 h) ∉
      (((Class.cv (nb078_alpha_dummy_1154 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1154 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1164] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1154 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1154 h))).fv)
      0

theorem nb078_fresh_394 :
    (nb078_alpha_dummy_1179) ∉ (((Class.cv (nb078_alpha_dummy_1172))).fv) := by
  simpa only [nb078_alpha_dummy_1179] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1172))).fv) 0

theorem nb078_fresh_395 :
    (nb078_alpha_dummy_1180) ∉ (((Class.cv (nb078_alpha_dummy_1172))).fv) := by
  simpa only [nb078_alpha_dummy_1180] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1172))).fv) 1

theorem nb078_distinct_396 : (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1180) := by
  simpa only [nb078_alpha_dummy_1179, nb078_alpha_dummy_1180] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1172))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_397 (h : Var) :
    (nb078_alpha_dummy_1181 h) ∉ (((Class.cv (nb078_alpha_dummy_1174 h))).fv) := by
  simpa only [nb078_alpha_dummy_1181] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1174 h))).fv) 0

theorem nb078_fresh_398 (h : Var) :
    (nb078_alpha_dummy_1182 h) ∉ (((Class.cv (nb078_alpha_dummy_1174 h))).fv) := by
  simpa only [nb078_alpha_dummy_1182] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1174 h))).fv) 1

theorem nb078_distinct_399 (h : Var) :
    (nb078_alpha_dummy_1181 h) ≠ (nb078_alpha_dummy_1182 h) := by
  simpa only [nb078_alpha_dummy_1181, nb078_alpha_dummy_1182] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1174 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_400 :
    (nb078_alpha_dummy_1185) ∉
      (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1185] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_401 :
    (nb078_alpha_dummy_1186) ∉
      (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1186] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_402 :
    (nb078_alpha_dummy_1187) ∉
      (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1187] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_403 : (nb078_alpha_dummy_1185) ≠ (nb078_alpha_dummy_1186) := by
  simpa only [nb078_alpha_dummy_1185, nb078_alpha_dummy_1186] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part013`. -/


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

theorem nb078_distinct_404 : (nb078_alpha_dummy_1185) ≠ (nb078_alpha_dummy_1187) := by
  simpa only [nb078_alpha_dummy_1185, nb078_alpha_dummy_1187] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_405 : (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1187) := by
  simpa only [nb078_alpha_dummy_1186, nb078_alpha_dummy_1187] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_406 (h : Var) :
    (nb078_alpha_dummy_1188 h) ∉
      (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1188] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_407 (h : Var) :
    (nb078_alpha_dummy_1189 h) ∉
      (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1189] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_408 (h : Var) :
    (nb078_alpha_dummy_1190 h) ∉
      (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1190] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_409 (h : Var) :
    (nb078_alpha_dummy_1188 h) ≠ (nb078_alpha_dummy_1189 h) := by
  simpa only [nb078_alpha_dummy_1188, nb078_alpha_dummy_1189] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_410 (h : Var) :
    (nb078_alpha_dummy_1188 h) ≠ (nb078_alpha_dummy_1190 h) := by
  simpa only [nb078_alpha_dummy_1188, nb078_alpha_dummy_1190] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_411 (h : Var) :
    (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1190 h) := by
  simpa only [nb078_alpha_dummy_1189, nb078_alpha_dummy_1190] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_412 :
    (nb078_alpha_dummy_1197) ∉
      (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1186))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1197] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1186))).fv)
      0

theorem nb078_fresh_413 :
    (nb078_alpha_dummy_1193) ∉
      (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1193] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv)
      0

theorem nb078_fresh_414 :
    (nb078_alpha_dummy_1199) ∉
      (((Class.cv (nb078_alpha_dummy_1187))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1199] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1187))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv)
      0

theorem nb078_fresh_415 (h : Var) :
    (nb078_alpha_dummy_1198 h) ∉
      (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1189 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1198] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1189 h))).fv)
      0

theorem nb078_fresh_416 (h : Var) :
    (nb078_alpha_dummy_1194 h) ∉
      (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1190 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1194] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1190 h))).fv)
      0

theorem nb078_fresh_417 (h : Var) :
    (nb078_alpha_dummy_1200 h) ∉
      (((Class.cv (nb078_alpha_dummy_1190 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1190 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1200] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1190 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1190 h))).fv)
      0

theorem nb078_fresh_418 :
    (nb078_alpha_dummy_1215) ∉ (((Class.cv (nb078_alpha_dummy_1208))).fv) := by
  simpa only [nb078_alpha_dummy_1215] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1208))).fv) 0

theorem nb078_fresh_419 :
    (nb078_alpha_dummy_1216) ∉ (((Class.cv (nb078_alpha_dummy_1208))).fv) := by
  simpa only [nb078_alpha_dummy_1216] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1208))).fv) 1

theorem nb078_distinct_420 : (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1216) := by
  simpa only [nb078_alpha_dummy_1215, nb078_alpha_dummy_1216] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1208))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_421 (h : Var) :
    (nb078_alpha_dummy_1217 h) ∉ (((Class.cv (nb078_alpha_dummy_1210 h))).fv) := by
  simpa only [nb078_alpha_dummy_1217] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1210 h))).fv) 0

theorem nb078_fresh_422 (h : Var) :
    (nb078_alpha_dummy_1218 h) ∉ (((Class.cv (nb078_alpha_dummy_1210 h))).fv) := by
  simpa only [nb078_alpha_dummy_1218] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1210 h))).fv) 1

theorem nb078_distinct_423 (h : Var) :
    (nb078_alpha_dummy_1217 h) ≠ (nb078_alpha_dummy_1218 h) := by
  simpa only [nb078_alpha_dummy_1217, nb078_alpha_dummy_1218] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1210 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_424 :
    (nb078_alpha_dummy_1221) ∉
      (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1221] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_425 :
    (nb078_alpha_dummy_1222) ∉
      (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1222] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_426 :
    (nb078_alpha_dummy_1223) ∉
      (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1223] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_427 : (nb078_alpha_dummy_1221) ≠ (nb078_alpha_dummy_1222) := by
  simpa only [nb078_alpha_dummy_1221, nb078_alpha_dummy_1222] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_428 : (nb078_alpha_dummy_1221) ≠ (nb078_alpha_dummy_1223) := by
  simpa only [nb078_alpha_dummy_1221, nb078_alpha_dummy_1223] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_429 : (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1223) := by
  simpa only [nb078_alpha_dummy_1222, nb078_alpha_dummy_1223] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_430 (h : Var) :
    (nb078_alpha_dummy_1224 h) ∉
      (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1224] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_431 (h : Var) :
    (nb078_alpha_dummy_1225 h) ∉
      (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1225] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_432 (h : Var) :
    (nb078_alpha_dummy_1226 h) ∉
      (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1226] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_433 (h : Var) :
    (nb078_alpha_dummy_1224 h) ≠ (nb078_alpha_dummy_1225 h) := by
  simpa only [nb078_alpha_dummy_1224, nb078_alpha_dummy_1225] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_434 (h : Var) :
    (nb078_alpha_dummy_1224 h) ≠ (nb078_alpha_dummy_1226 h) := by
  simpa only [nb078_alpha_dummy_1224, nb078_alpha_dummy_1226] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_435 (h : Var) :
    (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1226 h) := by
  simpa only [nb078_alpha_dummy_1225, nb078_alpha_dummy_1226] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_436 :
    (nb078_alpha_dummy_1233) ∉
      (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1222))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1233] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1222))).fv)
      0

theorem nb078_fresh_437 :
    (nb078_alpha_dummy_1229) ∉
      (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1229] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv)
      0

theorem nb078_fresh_438 :
    (nb078_alpha_dummy_1235) ∉
      (((Class.cv (nb078_alpha_dummy_1223))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1235] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1223))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv)
      0

theorem nb078_fresh_439 (h : Var) :
    (nb078_alpha_dummy_1234 h) ∉
      (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1225 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1234] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1225 h))).fv)
      0

theorem nb078_fresh_440 (h : Var) :
    (nb078_alpha_dummy_1230 h) ∉
      (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1226 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1230] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1226 h))).fv)
      0

theorem nb078_fresh_441 (h : Var) :
    (nb078_alpha_dummy_1236 h) ∉
      (((Class.cv (nb078_alpha_dummy_1226 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1226 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1236] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1226 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1226 h))).fv)
      0

theorem nb078_fresh_442 :
    (nb078_alpha_dummy_139) ∉ (((Class.cv (nb078_alpha_dummy_132))).fv) := by
  simpa only [nb078_alpha_dummy_139] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_132))).fv) 0

theorem nb078_fresh_443 :
    (nb078_alpha_dummy_140) ∉ (((Class.cv (nb078_alpha_dummy_132))).fv) := by
  simpa only [nb078_alpha_dummy_140] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_132))).fv) 1

theorem nb078_distinct_444 : (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_140) := by
  simpa only [nb078_alpha_dummy_139, nb078_alpha_dummy_140] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_132))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_445 (f : Var) :
    (nb078_alpha_dummy_141 f) ∉ (((Class.cv (nb078_alpha_dummy_134 f))).fv) := by
  simpa only [nb078_alpha_dummy_141] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_134 f))).fv) 0

theorem nb078_fresh_446 (f : Var) :
    (nb078_alpha_dummy_142 f) ∉ (((Class.cv (nb078_alpha_dummy_134 f))).fv) := by
  simpa only [nb078_alpha_dummy_142] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_134 f))).fv) 1

theorem nb078_distinct_447 (f : Var) :
    (nb078_alpha_dummy_141 f) ≠ (nb078_alpha_dummy_142 f) := by
  simpa only [nb078_alpha_dummy_141, nb078_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_134 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_448 :
    (nb078_alpha_dummy_145) ∉
      (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_145] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_449 :
    (nb078_alpha_dummy_146) ∉
      (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_146] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_450 :
    (nb078_alpha_dummy_147) ∉
      (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_147] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_451 : (nb078_alpha_dummy_145) ≠ (nb078_alpha_dummy_146) := by
  simpa only [nb078_alpha_dummy_145, nb078_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_452 : (nb078_alpha_dummy_145) ≠ (nb078_alpha_dummy_147) := by
  simpa only [nb078_alpha_dummy_145, nb078_alpha_dummy_147] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_453 : (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_147) := by
  simpa only [nb078_alpha_dummy_146, nb078_alpha_dummy_147] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_454 (f : Var) :
    (nb078_alpha_dummy_148 f) ∉
      (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_148] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_455 (f : Var) :
    (nb078_alpha_dummy_149 f) ∉
      (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_149] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_456 (f : Var) :
    (nb078_alpha_dummy_150 f) ∉
      (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_150] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_457 (f : Var) :
    (nb078_alpha_dummy_148 f) ≠ (nb078_alpha_dummy_149 f) := by
  simpa only [nb078_alpha_dummy_148, nb078_alpha_dummy_149] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_458 (f : Var) :
    (nb078_alpha_dummy_148 f) ≠ (nb078_alpha_dummy_150 f) := by
  simpa only [nb078_alpha_dummy_148, nb078_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_459 (f : Var) :
    (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_150 f) := by
  simpa only [nb078_alpha_dummy_149, nb078_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_460 :
    (nb078_alpha_dummy_157) ∉
      (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_146))).fv) :=
  by
  simpa only [nb078_alpha_dummy_157] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_146))).fv)
      0

theorem nb078_fresh_461 :
    (nb078_alpha_dummy_153) ∉
      (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) :=
  by
  simpa only [nb078_alpha_dummy_153] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv)
      0

theorem nb078_fresh_462 :
    (nb078_alpha_dummy_159) ∉
      (((Class.cv (nb078_alpha_dummy_147))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) :=
  by
  simpa only [nb078_alpha_dummy_159] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_147))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv)
      0

theorem nb078_fresh_463 (f : Var) :
    (nb078_alpha_dummy_158 f) ∉
      (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_149 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_158] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_149 f))).fv)
      0

theorem nb078_fresh_464 (f : Var) :
    (nb078_alpha_dummy_154 f) ∉
      (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_154] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv)
      0

theorem nb078_fresh_465 (f : Var) :
    (nb078_alpha_dummy_160 f) ∉
      (((Class.cv (nb078_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_160] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv)
      0

theorem nb078_fresh_466 :
    (nb078_alpha_dummy_175) ∉ (((Class.cv (nb078_alpha_dummy_168))).fv) := by
  simpa only [nb078_alpha_dummy_175] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_168))).fv) 0

theorem nb078_fresh_467 :
    (nb078_alpha_dummy_176) ∉ (((Class.cv (nb078_alpha_dummy_168))).fv) := by
  simpa only [nb078_alpha_dummy_176] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_168))).fv) 1

theorem nb078_distinct_468 : (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_176) := by
  simpa only [nb078_alpha_dummy_175, nb078_alpha_dummy_176] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_168))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_469 (f : Var) :
    (nb078_alpha_dummy_177 f) ∉ (((Class.cv (nb078_alpha_dummy_170 f))).fv) := by
  simpa only [nb078_alpha_dummy_177] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_170 f))).fv) 0

theorem nb078_fresh_470 (f : Var) :
    (nb078_alpha_dummy_178 f) ∉ (((Class.cv (nb078_alpha_dummy_170 f))).fv) := by
  simpa only [nb078_alpha_dummy_178] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_170 f))).fv) 1

theorem nb078_distinct_471 (f : Var) :
    (nb078_alpha_dummy_177 f) ≠ (nb078_alpha_dummy_178 f) := by
  simpa only [nb078_alpha_dummy_177, nb078_alpha_dummy_178] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_170 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_472 :
    (nb078_alpha_dummy_181) ∉
      (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_181] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_473 :
    (nb078_alpha_dummy_182) ∉
      (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_182] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_474 :
    (nb078_alpha_dummy_183) ∉
      (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_183] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_475 : (nb078_alpha_dummy_181) ≠ (nb078_alpha_dummy_182) := by
  simpa only [nb078_alpha_dummy_181, nb078_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_476 : (nb078_alpha_dummy_181) ≠ (nb078_alpha_dummy_183) := by
  simpa only [nb078_alpha_dummy_181, nb078_alpha_dummy_183] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_477 : (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_183) := by
  simpa only [nb078_alpha_dummy_182, nb078_alpha_dummy_183] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_478 (f : Var) :
    (nb078_alpha_dummy_184 f) ∉
      (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_184] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_479 (f : Var) :
    (nb078_alpha_dummy_185 f) ∉
      (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_185] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_480 (f : Var) :
    (nb078_alpha_dummy_186 f) ∉
      (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_186] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_481 (f : Var) :
    (nb078_alpha_dummy_184 f) ≠ (nb078_alpha_dummy_185 f) := by
  simpa only [nb078_alpha_dummy_184, nb078_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_482 (f : Var) :
    (nb078_alpha_dummy_184 f) ≠ (nb078_alpha_dummy_186 f) := by
  simpa only [nb078_alpha_dummy_184, nb078_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_483 (f : Var) :
    (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_186 f) := by
  simpa only [nb078_alpha_dummy_185, nb078_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_484 :
    (nb078_alpha_dummy_193) ∉
      (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_182))).fv) :=
  by
  simpa only [nb078_alpha_dummy_193] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_182))).fv)
      0

theorem nb078_fresh_485 :
    (nb078_alpha_dummy_189) ∉
      (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) :=
  by
  simpa only [nb078_alpha_dummy_189] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv)
      0

theorem nb078_fresh_486 :
    (nb078_alpha_dummy_195) ∉
      (((Class.cv (nb078_alpha_dummy_183))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) :=
  by
  simpa only [nb078_alpha_dummy_195] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_183))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv)
      0

theorem nb078_fresh_487 (f : Var) :
    (nb078_alpha_dummy_194 f) ∉
      (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_185 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_194] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_185 f))).fv)
      0

theorem nb078_fresh_488 (f : Var) :
    (nb078_alpha_dummy_190 f) ∉
      (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_190] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv)
      0

theorem nb078_fresh_489 (f : Var) :
    (nb078_alpha_dummy_196 f) ∉
      (((Class.cv (nb078_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_196] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv)
      0

theorem nb078_fresh_490 :
    (nb078_alpha_dummy_207) ∉
      (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) :=
  by
  simpa only [nb078_alpha_dummy_207] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv)
      0

theorem nb078_fresh_491 :
    (nb078_alpha_dummy_208) ∉
      (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) :=
  by
  simpa only [nb078_alpha_dummy_208] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv)
      1

theorem nb078_distinct_492 : (nb078_alpha_dummy_207) ≠ (nb078_alpha_dummy_208) := by
  simpa only [nb078_alpha_dummy_207, nb078_alpha_dummy_208] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_493 (f : Var) :
    (nb078_alpha_dummy_209 f) ∉
      (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_209] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv)
      0

theorem nb078_fresh_494 (f : Var) :
    (nb078_alpha_dummy_210 f) ∉
      (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_210] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv)
      1

theorem nb078_distinct_495 (f : Var) :
    (nb078_alpha_dummy_209 f) ≠ (nb078_alpha_dummy_210 f) := by
  simpa only [nb078_alpha_dummy_209, nb078_alpha_dummy_210] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪
        ((Class.cv (nb078_alpha_dummy_205 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_496 :
    (nb078_alpha_dummy_215) ∉ (((Class.cv (nb078_alpha_dummy_208))).fv) := by
  simpa only [nb078_alpha_dummy_215] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_208))).fv) 0

theorem nb078_fresh_497 :
    (nb078_alpha_dummy_216) ∉ (((Class.cv (nb078_alpha_dummy_208))).fv) := by
  simpa only [nb078_alpha_dummy_216] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_208))).fv) 1

theorem nb078_distinct_498 : (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_216) := by
  simpa only [nb078_alpha_dummy_215, nb078_alpha_dummy_216] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_208))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_499 (f : Var) :
    (nb078_alpha_dummy_217 f) ∉ (((Class.cv (nb078_alpha_dummy_210 f))).fv) := by
  simpa only [nb078_alpha_dummy_217] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_210 f))).fv) 0

theorem nb078_fresh_500 (f : Var) :
    (nb078_alpha_dummy_218 f) ∉ (((Class.cv (nb078_alpha_dummy_210 f))).fv) := by
  simpa only [nb078_alpha_dummy_218] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_210 f))).fv) 1

theorem nb078_distinct_501 (f : Var) :
    (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_218 f) := by
  simpa only [nb078_alpha_dummy_217, nb078_alpha_dummy_218] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_210 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_502 :
    (nb078_alpha_dummy_221) ∉
      (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_221] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_503 :
    (nb078_alpha_dummy_222) ∉
      (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_222] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_504 :
    (nb078_alpha_dummy_223) ∉
      (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_223] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_505 : (nb078_alpha_dummy_221) ≠ (nb078_alpha_dummy_222) := by
  simpa only [nb078_alpha_dummy_221, nb078_alpha_dummy_222] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_506 : (nb078_alpha_dummy_221) ≠ (nb078_alpha_dummy_223) := by
  simpa only [nb078_alpha_dummy_221, nb078_alpha_dummy_223] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_507 : (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_223) := by
  simpa only [nb078_alpha_dummy_222, nb078_alpha_dummy_223] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_508 (f : Var) :
    (nb078_alpha_dummy_224 f) ∉
      (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_224] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_509 (f : Var) :
    (nb078_alpha_dummy_225 f) ∉
      (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_225] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_510 (f : Var) :
    (nb078_alpha_dummy_226 f) ∉
      (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_226] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_511 (f : Var) :
    (nb078_alpha_dummy_224 f) ≠ (nb078_alpha_dummy_225 f) := by
  simpa only [nb078_alpha_dummy_224, nb078_alpha_dummy_225] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_512 (f : Var) :
    (nb078_alpha_dummy_224 f) ≠ (nb078_alpha_dummy_226 f) := by
  simpa only [nb078_alpha_dummy_224, nb078_alpha_dummy_226] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_513 (f : Var) :
    (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_226 f) := by
  simpa only [nb078_alpha_dummy_225, nb078_alpha_dummy_226] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_514 :
    (nb078_alpha_dummy_233) ∉
      (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_222))).fv) :=
  by
  simpa only [nb078_alpha_dummy_233] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_222))).fv)
      0

theorem nb078_fresh_515 :
    (nb078_alpha_dummy_229) ∉
      (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) :=
  by
  simpa only [nb078_alpha_dummy_229] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv)
      0

theorem nb078_fresh_516 :
    (nb078_alpha_dummy_235) ∉
      (((Class.cv (nb078_alpha_dummy_223))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) :=
  by
  simpa only [nb078_alpha_dummy_235] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_223))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv)
      0

theorem nb078_fresh_517 (f : Var) :
    (nb078_alpha_dummy_234 f) ∉
      (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_225 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_234] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_225 f))).fv)
      0

theorem nb078_fresh_518 (f : Var) :
    (nb078_alpha_dummy_230 f) ∉
      (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_230] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv)
      0

theorem nb078_fresh_519 (f : Var) :
    (nb078_alpha_dummy_236 f) ∉
      (((Class.cv (nb078_alpha_dummy_226 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_236] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_226 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv)
      0

theorem nb078_fresh_520 :
    (nb078_alpha_dummy_247) ∉
      (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) :=
  by
  simpa only [nb078_alpha_dummy_247] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv)
      0

theorem nb078_fresh_521 :
    (nb078_alpha_dummy_248) ∉
      (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) :=
  by
  simpa only [nb078_alpha_dummy_248] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv)
      1

theorem nb078_distinct_522 : (nb078_alpha_dummy_247) ≠ (nb078_alpha_dummy_248) := by
  simpa only [nb078_alpha_dummy_247, nb078_alpha_dummy_248] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_523 (f : Var) :
    (nb078_alpha_dummy_249 f) ∉
      (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_249] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv)
      0

theorem nb078_fresh_524 (f : Var) :
    (nb078_alpha_dummy_250 f) ∉
      (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_250] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv)
      1

theorem nb078_distinct_525 (f : Var) :
    (nb078_alpha_dummy_249 f) ≠ (nb078_alpha_dummy_250 f) := by
  simpa only [nb078_alpha_dummy_249, nb078_alpha_dummy_250] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪
        ((Class.cv (nb078_alpha_dummy_245 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_526 :
    (nb078_alpha_dummy_255) ∉ (((Class.cv (nb078_alpha_dummy_248))).fv) := by
  simpa only [nb078_alpha_dummy_255] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_248))).fv) 0

theorem nb078_fresh_527 :
    (nb078_alpha_dummy_256) ∉ (((Class.cv (nb078_alpha_dummy_248))).fv) := by
  simpa only [nb078_alpha_dummy_256] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_248))).fv) 1

theorem nb078_distinct_528 : (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_256) := by
  simpa only [nb078_alpha_dummy_255, nb078_alpha_dummy_256] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_248))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_529 (f : Var) :
    (nb078_alpha_dummy_257 f) ∉ (((Class.cv (nb078_alpha_dummy_250 f))).fv) := by
  simpa only [nb078_alpha_dummy_257] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_250 f))).fv) 0

theorem nb078_fresh_530 (f : Var) :
    (nb078_alpha_dummy_258 f) ∉ (((Class.cv (nb078_alpha_dummy_250 f))).fv) := by
  simpa only [nb078_alpha_dummy_258] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_250 f))).fv) 1

theorem nb078_distinct_531 (f : Var) :
    (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_258 f) := by
  simpa only [nb078_alpha_dummy_257, nb078_alpha_dummy_258] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_250 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_532 :
    (nb078_alpha_dummy_261) ∉
      (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_261] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_533 :
    (nb078_alpha_dummy_262) ∉
      (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_262] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_534 :
    (nb078_alpha_dummy_263) ∉
      (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_263] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_535 : (nb078_alpha_dummy_261) ≠ (nb078_alpha_dummy_262) := by
  simpa only [nb078_alpha_dummy_261, nb078_alpha_dummy_262] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_536 : (nb078_alpha_dummy_261) ≠ (nb078_alpha_dummy_263) := by
  simpa only [nb078_alpha_dummy_261, nb078_alpha_dummy_263] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_537 : (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_263) := by
  simpa only [nb078_alpha_dummy_262, nb078_alpha_dummy_263] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_538 (f : Var) :
    (nb078_alpha_dummy_264 f) ∉
      (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_264] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_539 (f : Var) :
    (nb078_alpha_dummy_265 f) ∉
      (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_265] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_540 (f : Var) :
    (nb078_alpha_dummy_266 f) ∉
      (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_266] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_541 (f : Var) :
    (nb078_alpha_dummy_264 f) ≠ (nb078_alpha_dummy_265 f) := by
  simpa only [nb078_alpha_dummy_264, nb078_alpha_dummy_265] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_542 (f : Var) :
    (nb078_alpha_dummy_264 f) ≠ (nb078_alpha_dummy_266 f) := by
  simpa only [nb078_alpha_dummy_264, nb078_alpha_dummy_266] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_543 (f : Var) :
    (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_266 f) := by
  simpa only [nb078_alpha_dummy_265, nb078_alpha_dummy_266] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_544 :
    (nb078_alpha_dummy_273) ∉
      (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_262))).fv) :=
  by
  simpa only [nb078_alpha_dummy_273] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_262))).fv)
      0

theorem nb078_fresh_545 :
    (nb078_alpha_dummy_269) ∉
      (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) :=
  by
  simpa only [nb078_alpha_dummy_269] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv)
      0

theorem nb078_fresh_546 :
    (nb078_alpha_dummy_275) ∉
      (((Class.cv (nb078_alpha_dummy_263))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) :=
  by
  simpa only [nb078_alpha_dummy_275] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_263))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv)
      0

theorem nb078_fresh_547 (f : Var) :
    (nb078_alpha_dummy_274 f) ∉
      (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_265 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_274] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_265 f))).fv)
      0

theorem nb078_fresh_548 (f : Var) :
    (nb078_alpha_dummy_270 f) ∉
      (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_270] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv)
      0

theorem nb078_fresh_549 (f : Var) :
    (nb078_alpha_dummy_276 f) ∉
      (((Class.cv (nb078_alpha_dummy_266 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_276] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_266 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv)
      0

theorem nb078_fresh_550 :
    (nb078_alpha_dummy_295) ∉
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) :=
  by
  simpa only [nb078_alpha_dummy_295] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv)
      0

theorem nb078_fresh_551 :
    (nb078_alpha_dummy_296) ∉
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) :=
  by
  simpa only [nb078_alpha_dummy_296] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv)
      1

theorem nb078_distinct_552 : (nb078_alpha_dummy_295) ≠ (nb078_alpha_dummy_296) := by
  simpa only [nb078_alpha_dummy_295, nb078_alpha_dummy_296] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_553 :
    (nb078_alpha_dummy_331) ∉
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) :=
  by
  simpa only [nb078_alpha_dummy_331] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part014`. -/


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

theorem nb078_fresh_554 :
    (nb078_alpha_dummy_332) ∉
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) :=
  by
  simpa only [nb078_alpha_dummy_332] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv)
      1

theorem nb078_distinct_555 : (nb078_alpha_dummy_331) ≠ (nb078_alpha_dummy_332) := by
  simpa only [nb078_alpha_dummy_331, nb078_alpha_dummy_332] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_556 :
    (nb078_alpha_dummy_445) ∉
      (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) :=
  by
  simpa only [nb078_alpha_dummy_445] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv)
      0

theorem nb078_fresh_557 :
    (nb078_alpha_dummy_446) ∉
      (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) :=
  by
  simpa only [nb078_alpha_dummy_446] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv)
      1

theorem nb078_distinct_558 : (nb078_alpha_dummy_445) ≠ (nb078_alpha_dummy_446) := by
  simpa only [nb078_alpha_dummy_445, nb078_alpha_dummy_446] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_559 (g : Var) :
    (nb078_alpha_dummy_297 g) ∉
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_297] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv)
      0

theorem nb078_fresh_560 (g : Var) :
    (nb078_alpha_dummy_298 g) ∉
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_298] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv)
      1

theorem nb078_distinct_561 (g : Var) :
    (nb078_alpha_dummy_297 g) ≠ (nb078_alpha_dummy_298 g) := by
  simpa only [nb078_alpha_dummy_297, nb078_alpha_dummy_298] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_291 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_562 (g : Var) :
    (nb078_alpha_dummy_333 g) ∉
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_333] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv)
      0

theorem nb078_fresh_563 (g : Var) :
    (nb078_alpha_dummy_334 g) ∉
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_334] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv)
      1

theorem nb078_distinct_564 (g : Var) :
    (nb078_alpha_dummy_333 g) ≠ (nb078_alpha_dummy_334 g) := by
  simpa only [nb078_alpha_dummy_333, nb078_alpha_dummy_334] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_292 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_565 (g : Var) :
    (nb078_alpha_dummy_447 g) ∉
      (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_447] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv)
      0

theorem nb078_fresh_566 (g : Var) :
    (nb078_alpha_dummy_448 g) ∉
      (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_448] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv)
      1

theorem nb078_distinct_567 (g : Var) :
    (nb078_alpha_dummy_447 g) ≠ (nb078_alpha_dummy_448 g) := by
  simpa only [nb078_alpha_dummy_447, nb078_alpha_dummy_448] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_291 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_568 :
    (nb078_alpha_dummy_303) ∉ (((Class.cv (nb078_alpha_dummy_296))).fv) := by
  simpa only [nb078_alpha_dummy_303] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_296))).fv) 0

theorem nb078_fresh_569 :
    (nb078_alpha_dummy_304) ∉ (((Class.cv (nb078_alpha_dummy_296))).fv) := by
  simpa only [nb078_alpha_dummy_304] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_296))).fv) 1

theorem nb078_distinct_570 : (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_304) := by
  simpa only [nb078_alpha_dummy_303, nb078_alpha_dummy_304] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_296))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_571 (g : Var) :
    (nb078_alpha_dummy_305 g) ∉ (((Class.cv (nb078_alpha_dummy_298 g))).fv) := by
  simpa only [nb078_alpha_dummy_305] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_298 g))).fv) 0

theorem nb078_fresh_572 (g : Var) :
    (nb078_alpha_dummy_306 g) ∉ (((Class.cv (nb078_alpha_dummy_298 g))).fv) := by
  simpa only [nb078_alpha_dummy_306] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_298 g))).fv) 1

theorem nb078_distinct_573 (g : Var) :
    (nb078_alpha_dummy_305 g) ≠ (nb078_alpha_dummy_306 g) := by
  simpa only [nb078_alpha_dummy_305, nb078_alpha_dummy_306] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_298 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_574 :
    (nb078_alpha_dummy_309) ∉
      (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_309] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_575 :
    (nb078_alpha_dummy_310) ∉
      (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_310] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_576 :
    (nb078_alpha_dummy_311) ∉
      (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_311] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_577 : (nb078_alpha_dummy_309) ≠ (nb078_alpha_dummy_310) := by
  simpa only [nb078_alpha_dummy_309, nb078_alpha_dummy_310] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_578 : (nb078_alpha_dummy_309) ≠ (nb078_alpha_dummy_311) := by
  simpa only [nb078_alpha_dummy_309, nb078_alpha_dummy_311] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_579 : (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_311) := by
  simpa only [nb078_alpha_dummy_310, nb078_alpha_dummy_311] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_580 (g : Var) :
    (nb078_alpha_dummy_312 g) ∉
      (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_312] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_581 (g : Var) :
    (nb078_alpha_dummy_313 g) ∉
      (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_313] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_582 (g : Var) :
    (nb078_alpha_dummy_314 g) ∉
      (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_314] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_583 (g : Var) :
    (nb078_alpha_dummy_312 g) ≠ (nb078_alpha_dummy_313 g) := by
  simpa only [nb078_alpha_dummy_312, nb078_alpha_dummy_313] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_584 (g : Var) :
    (nb078_alpha_dummy_312 g) ≠ (nb078_alpha_dummy_314 g) := by
  simpa only [nb078_alpha_dummy_312, nb078_alpha_dummy_314] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_585 (g : Var) :
    (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_314 g) := by
  simpa only [nb078_alpha_dummy_313, nb078_alpha_dummy_314] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_586 :
    (nb078_alpha_dummy_321) ∉
      (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_310))).fv) :=
  by
  simpa only [nb078_alpha_dummy_321] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_310))).fv)
      0

theorem nb078_fresh_587 :
    (nb078_alpha_dummy_317) ∉
      (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) :=
  by
  simpa only [nb078_alpha_dummy_317] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv)
      0

theorem nb078_fresh_588 :
    (nb078_alpha_dummy_323) ∉
      (((Class.cv (nb078_alpha_dummy_311))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) :=
  by
  simpa only [nb078_alpha_dummy_323] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_311))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv)
      0

theorem nb078_fresh_589 (g : Var) :
    (nb078_alpha_dummy_322 g) ∉
      (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_313 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_322] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_313 g))).fv)
      0

theorem nb078_fresh_590 (g : Var) :
    (nb078_alpha_dummy_318 g) ∉
      (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_318] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv)
      0

theorem nb078_fresh_591 (g : Var) :
    (nb078_alpha_dummy_324 g) ∉
      (((Class.cv (nb078_alpha_dummy_314 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_324] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_314 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv)
      0

theorem nb078_fresh_592 :
    (nb078_alpha_dummy_339) ∉ (((Class.cv (nb078_alpha_dummy_332))).fv) := by
  simpa only [nb078_alpha_dummy_339] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_332))).fv) 0

theorem nb078_fresh_593 :
    (nb078_alpha_dummy_340) ∉ (((Class.cv (nb078_alpha_dummy_332))).fv) := by
  simpa only [nb078_alpha_dummy_340] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_332))).fv) 1

theorem nb078_distinct_594 : (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_340) := by
  simpa only [nb078_alpha_dummy_339, nb078_alpha_dummy_340] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_332))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_595 (g : Var) :
    (nb078_alpha_dummy_341 g) ∉ (((Class.cv (nb078_alpha_dummy_334 g))).fv) := by
  simpa only [nb078_alpha_dummy_341] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_334 g))).fv) 0

theorem nb078_fresh_596 (g : Var) :
    (nb078_alpha_dummy_342 g) ∉ (((Class.cv (nb078_alpha_dummy_334 g))).fv) := by
  simpa only [nb078_alpha_dummy_342] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_334 g))).fv) 1

theorem nb078_distinct_597 (g : Var) :
    (nb078_alpha_dummy_341 g) ≠ (nb078_alpha_dummy_342 g) := by
  simpa only [nb078_alpha_dummy_341, nb078_alpha_dummy_342] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_334 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_598 :
    (nb078_alpha_dummy_345) ∉
      (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_345] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_599 :
    (nb078_alpha_dummy_346) ∉
      (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_346] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_600 :
    (nb078_alpha_dummy_347) ∉
      (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_347] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_601 : (nb078_alpha_dummy_345) ≠ (nb078_alpha_dummy_346) := by
  simpa only [nb078_alpha_dummy_345, nb078_alpha_dummy_346] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_602 : (nb078_alpha_dummy_345) ≠ (nb078_alpha_dummy_347) := by
  simpa only [nb078_alpha_dummy_345, nb078_alpha_dummy_347] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_603 : (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_347) := by
  simpa only [nb078_alpha_dummy_346, nb078_alpha_dummy_347] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_604 (g : Var) :
    (nb078_alpha_dummy_348 g) ∉
      (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_348] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_605 (g : Var) :
    (nb078_alpha_dummy_349 g) ∉
      (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_349] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_606 (g : Var) :
    (nb078_alpha_dummy_350 g) ∉
      (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_350] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_607 (g : Var) :
    (nb078_alpha_dummy_348 g) ≠ (nb078_alpha_dummy_349 g) := by
  simpa only [nb078_alpha_dummy_348, nb078_alpha_dummy_349] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_608 (g : Var) :
    (nb078_alpha_dummy_348 g) ≠ (nb078_alpha_dummy_350 g) := by
  simpa only [nb078_alpha_dummy_348, nb078_alpha_dummy_350] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_609 (g : Var) :
    (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_350 g) := by
  simpa only [nb078_alpha_dummy_349, nb078_alpha_dummy_350] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_610 :
    (nb078_alpha_dummy_357) ∉
      (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_346))).fv) :=
  by
  simpa only [nb078_alpha_dummy_357] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_346))).fv)
      0

theorem nb078_fresh_611 :
    (nb078_alpha_dummy_353) ∉
      (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) :=
  by
  simpa only [nb078_alpha_dummy_353] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv)
      0

theorem nb078_fresh_612 :
    (nb078_alpha_dummy_359) ∉
      (((Class.cv (nb078_alpha_dummy_347))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) :=
  by
  simpa only [nb078_alpha_dummy_359] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_347))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv)
      0

theorem nb078_fresh_613 (g : Var) :
    (nb078_alpha_dummy_358 g) ∉
      (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_349 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_358] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_349 g))).fv)
      0

theorem nb078_fresh_614 (g : Var) :
    (nb078_alpha_dummy_354 g) ∉
      (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_354] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv)
      0

theorem nb078_fresh_615 (g : Var) :
    (nb078_alpha_dummy_360 g) ∉
      (((Class.cv (nb078_alpha_dummy_350 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_360] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_350 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv)
      0

theorem nb078_fresh_616 :
    (nb078_alpha_dummy_373) ∉
      (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) :=
  by
  simpa only [nb078_alpha_dummy_373] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv)
      0

theorem nb078_fresh_617 :
    (nb078_alpha_dummy_374) ∉
      (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) :=
  by
  simpa only [nb078_alpha_dummy_374] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv)
      1

theorem nb078_distinct_618 : (nb078_alpha_dummy_373) ≠ (nb078_alpha_dummy_374) := by
  simpa only [nb078_alpha_dummy_373, nb078_alpha_dummy_374] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_619 :
    (nb078_alpha_dummy_409) ∉
      (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) :=
  by
  simpa only [nb078_alpha_dummy_409] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv)
      0

theorem nb078_fresh_620 :
    (nb078_alpha_dummy_410) ∉
      (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) :=
  by
  simpa only [nb078_alpha_dummy_410] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv)
      1

theorem nb078_distinct_621 : (nb078_alpha_dummy_409) ≠ (nb078_alpha_dummy_410) := by
  simpa only [nb078_alpha_dummy_409, nb078_alpha_dummy_410] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_622 (g : Var) :
    (nb078_alpha_dummy_375 g) ∉
      (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_375] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv)
      0

theorem nb078_fresh_623 (g : Var) :
    (nb078_alpha_dummy_376 g) ∉
      (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_376] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv)
      1

theorem nb078_distinct_624 (g : Var) :
    (nb078_alpha_dummy_375 g) ≠ (nb078_alpha_dummy_376 g) := by
  simpa only [nb078_alpha_dummy_375, nb078_alpha_dummy_376] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_370 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_625 (g : Var) :
    (nb078_alpha_dummy_411 g) ∉
      (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_411] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv)
      0

theorem nb078_fresh_626 (g : Var) :
    (nb078_alpha_dummy_412 g) ∉
      (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_412] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv)
      1

theorem nb078_distinct_627 (g : Var) :
    (nb078_alpha_dummy_411 g) ≠ (nb078_alpha_dummy_412 g) := by
  simpa only [nb078_alpha_dummy_411, nb078_alpha_dummy_412] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_369 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_628 :
    (nb078_alpha_dummy_381) ∉ (((Class.cv (nb078_alpha_dummy_374))).fv) := by
  simpa only [nb078_alpha_dummy_381] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_374))).fv) 0

theorem nb078_fresh_629 :
    (nb078_alpha_dummy_382) ∉ (((Class.cv (nb078_alpha_dummy_374))).fv) := by
  simpa only [nb078_alpha_dummy_382] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_374))).fv) 1

theorem nb078_distinct_630 : (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_382) := by
  simpa only [nb078_alpha_dummy_381, nb078_alpha_dummy_382] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_631 (g : Var) :
    (nb078_alpha_dummy_383 g) ∉ (((Class.cv (nb078_alpha_dummy_376 g))).fv) := by
  simpa only [nb078_alpha_dummy_383] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_376 g))).fv) 0

theorem nb078_fresh_632 (g : Var) :
    (nb078_alpha_dummy_384 g) ∉ (((Class.cv (nb078_alpha_dummy_376 g))).fv) := by
  simpa only [nb078_alpha_dummy_384] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_376 g))).fv) 1

theorem nb078_distinct_633 (g : Var) :
    (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_384 g) := by
  simpa only [nb078_alpha_dummy_383, nb078_alpha_dummy_384] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_376 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_634 :
    (nb078_alpha_dummy_387) ∉
      (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_387] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_635 :
    (nb078_alpha_dummy_388) ∉
      (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_388] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_636 :
    (nb078_alpha_dummy_389) ∉
      (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_389] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_637 : (nb078_alpha_dummy_387) ≠ (nb078_alpha_dummy_388) := by
  simpa only [nb078_alpha_dummy_387, nb078_alpha_dummy_388] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_638 : (nb078_alpha_dummy_387) ≠ (nb078_alpha_dummy_389) := by
  simpa only [nb078_alpha_dummy_387, nb078_alpha_dummy_389] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_639 : (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_389) := by
  simpa only [nb078_alpha_dummy_388, nb078_alpha_dummy_389] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_640 (g : Var) :
    (nb078_alpha_dummy_390 g) ∉
      (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_390] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_641 (g : Var) :
    (nb078_alpha_dummy_391 g) ∉
      (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_391] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_642 (g : Var) :
    (nb078_alpha_dummy_392 g) ∉
      (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_392] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_643 (g : Var) :
    (nb078_alpha_dummy_390 g) ≠ (nb078_alpha_dummy_391 g) := by
  simpa only [nb078_alpha_dummy_390, nb078_alpha_dummy_391] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_644 (g : Var) :
    (nb078_alpha_dummy_390 g) ≠ (nb078_alpha_dummy_392 g) := by
  simpa only [nb078_alpha_dummy_390, nb078_alpha_dummy_392] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_645 (g : Var) :
    (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_392 g) := by
  simpa only [nb078_alpha_dummy_391, nb078_alpha_dummy_392] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_646 :
    (nb078_alpha_dummy_399) ∉
      (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_388))).fv) :=
  by
  simpa only [nb078_alpha_dummy_399] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_388))).fv)
      0

theorem nb078_fresh_647 :
    (nb078_alpha_dummy_395) ∉
      (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) :=
  by
  simpa only [nb078_alpha_dummy_395] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv)
      0

theorem nb078_fresh_648 :
    (nb078_alpha_dummy_401) ∉
      (((Class.cv (nb078_alpha_dummy_389))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) :=
  by
  simpa only [nb078_alpha_dummy_401] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_389))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv)
      0

theorem nb078_fresh_649 (g : Var) :
    (nb078_alpha_dummy_400 g) ∉
      (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_391 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_400] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_391 g))).fv)
      0

theorem nb078_fresh_650 (g : Var) :
    (nb078_alpha_dummy_396 g) ∉
      (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_396] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv)
      0

theorem nb078_fresh_651 (g : Var) :
    (nb078_alpha_dummy_402 g) ∉
      (((Class.cv (nb078_alpha_dummy_392 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_402] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_392 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv)
      0

theorem nb078_fresh_652 :
    (nb078_alpha_dummy_417) ∉ (((Class.cv (nb078_alpha_dummy_410))).fv) := by
  simpa only [nb078_alpha_dummy_417] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_410))).fv) 0

theorem nb078_fresh_653 :
    (nb078_alpha_dummy_418) ∉ (((Class.cv (nb078_alpha_dummy_410))).fv) := by
  simpa only [nb078_alpha_dummy_418] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_410))).fv) 1

theorem nb078_distinct_654 : (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_418) := by
  simpa only [nb078_alpha_dummy_417, nb078_alpha_dummy_418] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_410))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_655 (g : Var) :
    (nb078_alpha_dummy_419 g) ∉ (((Class.cv (nb078_alpha_dummy_412 g))).fv) := by
  simpa only [nb078_alpha_dummy_419] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_412 g))).fv) 0

theorem nb078_fresh_656 (g : Var) :
    (nb078_alpha_dummy_420 g) ∉ (((Class.cv (nb078_alpha_dummy_412 g))).fv) := by
  simpa only [nb078_alpha_dummy_420] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_412 g))).fv) 1

theorem nb078_distinct_657 (g : Var) :
    (nb078_alpha_dummy_419 g) ≠ (nb078_alpha_dummy_420 g) := by
  simpa only [nb078_alpha_dummy_419, nb078_alpha_dummy_420] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_412 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_658 :
    (nb078_alpha_dummy_423) ∉
      (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_423] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_659 :
    (nb078_alpha_dummy_424) ∉
      (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_424] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_660 :
    (nb078_alpha_dummy_425) ∉
      (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_425] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_661 : (nb078_alpha_dummy_423) ≠ (nb078_alpha_dummy_424) := by
  simpa only [nb078_alpha_dummy_423, nb078_alpha_dummy_424] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_662 : (nb078_alpha_dummy_423) ≠ (nb078_alpha_dummy_425) := by
  simpa only [nb078_alpha_dummy_423, nb078_alpha_dummy_425] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_663 : (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_425) := by
  simpa only [nb078_alpha_dummy_424, nb078_alpha_dummy_425] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_664 (g : Var) :
    (nb078_alpha_dummy_426 g) ∉
      (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_426] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_665 (g : Var) :
    (nb078_alpha_dummy_427 g) ∉
      (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_427] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_666 (g : Var) :
    (nb078_alpha_dummy_428 g) ∉
      (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_428] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_667 (g : Var) :
    (nb078_alpha_dummy_426 g) ≠ (nb078_alpha_dummy_427 g) := by
  simpa only [nb078_alpha_dummy_426, nb078_alpha_dummy_427] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_668 (g : Var) :
    (nb078_alpha_dummy_426 g) ≠ (nb078_alpha_dummy_428 g) := by
  simpa only [nb078_alpha_dummy_426, nb078_alpha_dummy_428] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_669 (g : Var) :
    (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_428 g) := by
  simpa only [nb078_alpha_dummy_427, nb078_alpha_dummy_428] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_670 :
    (nb078_alpha_dummy_435) ∉
      (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_424))).fv) :=
  by
  simpa only [nb078_alpha_dummy_435] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_424))).fv)
      0

theorem nb078_fresh_671 :
    (nb078_alpha_dummy_431) ∉
      (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) :=
  by
  simpa only [nb078_alpha_dummy_431] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv)
      0

theorem nb078_fresh_672 :
    (nb078_alpha_dummy_437) ∉
      (((Class.cv (nb078_alpha_dummy_425))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) :=
  by
  simpa only [nb078_alpha_dummy_437] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_425))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv)
      0

theorem nb078_fresh_673 (g : Var) :
    (nb078_alpha_dummy_436 g) ∉
      (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_427 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_436] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_427 g))).fv)
      0

theorem nb078_fresh_674 (g : Var) :
    (nb078_alpha_dummy_432 g) ∉
      (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_432] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv)
      0

theorem nb078_fresh_675 (g : Var) :
    (nb078_alpha_dummy_438 g) ∉
      (((Class.cv (nb078_alpha_dummy_428 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_438] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_428 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv)
      0

theorem nb078_fresh_676 :
    (nb078_alpha_dummy_453) ∉ (((Class.cv (nb078_alpha_dummy_446))).fv) := by
  simpa only [nb078_alpha_dummy_453] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_446))).fv) 0

theorem nb078_fresh_677 :
    (nb078_alpha_dummy_454) ∉ (((Class.cv (nb078_alpha_dummy_446))).fv) := by
  simpa only [nb078_alpha_dummy_454] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_446))).fv) 1

theorem nb078_distinct_678 : (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_454) := by
  simpa only [nb078_alpha_dummy_453, nb078_alpha_dummy_454] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_446))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_679 (g : Var) :
    (nb078_alpha_dummy_455 g) ∉ (((Class.cv (nb078_alpha_dummy_448 g))).fv) := by
  simpa only [nb078_alpha_dummy_455] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_448 g))).fv) 0

theorem nb078_fresh_680 (g : Var) :
    (nb078_alpha_dummy_456 g) ∉ (((Class.cv (nb078_alpha_dummy_448 g))).fv) := by
  simpa only [nb078_alpha_dummy_456] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_448 g))).fv) 1

theorem nb078_distinct_681 (g : Var) :
    (nb078_alpha_dummy_455 g) ≠ (nb078_alpha_dummy_456 g) := by
  simpa only [nb078_alpha_dummy_455, nb078_alpha_dummy_456] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_448 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_682 :
    (nb078_alpha_dummy_459) ∉
      (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_459] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_683 :
    (nb078_alpha_dummy_460) ∉
      (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_460] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_684 :
    (nb078_alpha_dummy_461) ∉
      (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_461] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_685 : (nb078_alpha_dummy_459) ≠ (nb078_alpha_dummy_460) := by
  simpa only [nb078_alpha_dummy_459, nb078_alpha_dummy_460] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_686 : (nb078_alpha_dummy_459) ≠ (nb078_alpha_dummy_461) := by
  simpa only [nb078_alpha_dummy_459, nb078_alpha_dummy_461] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_687 : (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_461) := by
  simpa only [nb078_alpha_dummy_460, nb078_alpha_dummy_461] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_688 (g : Var) :
    (nb078_alpha_dummy_462 g) ∉
      (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_462] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_689 (g : Var) :
    (nb078_alpha_dummy_463 g) ∉
      (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_463] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_690 (g : Var) :
    (nb078_alpha_dummy_464 g) ∉
      (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_464] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_691 (g : Var) :
    (nb078_alpha_dummy_462 g) ≠ (nb078_alpha_dummy_463 g) := by
  simpa only [nb078_alpha_dummy_462, nb078_alpha_dummy_463] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_692 (g : Var) :
    (nb078_alpha_dummy_462 g) ≠ (nb078_alpha_dummy_464 g) := by
  simpa only [nb078_alpha_dummy_462, nb078_alpha_dummy_464] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_693 (g : Var) :
    (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_464 g) := by
  simpa only [nb078_alpha_dummy_463, nb078_alpha_dummy_464] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_694 :
    (nb078_alpha_dummy_471) ∉
      (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_460))).fv) :=
  by
  simpa only [nb078_alpha_dummy_471] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_460))).fv)
      0

theorem nb078_fresh_695 :
    (nb078_alpha_dummy_467) ∉
      (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) :=
  by
  simpa only [nb078_alpha_dummy_467] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv)
      0

theorem nb078_fresh_696 :
    (nb078_alpha_dummy_473) ∉
      (((Class.cv (nb078_alpha_dummy_461))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) :=
  by
  simpa only [nb078_alpha_dummy_473] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_461))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv)
      0

theorem nb078_fresh_697 (g : Var) :
    (nb078_alpha_dummy_472 g) ∉
      (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_463 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_472] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_463 g))).fv)
      0

theorem nb078_fresh_698 (g : Var) :
    (nb078_alpha_dummy_468 g) ∉
      (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_468] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv)
      0

theorem nb078_fresh_699 (g : Var) :
    (nb078_alpha_dummy_474 g) ∉
      (((Class.cv (nb078_alpha_dummy_464 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_474] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_464 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv)
      0

theorem nb078_fresh_700 :
    (nb078_alpha_dummy_485) ∉
      (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) :=
  by
  simpa only [nb078_alpha_dummy_485] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv)
      0

theorem nb078_fresh_701 :
    (nb078_alpha_dummy_486) ∉
      (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) :=
  by
  simpa only [nb078_alpha_dummy_486] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv)
      1

theorem nb078_distinct_702 : (nb078_alpha_dummy_485) ≠ (nb078_alpha_dummy_486) := by
  simpa only [nb078_alpha_dummy_485, nb078_alpha_dummy_486] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_703 (g : Var) :
    (nb078_alpha_dummy_487 g) ∉
      (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_487] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part015`. -/


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

theorem nb078_fresh_704 (g : Var) :
    (nb078_alpha_dummy_488 g) ∉
      (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_488] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv)
      1

theorem nb078_distinct_705 (g : Var) :
    (nb078_alpha_dummy_487 g) ≠ (nb078_alpha_dummy_488 g) := by
  simpa only [nb078_alpha_dummy_487, nb078_alpha_dummy_488] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_483 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_706 :
    (nb078_alpha_dummy_493) ∉ (((Class.cv (nb078_alpha_dummy_486))).fv) := by
  simpa only [nb078_alpha_dummy_493] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_486))).fv) 0

theorem nb078_fresh_707 :
    (nb078_alpha_dummy_494) ∉ (((Class.cv (nb078_alpha_dummy_486))).fv) := by
  simpa only [nb078_alpha_dummy_494] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_486))).fv) 1

theorem nb078_distinct_708 : (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_494) := by
  simpa only [nb078_alpha_dummy_493, nb078_alpha_dummy_494] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_486))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_709 (g : Var) :
    (nb078_alpha_dummy_495 g) ∉ (((Class.cv (nb078_alpha_dummy_488 g))).fv) := by
  simpa only [nb078_alpha_dummy_495] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_488 g))).fv) 0

theorem nb078_fresh_710 (g : Var) :
    (nb078_alpha_dummy_496 g) ∉ (((Class.cv (nb078_alpha_dummy_488 g))).fv) := by
  simpa only [nb078_alpha_dummy_496] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_488 g))).fv) 1

theorem nb078_distinct_711 (g : Var) :
    (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_496 g) := by
  simpa only [nb078_alpha_dummy_495, nb078_alpha_dummy_496] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_488 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_712 :
    (nb078_alpha_dummy_499) ∉
      (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_499] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_713 :
    (nb078_alpha_dummy_500) ∉
      (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_500] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_714 :
    (nb078_alpha_dummy_501) ∉
      (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_501] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_715 : (nb078_alpha_dummy_499) ≠ (nb078_alpha_dummy_500) := by
  simpa only [nb078_alpha_dummy_499, nb078_alpha_dummy_500] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_716 : (nb078_alpha_dummy_499) ≠ (nb078_alpha_dummy_501) := by
  simpa only [nb078_alpha_dummy_499, nb078_alpha_dummy_501] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_717 : (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_501) := by
  simpa only [nb078_alpha_dummy_500, nb078_alpha_dummy_501] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_718 (g : Var) :
    (nb078_alpha_dummy_502 g) ∉
      (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_502] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_719 (g : Var) :
    (nb078_alpha_dummy_503 g) ∉
      (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_503] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_720 (g : Var) :
    (nb078_alpha_dummy_504 g) ∉
      (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_504] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_721 (g : Var) :
    (nb078_alpha_dummy_502 g) ≠ (nb078_alpha_dummy_503 g) := by
  simpa only [nb078_alpha_dummy_502, nb078_alpha_dummy_503] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_722 (g : Var) :
    (nb078_alpha_dummy_502 g) ≠ (nb078_alpha_dummy_504 g) := by
  simpa only [nb078_alpha_dummy_502, nb078_alpha_dummy_504] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_723 (g : Var) :
    (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_504 g) := by
  simpa only [nb078_alpha_dummy_503, nb078_alpha_dummy_504] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_724 :
    (nb078_alpha_dummy_511) ∉
      (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_500))).fv) :=
  by
  simpa only [nb078_alpha_dummy_511] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_500))).fv)
      0

theorem nb078_fresh_725 :
    (nb078_alpha_dummy_507) ∉
      (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) :=
  by
  simpa only [nb078_alpha_dummy_507] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv)
      0

theorem nb078_fresh_726 :
    (nb078_alpha_dummy_513) ∉
      (((Class.cv (nb078_alpha_dummy_501))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) :=
  by
  simpa only [nb078_alpha_dummy_513] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_501))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv)
      0

theorem nb078_fresh_727 (g : Var) :
    (nb078_alpha_dummy_512 g) ∉
      (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_503 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_512] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_503 g))).fv)
      0

theorem nb078_fresh_728 (g : Var) :
    (nb078_alpha_dummy_508 g) ∉
      (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_508] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv)
      0

theorem nb078_fresh_729 (g : Var) :
    (nb078_alpha_dummy_514 g) ∉
      (((Class.cv (nb078_alpha_dummy_504 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_514] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_504 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv)
      0

theorem nb078_fresh_730 :
    (nb078_alpha_dummy_529) ∉
      (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) :=
  by
  simpa only [nb078_alpha_dummy_529] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv)
      0

theorem nb078_fresh_731 :
    (nb078_alpha_dummy_530) ∉
      (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) :=
  by
  simpa only [nb078_alpha_dummy_530] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv)
      1

theorem nb078_distinct_732 : (nb078_alpha_dummy_529) ≠ (nb078_alpha_dummy_530) := by
  simpa only [nb078_alpha_dummy_529, nb078_alpha_dummy_530] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_733 (g : Var) :
    (nb078_alpha_dummy_531 g) ∉
      (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_531] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv)
      0

theorem nb078_fresh_734 (g : Var) :
    (nb078_alpha_dummy_532 g) ∉
      (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_532] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv)
      1

theorem nb078_distinct_735 (g : Var) :
    (nb078_alpha_dummy_531 g) ≠ (nb078_alpha_dummy_532 g) := by
  simpa only [nb078_alpha_dummy_531, nb078_alpha_dummy_532] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_527 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_736 :
    (nb078_alpha_dummy_537) ∉ (((Class.cv (nb078_alpha_dummy_530))).fv) := by
  simpa only [nb078_alpha_dummy_537] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_530))).fv) 0

theorem nb078_fresh_737 :
    (nb078_alpha_dummy_538) ∉ (((Class.cv (nb078_alpha_dummy_530))).fv) := by
  simpa only [nb078_alpha_dummy_538] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_530))).fv) 1

theorem nb078_distinct_738 : (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_538) := by
  simpa only [nb078_alpha_dummy_537, nb078_alpha_dummy_538] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_530))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_739 (g : Var) :
    (nb078_alpha_dummy_539 g) ∉ (((Class.cv (nb078_alpha_dummy_532 g))).fv) := by
  simpa only [nb078_alpha_dummy_539] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_532 g))).fv) 0

theorem nb078_fresh_740 (g : Var) :
    (nb078_alpha_dummy_540 g) ∉ (((Class.cv (nb078_alpha_dummy_532 g))).fv) := by
  simpa only [nb078_alpha_dummy_540] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_532 g))).fv) 1

theorem nb078_distinct_741 (g : Var) :
    (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_540 g) := by
  simpa only [nb078_alpha_dummy_539, nb078_alpha_dummy_540] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_532 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_742 :
    (nb078_alpha_dummy_543) ∉
      (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_543] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_743 :
    (nb078_alpha_dummy_544) ∉
      (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_544] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_744 :
    (nb078_alpha_dummy_545) ∉
      (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_545] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_745 : (nb078_alpha_dummy_543) ≠ (nb078_alpha_dummy_544) := by
  simpa only [nb078_alpha_dummy_543, nb078_alpha_dummy_544] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_746 : (nb078_alpha_dummy_543) ≠ (nb078_alpha_dummy_545) := by
  simpa only [nb078_alpha_dummy_543, nb078_alpha_dummy_545] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_747 : (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_545) := by
  simpa only [nb078_alpha_dummy_544, nb078_alpha_dummy_545] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_748 (g : Var) :
    (nb078_alpha_dummy_546 g) ∉
      (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_546] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_749 (g : Var) :
    (nb078_alpha_dummy_547 g) ∉
      (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_547] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_750 (g : Var) :
    (nb078_alpha_dummy_548 g) ∉
      (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_548] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_751 (g : Var) :
    (nb078_alpha_dummy_546 g) ≠ (nb078_alpha_dummy_547 g) := by
  simpa only [nb078_alpha_dummy_546, nb078_alpha_dummy_547] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_752 (g : Var) :
    (nb078_alpha_dummy_546 g) ≠ (nb078_alpha_dummy_548 g) := by
  simpa only [nb078_alpha_dummy_546, nb078_alpha_dummy_548] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_753 (g : Var) :
    (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_548 g) := by
  simpa only [nb078_alpha_dummy_547, nb078_alpha_dummy_548] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_754 :
    (nb078_alpha_dummy_555) ∉
      (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_544))).fv) :=
  by
  simpa only [nb078_alpha_dummy_555] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_544))).fv)
      0

theorem nb078_fresh_755 :
    (nb078_alpha_dummy_551) ∉
      (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) :=
  by
  simpa only [nb078_alpha_dummy_551] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv)
      0

theorem nb078_fresh_756 :
    (nb078_alpha_dummy_557) ∉
      (((Class.cv (nb078_alpha_dummy_545))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) :=
  by
  simpa only [nb078_alpha_dummy_557] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_545))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv)
      0

theorem nb078_fresh_757 (g : Var) :
    (nb078_alpha_dummy_556 g) ∉
      (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_547 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_556] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_547 g))).fv)
      0

theorem nb078_fresh_758 (g : Var) :
    (nb078_alpha_dummy_552 g) ∉
      (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_552] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv)
      0

theorem nb078_fresh_759 (g : Var) :
    (nb078_alpha_dummy_558 g) ∉
      (((Class.cv (nb078_alpha_dummy_548 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_558] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_548 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv)
      0

theorem nb078_fresh_760 :
    (nb078_alpha_dummy_577) ∉
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) :=
  by
  simpa only [nb078_alpha_dummy_577] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv)
      0

theorem nb078_fresh_761 :
    (nb078_alpha_dummy_578) ∉
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) :=
  by
  simpa only [nb078_alpha_dummy_578] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv)
      1

theorem nb078_distinct_762 : (nb078_alpha_dummy_577) ≠ (nb078_alpha_dummy_578) := by
  simpa only [nb078_alpha_dummy_577, nb078_alpha_dummy_578] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_763 :
    (nb078_alpha_dummy_613) ∉
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) :=
  by
  simpa only [nb078_alpha_dummy_613] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv)
      0

theorem nb078_fresh_764 :
    (nb078_alpha_dummy_614) ∉
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) :=
  by
  simpa only [nb078_alpha_dummy_614] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv)
      1

theorem nb078_distinct_765 : (nb078_alpha_dummy_613) ≠ (nb078_alpha_dummy_614) := by
  simpa only [nb078_alpha_dummy_613, nb078_alpha_dummy_614] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_766 :
    (nb078_alpha_dummy_727) ∉
      (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) :=
  by
  simpa only [nb078_alpha_dummy_727] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv)
      0

theorem nb078_fresh_767 :
    (nb078_alpha_dummy_728) ∉
      (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) :=
  by
  simpa only [nb078_alpha_dummy_728] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv)
      1

theorem nb078_distinct_768 : (nb078_alpha_dummy_727) ≠ (nb078_alpha_dummy_728) := by
  simpa only [nb078_alpha_dummy_727, nb078_alpha_dummy_728] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_769 (g : Var) :
    (nb078_alpha_dummy_579 g) ∉
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_579] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv)
      0

theorem nb078_fresh_770 (g : Var) :
    (nb078_alpha_dummy_580 g) ∉
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_580] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv)
      1

theorem nb078_distinct_771 (g : Var) :
    (nb078_alpha_dummy_579 g) ≠ (nb078_alpha_dummy_580 g) := by
  simpa only [nb078_alpha_dummy_579, nb078_alpha_dummy_580] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_573 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_772 (g : Var) :
    (nb078_alpha_dummy_615 g) ∉
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_615] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv)
      0

theorem nb078_fresh_773 (g : Var) :
    (nb078_alpha_dummy_616 g) ∉
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_616] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv)
      1

theorem nb078_distinct_774 (g : Var) :
    (nb078_alpha_dummy_615 g) ≠ (nb078_alpha_dummy_616 g) := by
  simpa only [nb078_alpha_dummy_615, nb078_alpha_dummy_616] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_574 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_775 (g : Var) :
    (nb078_alpha_dummy_729 g) ∉
      (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_729] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv)
      0

theorem nb078_fresh_776 (g : Var) :
    (nb078_alpha_dummy_730 g) ∉
      (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_730] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv)
      1

theorem nb078_distinct_777 (g : Var) :
    (nb078_alpha_dummy_729 g) ≠ (nb078_alpha_dummy_730 g) := by
  simpa only [nb078_alpha_dummy_729, nb078_alpha_dummy_730] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_573 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_778 :
    (nb078_alpha_dummy_585) ∉ (((Class.cv (nb078_alpha_dummy_578))).fv) := by
  simpa only [nb078_alpha_dummy_585] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_578))).fv) 0

theorem nb078_fresh_779 :
    (nb078_alpha_dummy_586) ∉ (((Class.cv (nb078_alpha_dummy_578))).fv) := by
  simpa only [nb078_alpha_dummy_586] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_578))).fv) 1

theorem nb078_distinct_780 : (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_586) := by
  simpa only [nb078_alpha_dummy_585, nb078_alpha_dummy_586] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_578))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_781 (g : Var) :
    (nb078_alpha_dummy_587 g) ∉ (((Class.cv (nb078_alpha_dummy_580 g))).fv) := by
  simpa only [nb078_alpha_dummy_587] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_580 g))).fv) 0

theorem nb078_fresh_782 (g : Var) :
    (nb078_alpha_dummy_588 g) ∉ (((Class.cv (nb078_alpha_dummy_580 g))).fv) := by
  simpa only [nb078_alpha_dummy_588] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_580 g))).fv) 1

theorem nb078_distinct_783 (g : Var) :
    (nb078_alpha_dummy_587 g) ≠ (nb078_alpha_dummy_588 g) := by
  simpa only [nb078_alpha_dummy_587, nb078_alpha_dummy_588] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_580 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_784 :
    (nb078_alpha_dummy_591) ∉
      (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_591] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_785 :
    (nb078_alpha_dummy_592) ∉
      (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_592] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_786 :
    (nb078_alpha_dummy_593) ∉
      (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_593] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_787 : (nb078_alpha_dummy_591) ≠ (nb078_alpha_dummy_592) := by
  simpa only [nb078_alpha_dummy_591, nb078_alpha_dummy_592] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_788 : (nb078_alpha_dummy_591) ≠ (nb078_alpha_dummy_593) := by
  simpa only [nb078_alpha_dummy_591, nb078_alpha_dummy_593] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_789 : (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_593) := by
  simpa only [nb078_alpha_dummy_592, nb078_alpha_dummy_593] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_790 (g : Var) :
    (nb078_alpha_dummy_594 g) ∉
      (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_594] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_791 (g : Var) :
    (nb078_alpha_dummy_595 g) ∉
      (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_595] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_792 (g : Var) :
    (nb078_alpha_dummy_596 g) ∉
      (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_596] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_793 (g : Var) :
    (nb078_alpha_dummy_594 g) ≠ (nb078_alpha_dummy_595 g) := by
  simpa only [nb078_alpha_dummy_594, nb078_alpha_dummy_595] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_794 (g : Var) :
    (nb078_alpha_dummy_594 g) ≠ (nb078_alpha_dummy_596 g) := by
  simpa only [nb078_alpha_dummy_594, nb078_alpha_dummy_596] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_795 (g : Var) :
    (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_596 g) := by
  simpa only [nb078_alpha_dummy_595, nb078_alpha_dummy_596] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_796 :
    (nb078_alpha_dummy_603) ∉
      (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_592))).fv) :=
  by
  simpa only [nb078_alpha_dummy_603] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_592))).fv)
      0

theorem nb078_fresh_797 :
    (nb078_alpha_dummy_599) ∉
      (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) :=
  by
  simpa only [nb078_alpha_dummy_599] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv)
      0

theorem nb078_fresh_798 :
    (nb078_alpha_dummy_605) ∉
      (((Class.cv (nb078_alpha_dummy_593))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) :=
  by
  simpa only [nb078_alpha_dummy_605] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_593))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv)
      0

theorem nb078_fresh_799 (g : Var) :
    (nb078_alpha_dummy_604 g) ∉
      (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_595 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_604] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_595 g))).fv)
      0

theorem nb078_fresh_800 (g : Var) :
    (nb078_alpha_dummy_600 g) ∉
      (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_600] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv)
      0

theorem nb078_fresh_801 (g : Var) :
    (nb078_alpha_dummy_606 g) ∉
      (((Class.cv (nb078_alpha_dummy_596 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_606] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_596 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv)
      0

theorem nb078_fresh_802 :
    (nb078_alpha_dummy_621) ∉ (((Class.cv (nb078_alpha_dummy_614))).fv) := by
  simpa only [nb078_alpha_dummy_621] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_614))).fv) 0

theorem nb078_fresh_803 :
    (nb078_alpha_dummy_622) ∉ (((Class.cv (nb078_alpha_dummy_614))).fv) := by
  simpa only [nb078_alpha_dummy_622] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_614))).fv) 1

theorem nb078_distinct_804 : (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_622) := by
  simpa only [nb078_alpha_dummy_621, nb078_alpha_dummy_622] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_614))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_805 (g : Var) :
    (nb078_alpha_dummy_623 g) ∉ (((Class.cv (nb078_alpha_dummy_616 g))).fv) := by
  simpa only [nb078_alpha_dummy_623] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_616 g))).fv) 0

theorem nb078_fresh_806 (g : Var) :
    (nb078_alpha_dummy_624 g) ∉ (((Class.cv (nb078_alpha_dummy_616 g))).fv) := by
  simpa only [nb078_alpha_dummy_624] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_616 g))).fv) 1

theorem nb078_distinct_807 (g : Var) :
    (nb078_alpha_dummy_623 g) ≠ (nb078_alpha_dummy_624 g) := by
  simpa only [nb078_alpha_dummy_623, nb078_alpha_dummy_624] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_616 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_808 :
    (nb078_alpha_dummy_627) ∉
      (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_627] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_809 :
    (nb078_alpha_dummy_628) ∉
      (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_628] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_810 :
    (nb078_alpha_dummy_629) ∉
      (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_629] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_811 : (nb078_alpha_dummy_627) ≠ (nb078_alpha_dummy_628) := by
  simpa only [nb078_alpha_dummy_627, nb078_alpha_dummy_628] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_812 : (nb078_alpha_dummy_627) ≠ (nb078_alpha_dummy_629) := by
  simpa only [nb078_alpha_dummy_627, nb078_alpha_dummy_629] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_813 : (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_629) := by
  simpa only [nb078_alpha_dummy_628, nb078_alpha_dummy_629] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_814 (g : Var) :
    (nb078_alpha_dummy_630 g) ∉
      (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_630] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_815 (g : Var) :
    (nb078_alpha_dummy_631 g) ∉
      (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_631] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_816 (g : Var) :
    (nb078_alpha_dummy_632 g) ∉
      (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_632] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_817 (g : Var) :
    (nb078_alpha_dummy_630 g) ≠ (nb078_alpha_dummy_631 g) := by
  simpa only [nb078_alpha_dummy_630, nb078_alpha_dummy_631] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_818 (g : Var) :
    (nb078_alpha_dummy_630 g) ≠ (nb078_alpha_dummy_632 g) := by
  simpa only [nb078_alpha_dummy_630, nb078_alpha_dummy_632] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_819 (g : Var) :
    (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_632 g) := by
  simpa only [nb078_alpha_dummy_631, nb078_alpha_dummy_632] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_820 :
    (nb078_alpha_dummy_639) ∉
      (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_628))).fv) :=
  by
  simpa only [nb078_alpha_dummy_639] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_628))).fv)
      0

theorem nb078_fresh_821 :
    (nb078_alpha_dummy_635) ∉
      (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) :=
  by
  simpa only [nb078_alpha_dummy_635] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv)
      0

theorem nb078_fresh_822 :
    (nb078_alpha_dummy_641) ∉
      (((Class.cv (nb078_alpha_dummy_629))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) :=
  by
  simpa only [nb078_alpha_dummy_641] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_629))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv)
      0

theorem nb078_fresh_823 (g : Var) :
    (nb078_alpha_dummy_640 g) ∉
      (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_631 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_640] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_631 g))).fv)
      0

theorem nb078_fresh_824 (g : Var) :
    (nb078_alpha_dummy_636 g) ∉
      (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_636] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv)
      0

theorem nb078_fresh_825 (g : Var) :
    (nb078_alpha_dummy_642 g) ∉
      (((Class.cv (nb078_alpha_dummy_632 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_642] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_632 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv)
      0

theorem nb078_fresh_826 :
    (nb078_alpha_dummy_655) ∉
      (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) :=
  by
  simpa only [nb078_alpha_dummy_655] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv)
      0

theorem nb078_fresh_827 :
    (nb078_alpha_dummy_656) ∉
      (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) :=
  by
  simpa only [nb078_alpha_dummy_656] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv)
      1

theorem nb078_distinct_828 : (nb078_alpha_dummy_655) ≠ (nb078_alpha_dummy_656) := by
  simpa only [nb078_alpha_dummy_655, nb078_alpha_dummy_656] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_829 :
    (nb078_alpha_dummy_691) ∉
      (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) :=
  by
  simpa only [nb078_alpha_dummy_691] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv)
      0

theorem nb078_fresh_830 :
    (nb078_alpha_dummy_692) ∉
      (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) :=
  by
  simpa only [nb078_alpha_dummy_692] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv)
      1

theorem nb078_distinct_831 : (nb078_alpha_dummy_691) ≠ (nb078_alpha_dummy_692) := by
  simpa only [nb078_alpha_dummy_691, nb078_alpha_dummy_692] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_832 (g : Var) :
    (nb078_alpha_dummy_657 g) ∉
      (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_657] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv)
      0

theorem nb078_fresh_833 (g : Var) :
    (nb078_alpha_dummy_658 g) ∉
      (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_658] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv)
      1

theorem nb078_distinct_834 (g : Var) :
    (nb078_alpha_dummy_657 g) ≠ (nb078_alpha_dummy_658 g) := by
  simpa only [nb078_alpha_dummy_657, nb078_alpha_dummy_658] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_652 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_835 (g : Var) :
    (nb078_alpha_dummy_693 g) ∉
      (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_693] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv)
      0

theorem nb078_fresh_836 (g : Var) :
    (nb078_alpha_dummy_694 g) ∉
      (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_694] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv)
      1

theorem nb078_distinct_837 (g : Var) :
    (nb078_alpha_dummy_693 g) ≠ (nb078_alpha_dummy_694 g) := by
  simpa only [nb078_alpha_dummy_693, nb078_alpha_dummy_694] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_651 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_838 :
    (nb078_alpha_dummy_663) ∉ (((Class.cv (nb078_alpha_dummy_656))).fv) := by
  simpa only [nb078_alpha_dummy_663] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_656))).fv) 0

theorem nb078_fresh_839 :
    (nb078_alpha_dummy_664) ∉ (((Class.cv (nb078_alpha_dummy_656))).fv) := by
  simpa only [nb078_alpha_dummy_664] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_656))).fv) 1

theorem nb078_distinct_840 : (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_664) := by
  simpa only [nb078_alpha_dummy_663, nb078_alpha_dummy_664] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_656))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_841 (g : Var) :
    (nb078_alpha_dummy_665 g) ∉ (((Class.cv (nb078_alpha_dummy_658 g))).fv) := by
  simpa only [nb078_alpha_dummy_665] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_658 g))).fv) 0

theorem nb078_fresh_842 (g : Var) :
    (nb078_alpha_dummy_666 g) ∉ (((Class.cv (nb078_alpha_dummy_658 g))).fv) := by
  simpa only [nb078_alpha_dummy_666] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_658 g))).fv) 1

theorem nb078_distinct_843 (g : Var) :
    (nb078_alpha_dummy_665 g) ≠ (nb078_alpha_dummy_666 g) := by
  simpa only [nb078_alpha_dummy_665, nb078_alpha_dummy_666] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_658 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_844 :
    (nb078_alpha_dummy_669) ∉
      (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_669] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_845 :
    (nb078_alpha_dummy_670) ∉
      (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_670] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_846 :
    (nb078_alpha_dummy_671) ∉
      (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_671] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_847 : (nb078_alpha_dummy_669) ≠ (nb078_alpha_dummy_670) := by
  simpa only [nb078_alpha_dummy_669, nb078_alpha_dummy_670] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_848 : (nb078_alpha_dummy_669) ≠ (nb078_alpha_dummy_671) := by
  simpa only [nb078_alpha_dummy_669, nb078_alpha_dummy_671] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_849 : (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_671) := by
  simpa only [nb078_alpha_dummy_670, nb078_alpha_dummy_671] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_850 (g : Var) :
    (nb078_alpha_dummy_672 g) ∉
      (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_672] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_851 (g : Var) :
    (nb078_alpha_dummy_673 g) ∉
      (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_673] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_852 (g : Var) :
    (nb078_alpha_dummy_674 g) ∉
      (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_674] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_853 (g : Var) :
    (nb078_alpha_dummy_672 g) ≠ (nb078_alpha_dummy_673 g) := by
  simpa only [nb078_alpha_dummy_672, nb078_alpha_dummy_673] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part016`. -/


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

theorem nb078_distinct_854 (g : Var) :
    (nb078_alpha_dummy_672 g) ≠ (nb078_alpha_dummy_674 g) := by
  simpa only [nb078_alpha_dummy_672, nb078_alpha_dummy_674] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_855 (g : Var) :
    (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_674 g) := by
  simpa only [nb078_alpha_dummy_673, nb078_alpha_dummy_674] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_856 :
    (nb078_alpha_dummy_681) ∉
      (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_670))).fv) :=
  by
  simpa only [nb078_alpha_dummy_681] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_670))).fv)
      0

theorem nb078_fresh_857 :
    (nb078_alpha_dummy_677) ∉
      (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) :=
  by
  simpa only [nb078_alpha_dummy_677] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv)
      0

theorem nb078_fresh_858 :
    (nb078_alpha_dummy_683) ∉
      (((Class.cv (nb078_alpha_dummy_671))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) :=
  by
  simpa only [nb078_alpha_dummy_683] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_671))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv)
      0

theorem nb078_fresh_859 (g : Var) :
    (nb078_alpha_dummy_682 g) ∉
      (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_673 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_682] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_673 g))).fv)
      0

theorem nb078_fresh_860 (g : Var) :
    (nb078_alpha_dummy_678 g) ∉
      (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_678] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv)
      0

theorem nb078_fresh_861 (g : Var) :
    (nb078_alpha_dummy_684 g) ∉
      (((Class.cv (nb078_alpha_dummy_674 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_684] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_674 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv)
      0

theorem nb078_fresh_862 :
    (nb078_alpha_dummy_699) ∉ (((Class.cv (nb078_alpha_dummy_692))).fv) := by
  simpa only [nb078_alpha_dummy_699] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_692))).fv) 0

theorem nb078_fresh_863 :
    (nb078_alpha_dummy_700) ∉ (((Class.cv (nb078_alpha_dummy_692))).fv) := by
  simpa only [nb078_alpha_dummy_700] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_692))).fv) 1

theorem nb078_distinct_864 : (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_700) := by
  simpa only [nb078_alpha_dummy_699, nb078_alpha_dummy_700] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_692))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_865 (g : Var) :
    (nb078_alpha_dummy_701 g) ∉ (((Class.cv (nb078_alpha_dummy_694 g))).fv) := by
  simpa only [nb078_alpha_dummy_701] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_694 g))).fv) 0

theorem nb078_fresh_866 (g : Var) :
    (nb078_alpha_dummy_702 g) ∉ (((Class.cv (nb078_alpha_dummy_694 g))).fv) := by
  simpa only [nb078_alpha_dummy_702] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_694 g))).fv) 1

theorem nb078_distinct_867 (g : Var) :
    (nb078_alpha_dummy_701 g) ≠ (nb078_alpha_dummy_702 g) := by
  simpa only [nb078_alpha_dummy_701, nb078_alpha_dummy_702] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_694 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_868 :
    (nb078_alpha_dummy_705) ∉
      (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_705] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_869 :
    (nb078_alpha_dummy_706) ∉
      (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_706] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_870 :
    (nb078_alpha_dummy_707) ∉
      (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_707] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_871 : (nb078_alpha_dummy_705) ≠ (nb078_alpha_dummy_706) := by
  simpa only [nb078_alpha_dummy_705, nb078_alpha_dummy_706] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_872 : (nb078_alpha_dummy_705) ≠ (nb078_alpha_dummy_707) := by
  simpa only [nb078_alpha_dummy_705, nb078_alpha_dummy_707] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_873 : (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_707) := by
  simpa only [nb078_alpha_dummy_706, nb078_alpha_dummy_707] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_874 (g : Var) :
    (nb078_alpha_dummy_708 g) ∉
      (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_708] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_875 (g : Var) :
    (nb078_alpha_dummy_709 g) ∉
      (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_709] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_876 (g : Var) :
    (nb078_alpha_dummy_710 g) ∉
      (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_710] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_877 (g : Var) :
    (nb078_alpha_dummy_708 g) ≠ (nb078_alpha_dummy_709 g) := by
  simpa only [nb078_alpha_dummy_708, nb078_alpha_dummy_709] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_878 (g : Var) :
    (nb078_alpha_dummy_708 g) ≠ (nb078_alpha_dummy_710 g) := by
  simpa only [nb078_alpha_dummy_708, nb078_alpha_dummy_710] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_879 (g : Var) :
    (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_710 g) := by
  simpa only [nb078_alpha_dummy_709, nb078_alpha_dummy_710] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_880 :
    (nb078_alpha_dummy_717) ∉
      (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_706))).fv) :=
  by
  simpa only [nb078_alpha_dummy_717] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_706))).fv)
      0

theorem nb078_fresh_881 :
    (nb078_alpha_dummy_713) ∉
      (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) :=
  by
  simpa only [nb078_alpha_dummy_713] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv)
      0

theorem nb078_fresh_882 :
    (nb078_alpha_dummy_719) ∉
      (((Class.cv (nb078_alpha_dummy_707))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) :=
  by
  simpa only [nb078_alpha_dummy_719] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_707))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv)
      0

theorem nb078_fresh_883 (g : Var) :
    (nb078_alpha_dummy_718 g) ∉
      (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_709 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_718] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_709 g))).fv)
      0

theorem nb078_fresh_884 (g : Var) :
    (nb078_alpha_dummy_714 g) ∉
      (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_714] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv)
      0

theorem nb078_fresh_885 (g : Var) :
    (nb078_alpha_dummy_720 g) ∉
      (((Class.cv (nb078_alpha_dummy_710 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_720] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_710 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv)
      0

theorem nb078_fresh_886 :
    (nb078_alpha_dummy_735) ∉ (((Class.cv (nb078_alpha_dummy_728))).fv) := by
  simpa only [nb078_alpha_dummy_735] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_728))).fv) 0

theorem nb078_fresh_887 :
    (nb078_alpha_dummy_736) ∉ (((Class.cv (nb078_alpha_dummy_728))).fv) := by
  simpa only [nb078_alpha_dummy_736] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_728))).fv) 1

theorem nb078_distinct_888 : (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_736) := by
  simpa only [nb078_alpha_dummy_735, nb078_alpha_dummy_736] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_728))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_889 (g : Var) :
    (nb078_alpha_dummy_737 g) ∉ (((Class.cv (nb078_alpha_dummy_730 g))).fv) := by
  simpa only [nb078_alpha_dummy_737] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_730 g))).fv) 0

theorem nb078_fresh_890 (g : Var) :
    (nb078_alpha_dummy_738 g) ∉ (((Class.cv (nb078_alpha_dummy_730 g))).fv) := by
  simpa only [nb078_alpha_dummy_738] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_730 g))).fv) 1

theorem nb078_distinct_891 (g : Var) :
    (nb078_alpha_dummy_737 g) ≠ (nb078_alpha_dummy_738 g) := by
  simpa only [nb078_alpha_dummy_737, nb078_alpha_dummy_738] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_730 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_892 :
    (nb078_alpha_dummy_741) ∉
      (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_741] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_893 :
    (nb078_alpha_dummy_742) ∉
      (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_742] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_894 :
    (nb078_alpha_dummy_743) ∉
      (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_743] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_895 : (nb078_alpha_dummy_741) ≠ (nb078_alpha_dummy_742) := by
  simpa only [nb078_alpha_dummy_741, nb078_alpha_dummy_742] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_896 : (nb078_alpha_dummy_741) ≠ (nb078_alpha_dummy_743) := by
  simpa only [nb078_alpha_dummy_741, nb078_alpha_dummy_743] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_897 : (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_743) := by
  simpa only [nb078_alpha_dummy_742, nb078_alpha_dummy_743] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_898 (g : Var) :
    (nb078_alpha_dummy_744 g) ∉
      (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_744] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_899 (g : Var) :
    (nb078_alpha_dummy_745 g) ∉
      (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_745] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_900 (g : Var) :
    (nb078_alpha_dummy_746 g) ∉
      (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_746] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_901 (g : Var) :
    (nb078_alpha_dummy_744 g) ≠ (nb078_alpha_dummy_745 g) := by
  simpa only [nb078_alpha_dummy_744, nb078_alpha_dummy_745] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_902 (g : Var) :
    (nb078_alpha_dummy_744 g) ≠ (nb078_alpha_dummy_746 g) := by
  simpa only [nb078_alpha_dummy_744, nb078_alpha_dummy_746] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_903 (g : Var) :
    (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_746 g) := by
  simpa only [nb078_alpha_dummy_745, nb078_alpha_dummy_746] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_904 :
    (nb078_alpha_dummy_753) ∉
      (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_742))).fv) :=
  by
  simpa only [nb078_alpha_dummy_753] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_742))).fv)
      0

theorem nb078_fresh_905 :
    (nb078_alpha_dummy_749) ∉
      (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) :=
  by
  simpa only [nb078_alpha_dummy_749] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv)
      0

theorem nb078_fresh_906 :
    (nb078_alpha_dummy_755) ∉
      (((Class.cv (nb078_alpha_dummy_743))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) :=
  by
  simpa only [nb078_alpha_dummy_755] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_743))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv)
      0

theorem nb078_fresh_907 (g : Var) :
    (nb078_alpha_dummy_754 g) ∉
      (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_745 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_754] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_745 g))).fv)
      0

theorem nb078_fresh_908 (g : Var) :
    (nb078_alpha_dummy_750 g) ∉
      (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_750] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv)
      0

theorem nb078_fresh_909 (g : Var) :
    (nb078_alpha_dummy_756 g) ∉
      (((Class.cv (nb078_alpha_dummy_746 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_756] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_746 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv)
      0

theorem nb078_fresh_910 :
    (nb078_alpha_dummy_775) ∉
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) :=
  by
  simpa only [nb078_alpha_dummy_775] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv)
      0

theorem nb078_fresh_911 :
    (nb078_alpha_dummy_776) ∉
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) :=
  by
  simpa only [nb078_alpha_dummy_776] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv)
      1

theorem nb078_distinct_912 : (nb078_alpha_dummy_775) ≠ (nb078_alpha_dummy_776) := by
  simpa only [nb078_alpha_dummy_775, nb078_alpha_dummy_776] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_913 :
    (nb078_alpha_dummy_811) ∉
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) :=
  by
  simpa only [nb078_alpha_dummy_811] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv)
      0

theorem nb078_fresh_914 :
    (nb078_alpha_dummy_812) ∉
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) :=
  by
  simpa only [nb078_alpha_dummy_812] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv)
      1

theorem nb078_distinct_915 : (nb078_alpha_dummy_811) ≠ (nb078_alpha_dummy_812) := by
  simpa only [nb078_alpha_dummy_811, nb078_alpha_dummy_812] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_916 :
    (nb078_alpha_dummy_925) ∉
      (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) :=
  by
  simpa only [nb078_alpha_dummy_925] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv)
      0

theorem nb078_fresh_917 :
    (nb078_alpha_dummy_926) ∉
      (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) :=
  by
  simpa only [nb078_alpha_dummy_926] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv)
      1

theorem nb078_distinct_918 : (nb078_alpha_dummy_925) ≠ (nb078_alpha_dummy_926) := by
  simpa only [nb078_alpha_dummy_925, nb078_alpha_dummy_926] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_919 (h : Var) :
    (nb078_alpha_dummy_777 h) ∉
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_777] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv)
      0

theorem nb078_fresh_920 (h : Var) :
    (nb078_alpha_dummy_778 h) ∉
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_778] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv)
      1

theorem nb078_distinct_921 (h : Var) :
    (nb078_alpha_dummy_777 h) ≠ (nb078_alpha_dummy_778 h) := by
  simpa only [nb078_alpha_dummy_777, nb078_alpha_dummy_778] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_771 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_922 (h : Var) :
    (nb078_alpha_dummy_813 h) ∉
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_813] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv)
      0

theorem nb078_fresh_923 (h : Var) :
    (nb078_alpha_dummy_814 h) ∉
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_814] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv)
      1

theorem nb078_distinct_924 (h : Var) :
    (nb078_alpha_dummy_813 h) ≠ (nb078_alpha_dummy_814 h) := by
  simpa only [nb078_alpha_dummy_813, nb078_alpha_dummy_814] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_772 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_925 (h : Var) :
    (nb078_alpha_dummy_927 h) ∉
      (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_927] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv)
      0

theorem nb078_fresh_926 (h : Var) :
    (nb078_alpha_dummy_928 h) ∉
      (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_928] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv)
      1

theorem nb078_distinct_927 (h : Var) :
    (nb078_alpha_dummy_927 h) ≠ (nb078_alpha_dummy_928 h) := by
  simpa only [nb078_alpha_dummy_927, nb078_alpha_dummy_928] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_771 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_928 :
    (nb078_alpha_dummy_783) ∉ (((Class.cv (nb078_alpha_dummy_776))).fv) := by
  simpa only [nb078_alpha_dummy_783] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_776))).fv) 0

theorem nb078_fresh_929 :
    (nb078_alpha_dummy_784) ∉ (((Class.cv (nb078_alpha_dummy_776))).fv) := by
  simpa only [nb078_alpha_dummy_784] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_776))).fv) 1

theorem nb078_distinct_930 : (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_784) := by
  simpa only [nb078_alpha_dummy_783, nb078_alpha_dummy_784] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_776))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_931 (h : Var) :
    (nb078_alpha_dummy_785 h) ∉ (((Class.cv (nb078_alpha_dummy_778 h))).fv) := by
  simpa only [nb078_alpha_dummy_785] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_778 h))).fv) 0

theorem nb078_fresh_932 (h : Var) :
    (nb078_alpha_dummy_786 h) ∉ (((Class.cv (nb078_alpha_dummy_778 h))).fv) := by
  simpa only [nb078_alpha_dummy_786] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_778 h))).fv) 1

theorem nb078_distinct_933 (h : Var) :
    (nb078_alpha_dummy_785 h) ≠ (nb078_alpha_dummy_786 h) := by
  simpa only [nb078_alpha_dummy_785, nb078_alpha_dummy_786] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_778 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_934 :
    (nb078_alpha_dummy_789) ∉
      (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_789] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_935 :
    (nb078_alpha_dummy_790) ∉
      (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_790] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_936 :
    (nb078_alpha_dummy_791) ∉
      (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_791] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_937 : (nb078_alpha_dummy_789) ≠ (nb078_alpha_dummy_790) := by
  simpa only [nb078_alpha_dummy_789, nb078_alpha_dummy_790] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_938 : (nb078_alpha_dummy_789) ≠ (nb078_alpha_dummy_791) := by
  simpa only [nb078_alpha_dummy_789, nb078_alpha_dummy_791] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_939 : (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_791) := by
  simpa only [nb078_alpha_dummy_790, nb078_alpha_dummy_791] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_940 (h : Var) :
    (nb078_alpha_dummy_792 h) ∉
      (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_792] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_941 (h : Var) :
    (nb078_alpha_dummy_793 h) ∉
      (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_793] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_942 (h : Var) :
    (nb078_alpha_dummy_794 h) ∉
      (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_794] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_943 (h : Var) :
    (nb078_alpha_dummy_792 h) ≠ (nb078_alpha_dummy_793 h) := by
  simpa only [nb078_alpha_dummy_792, nb078_alpha_dummy_793] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_944 (h : Var) :
    (nb078_alpha_dummy_792 h) ≠ (nb078_alpha_dummy_794 h) := by
  simpa only [nb078_alpha_dummy_792, nb078_alpha_dummy_794] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_945 (h : Var) :
    (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_794 h) := by
  simpa only [nb078_alpha_dummy_793, nb078_alpha_dummy_794] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_946 :
    (nb078_alpha_dummy_801) ∉
      (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_790))).fv) :=
  by
  simpa only [nb078_alpha_dummy_801] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_790))).fv)
      0

theorem nb078_fresh_947 :
    (nb078_alpha_dummy_797) ∉
      (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) :=
  by
  simpa only [nb078_alpha_dummy_797] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv)
      0

theorem nb078_fresh_948 :
    (nb078_alpha_dummy_803) ∉
      (((Class.cv (nb078_alpha_dummy_791))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) :=
  by
  simpa only [nb078_alpha_dummy_803] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_791))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv)
      0

theorem nb078_fresh_949 (h : Var) :
    (nb078_alpha_dummy_802 h) ∉
      (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_793 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_802] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_793 h))).fv)
      0

theorem nb078_fresh_950 (h : Var) :
    (nb078_alpha_dummy_798 h) ∉
      (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_798] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv)
      0

theorem nb078_fresh_951 (h : Var) :
    (nb078_alpha_dummy_804 h) ∉
      (((Class.cv (nb078_alpha_dummy_794 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_804] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_794 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv)
      0

theorem nb078_fresh_952 :
    (nb078_alpha_dummy_819) ∉ (((Class.cv (nb078_alpha_dummy_812))).fv) := by
  simpa only [nb078_alpha_dummy_819] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_812))).fv) 0

theorem nb078_fresh_953 :
    (nb078_alpha_dummy_820) ∉ (((Class.cv (nb078_alpha_dummy_812))).fv) := by
  simpa only [nb078_alpha_dummy_820] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_812))).fv) 1

theorem nb078_distinct_954 : (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_820) := by
  simpa only [nb078_alpha_dummy_819, nb078_alpha_dummy_820] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_812))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_955 (h : Var) :
    (nb078_alpha_dummy_821 h) ∉ (((Class.cv (nb078_alpha_dummy_814 h))).fv) := by
  simpa only [nb078_alpha_dummy_821] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_814 h))).fv) 0

theorem nb078_fresh_956 (h : Var) :
    (nb078_alpha_dummy_822 h) ∉ (((Class.cv (nb078_alpha_dummy_814 h))).fv) := by
  simpa only [nb078_alpha_dummy_822] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_814 h))).fv) 1

theorem nb078_distinct_957 (h : Var) :
    (nb078_alpha_dummy_821 h) ≠ (nb078_alpha_dummy_822 h) := by
  simpa only [nb078_alpha_dummy_821, nb078_alpha_dummy_822] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_814 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_958 :
    (nb078_alpha_dummy_825) ∉
      (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_825] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_959 :
    (nb078_alpha_dummy_826) ∉
      (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_826] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_960 :
    (nb078_alpha_dummy_827) ∉
      (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_827] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_961 : (nb078_alpha_dummy_825) ≠ (nb078_alpha_dummy_826) := by
  simpa only [nb078_alpha_dummy_825, nb078_alpha_dummy_826] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_962 : (nb078_alpha_dummy_825) ≠ (nb078_alpha_dummy_827) := by
  simpa only [nb078_alpha_dummy_825, nb078_alpha_dummy_827] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_963 : (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_827) := by
  simpa only [nb078_alpha_dummy_826, nb078_alpha_dummy_827] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_964 (h : Var) :
    (nb078_alpha_dummy_828 h) ∉
      (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_828] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_965 (h : Var) :
    (nb078_alpha_dummy_829 h) ∉
      (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_829] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_966 (h : Var) :
    (nb078_alpha_dummy_830 h) ∉
      (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_830] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_967 (h : Var) :
    (nb078_alpha_dummy_828 h) ≠ (nb078_alpha_dummy_829 h) := by
  simpa only [nb078_alpha_dummy_828, nb078_alpha_dummy_829] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_968 (h : Var) :
    (nb078_alpha_dummy_828 h) ≠ (nb078_alpha_dummy_830 h) := by
  simpa only [nb078_alpha_dummy_828, nb078_alpha_dummy_830] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_969 (h : Var) :
    (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_830 h) := by
  simpa only [nb078_alpha_dummy_829, nb078_alpha_dummy_830] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_970 :
    (nb078_alpha_dummy_837) ∉
      (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_826))).fv) :=
  by
  simpa only [nb078_alpha_dummy_837] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_826))).fv)
      0

theorem nb078_fresh_971 :
    (nb078_alpha_dummy_833) ∉
      (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) :=
  by
  simpa only [nb078_alpha_dummy_833] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv)
      0

theorem nb078_fresh_972 :
    (nb078_alpha_dummy_839) ∉
      (((Class.cv (nb078_alpha_dummy_827))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) :=
  by
  simpa only [nb078_alpha_dummy_839] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_827))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv)
      0

theorem nb078_fresh_973 (h : Var) :
    (nb078_alpha_dummy_838 h) ∉
      (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_829 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_838] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_829 h))).fv)
      0

theorem nb078_fresh_974 (h : Var) :
    (nb078_alpha_dummy_834 h) ∉
      (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_834] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv)
      0

theorem nb078_fresh_975 (h : Var) :
    (nb078_alpha_dummy_840 h) ∉
      (((Class.cv (nb078_alpha_dummy_830 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_840] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_830 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv)
      0

theorem nb078_fresh_976 :
    (nb078_alpha_dummy_853) ∉
      (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) :=
  by
  simpa only [nb078_alpha_dummy_853] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv)
      0

theorem nb078_fresh_977 :
    (nb078_alpha_dummy_854) ∉
      (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) :=
  by
  simpa only [nb078_alpha_dummy_854] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv)
      1

theorem nb078_distinct_978 : (nb078_alpha_dummy_853) ≠ (nb078_alpha_dummy_854) := by
  simpa only [nb078_alpha_dummy_853, nb078_alpha_dummy_854] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_979 :
    (nb078_alpha_dummy_889) ∉
      (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) :=
  by
  simpa only [nb078_alpha_dummy_889] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv)
      0

theorem nb078_fresh_980 :
    (nb078_alpha_dummy_890) ∉
      (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) :=
  by
  simpa only [nb078_alpha_dummy_890] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv)
      1

theorem nb078_distinct_981 : (nb078_alpha_dummy_889) ≠ (nb078_alpha_dummy_890) := by
  simpa only [nb078_alpha_dummy_889, nb078_alpha_dummy_890] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_982 (h : Var) :
    (nb078_alpha_dummy_855 h) ∉
      (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_855] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv)
      0

theorem nb078_fresh_983 (h : Var) :
    (nb078_alpha_dummy_856 h) ∉
      (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_856] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv)
      1

theorem nb078_distinct_984 (h : Var) :
    (nb078_alpha_dummy_855 h) ≠ (nb078_alpha_dummy_856 h) := by
  simpa only [nb078_alpha_dummy_855, nb078_alpha_dummy_856] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_850 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_985 (h : Var) :
    (nb078_alpha_dummy_891 h) ∉
      (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_891] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv)
      0

theorem nb078_fresh_986 (h : Var) :
    (nb078_alpha_dummy_892 h) ∉
      (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_892] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv)
      1

theorem nb078_distinct_987 (h : Var) :
    (nb078_alpha_dummy_891 h) ≠ (nb078_alpha_dummy_892 h) := by
  simpa only [nb078_alpha_dummy_891, nb078_alpha_dummy_892] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_849 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_988 :
    (nb078_alpha_dummy_861) ∉ (((Class.cv (nb078_alpha_dummy_854))).fv) := by
  simpa only [nb078_alpha_dummy_861] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_854))).fv) 0

theorem nb078_fresh_989 :
    (nb078_alpha_dummy_862) ∉ (((Class.cv (nb078_alpha_dummy_854))).fv) := by
  simpa only [nb078_alpha_dummy_862] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_854))).fv) 1

theorem nb078_distinct_990 : (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_862) := by
  simpa only [nb078_alpha_dummy_861, nb078_alpha_dummy_862] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_991 (h : Var) :
    (nb078_alpha_dummy_863 h) ∉ (((Class.cv (nb078_alpha_dummy_856 h))).fv) := by
  simpa only [nb078_alpha_dummy_863] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_856 h))).fv) 0

theorem nb078_fresh_992 (h : Var) :
    (nb078_alpha_dummy_864 h) ∉ (((Class.cv (nb078_alpha_dummy_856 h))).fv) := by
  simpa only [nb078_alpha_dummy_864] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_856 h))).fv) 1

theorem nb078_distinct_993 (h : Var) :
    (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_864 h) := by
  simpa only [nb078_alpha_dummy_863, nb078_alpha_dummy_864] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_856 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_994 :
    (nb078_alpha_dummy_867) ∉
      (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_867] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_995 :
    (nb078_alpha_dummy_868) ∉
      (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_868] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_996 :
    (nb078_alpha_dummy_869) ∉
      (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_869] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_997 : (nb078_alpha_dummy_867) ≠ (nb078_alpha_dummy_868) := by
  simpa only [nb078_alpha_dummy_867, nb078_alpha_dummy_868] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_998 : (nb078_alpha_dummy_867) ≠ (nb078_alpha_dummy_869) := by
  simpa only [nb078_alpha_dummy_867, nb078_alpha_dummy_869] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_999 : (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_869) := by
  simpa only [nb078_alpha_dummy_868, nb078_alpha_dummy_869] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1000 (h : Var) :
    (nb078_alpha_dummy_870 h) ∉
      (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_870] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1001 (h : Var) :
    (nb078_alpha_dummy_871 h) ∉
      (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_871] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1002 (h : Var) :
    (nb078_alpha_dummy_872 h) ∉
      (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_872] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1003 (h : Var) :
    (nb078_alpha_dummy_870 h) ≠ (nb078_alpha_dummy_871 h) := by
  simpa only [nb078_alpha_dummy_870, nb078_alpha_dummy_871] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part017`. -/


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

theorem nb078_distinct_1004 (h : Var) :
    (nb078_alpha_dummy_870 h) ≠ (nb078_alpha_dummy_872 h) := by
  simpa only [nb078_alpha_dummy_870, nb078_alpha_dummy_872] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1005 (h : Var) :
    (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_872 h) := by
  simpa only [nb078_alpha_dummy_871, nb078_alpha_dummy_872] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1006 :
    (nb078_alpha_dummy_879) ∉
      (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_868))).fv) :=
  by
  simpa only [nb078_alpha_dummy_879] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_868))).fv)
      0

theorem nb078_fresh_1007 :
    (nb078_alpha_dummy_875) ∉
      (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) :=
  by
  simpa only [nb078_alpha_dummy_875] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv)
      0

theorem nb078_fresh_1008 :
    (nb078_alpha_dummy_881) ∉
      (((Class.cv (nb078_alpha_dummy_869))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) :=
  by
  simpa only [nb078_alpha_dummy_881] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_869))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv)
      0

theorem nb078_fresh_1009 (h : Var) :
    (nb078_alpha_dummy_880 h) ∉
      (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_871 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_880] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_871 h))).fv)
      0

theorem nb078_fresh_1010 (h : Var) :
    (nb078_alpha_dummy_876 h) ∉
      (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_876] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv)
      0

theorem nb078_fresh_1011 (h : Var) :
    (nb078_alpha_dummy_882 h) ∉
      (((Class.cv (nb078_alpha_dummy_872 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_882] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_872 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv)
      0

theorem nb078_fresh_1012 :
    (nb078_alpha_dummy_897) ∉ (((Class.cv (nb078_alpha_dummy_890))).fv) := by
  simpa only [nb078_alpha_dummy_897] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_890))).fv) 0

theorem nb078_fresh_1013 :
    (nb078_alpha_dummy_898) ∉ (((Class.cv (nb078_alpha_dummy_890))).fv) := by
  simpa only [nb078_alpha_dummy_898] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_890))).fv) 1

theorem nb078_distinct_1014 : (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_898) := by
  simpa only [nb078_alpha_dummy_897, nb078_alpha_dummy_898] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_890))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1015 (h : Var) :
    (nb078_alpha_dummy_899 h) ∉ (((Class.cv (nb078_alpha_dummy_892 h))).fv) := by
  simpa only [nb078_alpha_dummy_899] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_892 h))).fv) 0

theorem nb078_fresh_1016 (h : Var) :
    (nb078_alpha_dummy_900 h) ∉ (((Class.cv (nb078_alpha_dummy_892 h))).fv) := by
  simpa only [nb078_alpha_dummy_900] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_892 h))).fv) 1

theorem nb078_distinct_1017 (h : Var) :
    (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_900 h) := by
  simpa only [nb078_alpha_dummy_899, nb078_alpha_dummy_900] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_892 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1018 :
    (nb078_alpha_dummy_903) ∉
      (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_903] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1019 :
    (nb078_alpha_dummy_904) ∉
      (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_904] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1020 :
    (nb078_alpha_dummy_905) ∉
      (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_905] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1021 : (nb078_alpha_dummy_903) ≠ (nb078_alpha_dummy_904) := by
  simpa only [nb078_alpha_dummy_903, nb078_alpha_dummy_904] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1022 : (nb078_alpha_dummy_903) ≠ (nb078_alpha_dummy_905) := by
  simpa only [nb078_alpha_dummy_903, nb078_alpha_dummy_905] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1023 : (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_905) := by
  simpa only [nb078_alpha_dummy_904, nb078_alpha_dummy_905] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1024 (h : Var) :
    (nb078_alpha_dummy_906 h) ∉
      (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_906] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1025 (h : Var) :
    (nb078_alpha_dummy_907 h) ∉
      (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_907] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1026 (h : Var) :
    (nb078_alpha_dummy_908 h) ∉
      (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_908] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1027 (h : Var) :
    (nb078_alpha_dummy_906 h) ≠ (nb078_alpha_dummy_907 h) := by
  simpa only [nb078_alpha_dummy_906, nb078_alpha_dummy_907] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1028 (h : Var) :
    (nb078_alpha_dummy_906 h) ≠ (nb078_alpha_dummy_908 h) := by
  simpa only [nb078_alpha_dummy_906, nb078_alpha_dummy_908] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1029 (h : Var) :
    (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_908 h) := by
  simpa only [nb078_alpha_dummy_907, nb078_alpha_dummy_908] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1030 :
    (nb078_alpha_dummy_915) ∉
      (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_904))).fv) :=
  by
  simpa only [nb078_alpha_dummy_915] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_904))).fv)
      0

theorem nb078_fresh_1031 :
    (nb078_alpha_dummy_911) ∉
      (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) :=
  by
  simpa only [nb078_alpha_dummy_911] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv)
      0

theorem nb078_fresh_1032 :
    (nb078_alpha_dummy_917) ∉
      (((Class.cv (nb078_alpha_dummy_905))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) :=
  by
  simpa only [nb078_alpha_dummy_917] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_905))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv)
      0

theorem nb078_fresh_1033 (h : Var) :
    (nb078_alpha_dummy_916 h) ∉
      (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_907 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_916] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_907 h))).fv)
      0

theorem nb078_fresh_1034 (h : Var) :
    (nb078_alpha_dummy_912 h) ∉
      (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_912] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv)
      0

theorem nb078_fresh_1035 (h : Var) :
    (nb078_alpha_dummy_918 h) ∉
      (((Class.cv (nb078_alpha_dummy_908 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_918] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_908 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv)
      0

theorem nb078_fresh_1036 :
    (nb078_alpha_dummy_933) ∉ (((Class.cv (nb078_alpha_dummy_926))).fv) := by
  simpa only [nb078_alpha_dummy_933] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_926))).fv) 0

theorem nb078_fresh_1037 :
    (nb078_alpha_dummy_934) ∉ (((Class.cv (nb078_alpha_dummy_926))).fv) := by
  simpa only [nb078_alpha_dummy_934] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_926))).fv) 1

theorem nb078_distinct_1038 : (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_934) := by
  simpa only [nb078_alpha_dummy_933, nb078_alpha_dummy_934] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_926))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1039 (h : Var) :
    (nb078_alpha_dummy_935 h) ∉ (((Class.cv (nb078_alpha_dummy_928 h))).fv) := by
  simpa only [nb078_alpha_dummy_935] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_928 h))).fv) 0

theorem nb078_fresh_1040 (h : Var) :
    (nb078_alpha_dummy_936 h) ∉ (((Class.cv (nb078_alpha_dummy_928 h))).fv) := by
  simpa only [nb078_alpha_dummy_936] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_928 h))).fv) 1

theorem nb078_distinct_1041 (h : Var) :
    (nb078_alpha_dummy_935 h) ≠ (nb078_alpha_dummy_936 h) := by
  simpa only [nb078_alpha_dummy_935, nb078_alpha_dummy_936] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_928 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1042 :
    (nb078_alpha_dummy_939) ∉
      (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_939] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1043 :
    (nb078_alpha_dummy_940) ∉
      (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_940] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1044 :
    (nb078_alpha_dummy_941) ∉
      (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_941] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1045 : (nb078_alpha_dummy_939) ≠ (nb078_alpha_dummy_940) := by
  simpa only [nb078_alpha_dummy_939, nb078_alpha_dummy_940] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1046 : (nb078_alpha_dummy_939) ≠ (nb078_alpha_dummy_941) := by
  simpa only [nb078_alpha_dummy_939, nb078_alpha_dummy_941] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1047 : (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_941) := by
  simpa only [nb078_alpha_dummy_940, nb078_alpha_dummy_941] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1048 (h : Var) :
    (nb078_alpha_dummy_942 h) ∉
      (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_942] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1049 (h : Var) :
    (nb078_alpha_dummy_943 h) ∉
      (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_943] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1050 (h : Var) :
    (nb078_alpha_dummy_944 h) ∉
      (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_944] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1051 (h : Var) :
    (nb078_alpha_dummy_942 h) ≠ (nb078_alpha_dummy_943 h) := by
  simpa only [nb078_alpha_dummy_942, nb078_alpha_dummy_943] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1052 (h : Var) :
    (nb078_alpha_dummy_942 h) ≠ (nb078_alpha_dummy_944 h) := by
  simpa only [nb078_alpha_dummy_942, nb078_alpha_dummy_944] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1053 (h : Var) :
    (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_944 h) := by
  simpa only [nb078_alpha_dummy_943, nb078_alpha_dummy_944] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1054 :
    (nb078_alpha_dummy_951) ∉
      (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_940))).fv) :=
  by
  simpa only [nb078_alpha_dummy_951] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_940))).fv)
      0

theorem nb078_fresh_1055 :
    (nb078_alpha_dummy_947) ∉
      (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) :=
  by
  simpa only [nb078_alpha_dummy_947] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv)
      0

theorem nb078_fresh_1056 :
    (nb078_alpha_dummy_953) ∉
      (((Class.cv (nb078_alpha_dummy_941))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) :=
  by
  simpa only [nb078_alpha_dummy_953] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_941))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv)
      0

theorem nb078_fresh_1057 (h : Var) :
    (nb078_alpha_dummy_952 h) ∉
      (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_943 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_952] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_943 h))).fv)
      0

theorem nb078_fresh_1058 (h : Var) :
    (nb078_alpha_dummy_948 h) ∉
      (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_948] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv)
      0

theorem nb078_fresh_1059 (h : Var) :
    (nb078_alpha_dummy_954 h) ∉
      (((Class.cv (nb078_alpha_dummy_944 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_954] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_944 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv)
      0

theorem nb078_fresh_1060 :
    (nb078_alpha_dummy_965) ∉
      (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) :=
  by
  simpa only [nb078_alpha_dummy_965] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv)
      0

theorem nb078_fresh_1061 :
    (nb078_alpha_dummy_966) ∉
      (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) :=
  by
  simpa only [nb078_alpha_dummy_966] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv)
      1

theorem nb078_distinct_1062 : (nb078_alpha_dummy_965) ≠ (nb078_alpha_dummy_966) := by
  simpa only [nb078_alpha_dummy_965, nb078_alpha_dummy_966] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1063 (h : Var) :
    (nb078_alpha_dummy_967 h) ∉
      (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_967] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv)
      0

theorem nb078_fresh_1064 (h : Var) :
    (nb078_alpha_dummy_968 h) ∉
      (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_968] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv)
      1

theorem nb078_distinct_1065 (h : Var) :
    (nb078_alpha_dummy_967 h) ≠ (nb078_alpha_dummy_968 h) := by
  simpa only [nb078_alpha_dummy_967, nb078_alpha_dummy_968] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_963 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1066 :
    (nb078_alpha_dummy_973) ∉ (((Class.cv (nb078_alpha_dummy_966))).fv) := by
  simpa only [nb078_alpha_dummy_973] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_966))).fv) 0

theorem nb078_fresh_1067 :
    (nb078_alpha_dummy_974) ∉ (((Class.cv (nb078_alpha_dummy_966))).fv) := by
  simpa only [nb078_alpha_dummy_974] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_966))).fv) 1

theorem nb078_distinct_1068 : (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_974) := by
  simpa only [nb078_alpha_dummy_973, nb078_alpha_dummy_974] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_966))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1069 (h : Var) :
    (nb078_alpha_dummy_975 h) ∉ (((Class.cv (nb078_alpha_dummy_968 h))).fv) := by
  simpa only [nb078_alpha_dummy_975] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_968 h))).fv) 0

theorem nb078_fresh_1070 (h : Var) :
    (nb078_alpha_dummy_976 h) ∉ (((Class.cv (nb078_alpha_dummy_968 h))).fv) := by
  simpa only [nb078_alpha_dummy_976] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_968 h))).fv) 1

theorem nb078_distinct_1071 (h : Var) :
    (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_976 h) := by
  simpa only [nb078_alpha_dummy_975, nb078_alpha_dummy_976] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_968 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1072 :
    (nb078_alpha_dummy_979) ∉
      (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_979] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1073 :
    (nb078_alpha_dummy_980) ∉
      (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_980] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1074 :
    (nb078_alpha_dummy_981) ∉
      (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_981] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1075 : (nb078_alpha_dummy_979) ≠ (nb078_alpha_dummy_980) := by
  simpa only [nb078_alpha_dummy_979, nb078_alpha_dummy_980] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1076 : (nb078_alpha_dummy_979) ≠ (nb078_alpha_dummy_981) := by
  simpa only [nb078_alpha_dummy_979, nb078_alpha_dummy_981] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1077 : (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_981) := by
  simpa only [nb078_alpha_dummy_980, nb078_alpha_dummy_981] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1078 (h : Var) :
    (nb078_alpha_dummy_982 h) ∉
      (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_982] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1079 (h : Var) :
    (nb078_alpha_dummy_983 h) ∉
      (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_983] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1080 (h : Var) :
    (nb078_alpha_dummy_984 h) ∉
      (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_984] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1081 (h : Var) :
    (nb078_alpha_dummy_982 h) ≠ (nb078_alpha_dummy_983 h) := by
  simpa only [nb078_alpha_dummy_982, nb078_alpha_dummy_983] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1082 (h : Var) :
    (nb078_alpha_dummy_982 h) ≠ (nb078_alpha_dummy_984 h) := by
  simpa only [nb078_alpha_dummy_982, nb078_alpha_dummy_984] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1083 (h : Var) :
    (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_984 h) := by
  simpa only [nb078_alpha_dummy_983, nb078_alpha_dummy_984] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1084 :
    (nb078_alpha_dummy_991) ∉
      (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_980))).fv) :=
  by
  simpa only [nb078_alpha_dummy_991] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_980))).fv)
      0

theorem nb078_fresh_1085 :
    (nb078_alpha_dummy_987) ∉
      (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) :=
  by
  simpa only [nb078_alpha_dummy_987] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv)
      0

theorem nb078_fresh_1086 :
    (nb078_alpha_dummy_993) ∉
      (((Class.cv (nb078_alpha_dummy_981))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) :=
  by
  simpa only [nb078_alpha_dummy_993] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_981))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv)
      0

theorem nb078_fresh_1087 (h : Var) :
    (nb078_alpha_dummy_992 h) ∉
      (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_983 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_992] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_983 h))).fv)
      0

theorem nb078_fresh_1088 (h : Var) :
    (nb078_alpha_dummy_988 h) ∉
      (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_988] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv)
      0

theorem nb078_fresh_1089 (h : Var) :
    (nb078_alpha_dummy_994 h) ∉
      (((Class.cv (nb078_alpha_dummy_984 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_994] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_984 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv)
      0

theorem nb078_fresh_1090 (f : Var) : (nb078_alpha_dummy_091 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb078_alpha_dummy_091] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb078_fresh_1091 (f : Var) : (nb078_alpha_dummy_092 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb078_alpha_dummy_092] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb078_distinct_1092 (f : Var) :
    (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_092 f) := by
  simpa only [nb078_alpha_dummy_091, nb078_alpha_dummy_092] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1093 (f : Var) :
    (nb078_alpha_dummy_012 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb078_alpha_dummy_012] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0

theorem nb078_fresh_1094 (f : Var) :
    (nb078_alpha_dummy_013 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb078_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1

theorem nb078_fresh_1095 (f : Var) :
    (nb078_alpha_dummy_014 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb078_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2

theorem nb078_distinct_1096 (f : Var) :
    (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_013 f) := by
  simpa only [nb078_alpha_dummy_012, nb078_alpha_dummy_013] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_distinct_1097 (f : Var) :
    (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_014 f) := by
  simpa only [nb078_alpha_dummy_012, nb078_alpha_dummy_014] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb078_distinct_1098 (f : Var) :
    (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_014 f) := by
  simpa only [nb078_alpha_dummy_013, nb078_alpha_dummy_014] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb078_fresh_1099 (f : Var) :
    (nb078_alpha_dummy_245 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_245] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1100 (f : Var) :
    (nb078_alpha_dummy_246 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_246] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1101 (f : Var) :
    (nb078_alpha_dummy_245 f) ≠ (nb078_alpha_dummy_246 f) := by
  simpa only [nb078_alpha_dummy_245, nb078_alpha_dummy_246] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1102 (g : Var) : (nb078_alpha_dummy_369 g) ∉ (((Class.cv g)).fv) := by
  simpa only [nb078_alpha_dummy_369] using freshVar_not_mem (((Class.cv g)).fv) 0

theorem nb078_fresh_1103 (g : Var) : (nb078_alpha_dummy_370 g) ∉ (((Class.cv g)).fv) := by
  simpa only [nb078_alpha_dummy_370] using freshVar_not_mem (((Class.cv g)).fv) 1

theorem nb078_distinct_1104 (g : Var) :
    (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_370 g) := by
  simpa only [nb078_alpha_dummy_369, nb078_alpha_dummy_370] using
    (freshVar_injective (((Class.cv g)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1105 (g : Var) :
    (nb078_alpha_dummy_290 g) ∉ (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) := by
  simpa only [nb078_alpha_dummy_290] using
    freshVar_not_mem (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 0

theorem nb078_fresh_1106 (g : Var) :
    (nb078_alpha_dummy_291 g) ∉ (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) := by
  simpa only [nb078_alpha_dummy_291] using
    freshVar_not_mem (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 1

theorem nb078_fresh_1107 (g : Var) :
    (nb078_alpha_dummy_292 g) ∉ (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) := by
  simpa only [nb078_alpha_dummy_292] using
    freshVar_not_mem (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 2

theorem nb078_distinct_1108 (g : Var) :
    (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_291 g) := by
  simpa only [nb078_alpha_dummy_290, nb078_alpha_dummy_291] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_distinct_1109 (g : Var) :
    (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_292 g) := by
  simpa only [nb078_alpha_dummy_290, nb078_alpha_dummy_292] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb078_distinct_1110 (g : Var) :
    (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_292 g) := by
  simpa only [nb078_alpha_dummy_291, nb078_alpha_dummy_292] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb078_fresh_1111 (g : Var) :
    (nb078_alpha_dummy_527 g) ∉ (((Class.cv g)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_527] using
    freshVar_not_mem (((Class.cv g)).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1112 (g : Var) :
    (nb078_alpha_dummy_528 g) ∉ (((Class.cv g)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_528] using
    freshVar_not_mem (((Class.cv g)).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1113 (g : Var) :
    (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_528 g) := by
  simpa only [nb078_alpha_dummy_527, nb078_alpha_dummy_528] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1114 (h : Var) : (nb078_alpha_dummy_849 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb078_alpha_dummy_849] using freshVar_not_mem (((Class.cv h)).fv) 0

theorem nb078_fresh_1115 (h : Var) : (nb078_alpha_dummy_850 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb078_alpha_dummy_850] using freshVar_not_mem (((Class.cv h)).fv) 1

theorem nb078_distinct_1116 (h : Var) :
    (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_850 h) := by
  simpa only [nb078_alpha_dummy_849, nb078_alpha_dummy_850] using
    (freshVar_injective (((Class.cv h)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1117 (h : Var) :
    (nb078_alpha_dummy_770 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb078_alpha_dummy_770] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 0

theorem nb078_fresh_1118 (h : Var) :
    (nb078_alpha_dummy_771 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb078_alpha_dummy_771] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 1

theorem nb078_fresh_1119 (h : Var) :
    (nb078_alpha_dummy_772 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb078_alpha_dummy_772] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 2

theorem nb078_distinct_1120 (h : Var) :
    (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_771 h) := by
  simpa only [nb078_alpha_dummy_770, nb078_alpha_dummy_771] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_distinct_1121 (h : Var) :
    (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_772 h) := by
  simpa only [nb078_alpha_dummy_770, nb078_alpha_dummy_772] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb078_distinct_1122 (h : Var) :
    (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_772 h) := by
  simpa only [nb078_alpha_dummy_771, nb078_alpha_dummy_772] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb078_fresh_1123 (h : Var) :
    (nb078_alpha_dummy_1007 h) ∉ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_1007] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1124 (h : Var) :
    (nb078_alpha_dummy_1008 h) ∉ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_1008] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1125 (h : Var) :
    (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1008 h) := by
  simpa only [nb078_alpha_dummy_1007, nb078_alpha_dummy_1008] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1126 :
    (nb078_alpha_dummy_029) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_025)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_025)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_025))).fv) :=
  by
  simpa only [nb078_alpha_dummy_029] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_025)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_025)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_025))).fv)
      0

theorem nb078_fresh_1127 (f : Var) :
    (nb078_alpha_dummy_030 f) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_027 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_027 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_027 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_030] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_027 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_027 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_027 f))).fv)
      0

theorem nb078_fresh_1128 :
    (nb078_alpha_dummy_065) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_061)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_061)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_061))).fv) :=
  by
  simpa only [nb078_alpha_dummy_065] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_061)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_061)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_061))).fv)
      0

theorem nb078_fresh_1129 (f : Var) :
    (nb078_alpha_dummy_066 f) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_063 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_063 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_063 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_066] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_063 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_063 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_063 f))).fv)
      0

theorem nb078_fresh_1130 :
    (nb078_alpha_dummy_1021) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1017)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1017)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1017))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1021] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1017)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1017)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1017))).fv)
      0

theorem nb078_fresh_1131 (h : Var) :
    (nb078_alpha_dummy_1022 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1019 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1019 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1019 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1022] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1019 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1019 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1019 h))).fv)
      0

theorem nb078_fresh_1132 :
    (nb078_alpha_dummy_107) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_103)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_103)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_103))).fv) :=
  by
  simpa only [nb078_alpha_dummy_107] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_103)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_103)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_103))).fv)
      0

theorem nb078_fresh_1133 (f : Var) :
    (nb078_alpha_dummy_108 f) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_105 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_105 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_105 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_108] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_105 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_105 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_105 f))).fv)
      0

theorem nb078_fresh_1134 :
    (nb078_alpha_dummy_1069) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1065)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1065)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1065))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1069] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1065)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1065)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1065))).fv)
      0

theorem nb078_fresh_1135 (h : Var) :
    (nb078_alpha_dummy_1070 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1067 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1067 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1067 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1070] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1067 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1067 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1067 h))).fv)
      0

theorem nb078_fresh_1136 :
    (nb078_alpha_dummy_1105) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1101)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1101)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1101))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1105] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1101)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1101)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1101))).fv)
      0

theorem nb078_fresh_1137 (h : Var) :
    (nb078_alpha_dummy_1106 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1103 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1103 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1103 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1106] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1103 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1103 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1103 h))).fv)
      0

theorem nb078_fresh_1138 :
    (nb078_alpha_dummy_1147) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1143)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1143)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1143))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1147] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1143)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1143)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1143))).fv)
      0

theorem nb078_fresh_1139 (h : Var) :
    (nb078_alpha_dummy_1148 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1145 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1145 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1145 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1148] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1145 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1145 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1145 h))).fv)
      0

theorem nb078_fresh_1140 :
    (nb078_alpha_dummy_1183) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1179)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1179)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1179))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1183] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1179)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1179)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1179))).fv)
      0

theorem nb078_fresh_1141 (h : Var) :
    (nb078_alpha_dummy_1184 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1181 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1181 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1181 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1184] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1181 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1181 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1181 h))).fv)
      0

theorem nb078_fresh_1142 :
    (nb078_alpha_dummy_1219) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1215)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1215)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1215))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1219] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1215)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1215)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1215))).fv)
      0

theorem nb078_fresh_1143 (h : Var) :
    (nb078_alpha_dummy_1220 h) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1217 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1217 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1217 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1220] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1217 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1217 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1217 h))).fv)
      0

theorem nb078_fresh_1144 :
    (nb078_alpha_dummy_143) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_139)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_139)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_139))).fv) :=
  by
  simpa only [nb078_alpha_dummy_143] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_139)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_139)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_139))).fv)
      0

theorem nb078_fresh_1145 (f : Var) :
    (nb078_alpha_dummy_144 f) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_141 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_141 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_141 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_144] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_141 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_141 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_141 f))).fv)
      0

theorem nb078_fresh_1146 :
    (nb078_alpha_dummy_179) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_175)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_175)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_175))).fv) :=
  by
  simpa only [nb078_alpha_dummy_179] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_175)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_175)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_175))).fv)
      0

theorem nb078_fresh_1147 (f : Var) :
    (nb078_alpha_dummy_180 f) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_177 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_177 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_177 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_180] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_177 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_177 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_177 f))).fv)
      0

theorem nb078_fresh_1148 :
    (nb078_alpha_dummy_219) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_215)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_215)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_215))).fv) :=
  by
  simpa only [nb078_alpha_dummy_219] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_215)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_215)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_215))).fv)
      0

theorem nb078_fresh_1149 (f : Var) :
    (nb078_alpha_dummy_220 f) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_217 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_217 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_217 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_220] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_217 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_217 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_217 f))).fv)
      0

theorem nb078_fresh_1150 :
    (nb078_alpha_dummy_259) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_255)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_255)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_255))).fv) :=
  by
  simpa only [nb078_alpha_dummy_259] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_255)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_255)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_255))).fv)
      0

theorem nb078_fresh_1151 (f : Var) :
    (nb078_alpha_dummy_260 f) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_257 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_257 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_257 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_260] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_257 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_257 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_257 f))).fv)
      0

theorem nb078_fresh_1152 :
    (nb078_alpha_dummy_307) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_303)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_303)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_303))).fv) :=
  by
  simpa only [nb078_alpha_dummy_307] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_303)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_303)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_303))).fv)
      0

theorem nb078_fresh_1153 (g : Var) :
    (nb078_alpha_dummy_308 g) ∉
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_305 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_305 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_305 g))).fv) :=
  by
  simpa only [nb078_alpha_dummy_308] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_305 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_305 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_305 g))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
