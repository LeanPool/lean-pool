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
    (nb078AlphaDummy1020 h) ∉ (((Class.cv (nb078AlphaDummy1012 h))).fv) := by
  simpa only [nb078AlphaDummy1020] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1012 h))).fv) 1

theorem nb078_distinct_255 (h : Var) :
    (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1020 h) := by
  simpa only [nb078AlphaDummy1019, nb078AlphaDummy1020] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1012 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_256 :
    (nb078AlphaDummy1023) ∉
      (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1023] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_257 :
    (nb078AlphaDummy1024) ∉
      (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1024] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_258 :
    (nb078AlphaDummy1025) ∉
      (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1025] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_259 : (nb078AlphaDummy1023) ≠ (nb078AlphaDummy1024) := by
  simpa only [nb078AlphaDummy1023, nb078AlphaDummy1024] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_260 : (nb078AlphaDummy1023) ≠ (nb078AlphaDummy1025) := by
  simpa only [nb078AlphaDummy1023, nb078AlphaDummy1025] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_261 : (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1025) := by
  simpa only [nb078AlphaDummy1024, nb078AlphaDummy1025] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_262 (h : Var) :
    (nb078AlphaDummy1026 h) ∉
      (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1026] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_263 (h : Var) :
    (nb078AlphaDummy1027 h) ∉
      (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1027] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_264 (h : Var) :
    (nb078AlphaDummy1028 h) ∉
      (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1028] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_265 (h : Var) :
    (nb078AlphaDummy1026 h) ≠ (nb078AlphaDummy1027 h) := by
  simpa only [nb078AlphaDummy1026, nb078AlphaDummy1027] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_266 (h : Var) :
    (nb078AlphaDummy1026 h) ≠ (nb078AlphaDummy1028 h) := by
  simpa only [nb078AlphaDummy1026, nb078AlphaDummy1028] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_267 (h : Var) :
    (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1028 h) := by
  simpa only [nb078AlphaDummy1027, nb078AlphaDummy1028] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_268 :
    (nb078AlphaDummy1035) ∉
      (((Class.cv (nb078AlphaDummy1024))).fv ∪ ((Class.cv (nb078AlphaDummy1024))).fv) :=
  by
  simpa only [nb078AlphaDummy1035] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1024))).fv ∪ ((Class.cv (nb078AlphaDummy1024))).fv)
      0

theorem nb078_fresh_269 :
    (nb078AlphaDummy1031) ∉
      (((Class.cv (nb078AlphaDummy1024))).fv ∪ ((Class.cv (nb078AlphaDummy1025))).fv) :=
  by
  simpa only [nb078AlphaDummy1031] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1024))).fv ∪ ((Class.cv (nb078AlphaDummy1025))).fv)
      0

theorem nb078_fresh_270 :
    (nb078AlphaDummy1037) ∉
      (((Class.cv (nb078AlphaDummy1025))).fv ∪ ((Class.cv (nb078AlphaDummy1025))).fv) :=
  by
  simpa only [nb078AlphaDummy1037] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1025))).fv ∪ ((Class.cv (nb078AlphaDummy1025))).fv)
      0

theorem nb078_fresh_271 (h : Var) :
    (nb078AlphaDummy1036 h) ∉
      (((Class.cv (nb078AlphaDummy1027 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1027 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1036] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1027 h))).fv ∪ ((Class.cv (nb078AlphaDummy1027 h))).fv)
      0

theorem nb078_fresh_272 (h : Var) :
    (nb078AlphaDummy1032 h) ∉
      (((Class.cv (nb078AlphaDummy1027 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1028 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1032] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1027 h))).fv ∪ ((Class.cv (nb078AlphaDummy1028 h))).fv)
      0

theorem nb078_fresh_273 (h : Var) :
    (nb078AlphaDummy1038 h) ∉
      (((Class.cv (nb078AlphaDummy1028 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1028 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1038] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1028 h))).fv ∪ ((Class.cv (nb078AlphaDummy1028 h))).fv)
      0

theorem nb078_fresh_274 :
    (nb078AlphaDummy109) ∉
      (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy109] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_275 :
    (nb078AlphaDummy110) ∉
      (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy110] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_276 :
    (nb078AlphaDummy111) ∉
      (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy111] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_277 : (nb078AlphaDummy109) ≠ (nb078AlphaDummy110) := by
  simpa only [nb078AlphaDummy109, nb078AlphaDummy110] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_278 : (nb078AlphaDummy109) ≠ (nb078AlphaDummy111) := by
  simpa only [nb078AlphaDummy109, nb078AlphaDummy111] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_279 : (nb078AlphaDummy110) ≠ (nb078AlphaDummy111) := by
  simpa only [nb078AlphaDummy110, nb078AlphaDummy111] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_280 :
    (nb078AlphaDummy1057) ∉
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) :=
  by
  simpa only [nb078AlphaDummy1057] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv)
      0

theorem nb078_fresh_281 :
    (nb078AlphaDummy1058) ∉
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) :=
  by
  simpa only [nb078AlphaDummy1058] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv)
      1

theorem nb078_distinct_282 : (nb078AlphaDummy1057) ≠ (nb078AlphaDummy1058) := by
  simpa only [nb078AlphaDummy1057, nb078AlphaDummy1058] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1049))).fv ∪
        ((Class.cv (nb078AlphaDummy1050))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_283 :
    (nb078AlphaDummy1093) ∉
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1051))).fv) :=
  by
  simpa only [nb078AlphaDummy1093] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1051))).fv)
      0

theorem nb078_fresh_284 :
    (nb078AlphaDummy1094) ∉
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1051))).fv) :=
  by
  simpa only [nb078AlphaDummy1094] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1051))).fv)
      1

theorem nb078_distinct_285 : (nb078AlphaDummy1093) ≠ (nb078AlphaDummy1094) := by
  simpa only [nb078AlphaDummy1093, nb078AlphaDummy1094] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1049))).fv ∪
        ((Class.cv (nb078AlphaDummy1051))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_286 (f : Var) :
    (nb078AlphaDummy112 f) ∉
      (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy112] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_287 (f : Var) :
    (nb078AlphaDummy113 f) ∉
      (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy113] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_288 (f : Var) :
    (nb078AlphaDummy114 f) ∉
      (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy114] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_289 (f : Var) :
    (nb078AlphaDummy112 f) ≠ (nb078AlphaDummy113 f) := by
  simpa only [nb078AlphaDummy112, nb078AlphaDummy113] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_290 (f : Var) :
    (nb078AlphaDummy112 f) ≠ (nb078AlphaDummy114 f) := by
  simpa only [nb078AlphaDummy112, nb078AlphaDummy114] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_291 (f : Var) :
    (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy114 f) := by
  simpa only [nb078AlphaDummy113, nb078AlphaDummy114] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_292 :
    (nb078AlphaDummy1207) ∉
      (((Class.cv (nb078AlphaDummy1051))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) :=
  by
  simpa only [nb078AlphaDummy1207] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1051))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv)
      0

theorem nb078_fresh_293 :
    (nb078AlphaDummy1208) ∉
      (((Class.cv (nb078AlphaDummy1051))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) :=
  by
  simpa only [nb078AlphaDummy1208] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1051))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv)
      1

theorem nb078_distinct_294 : (nb078AlphaDummy1207) ≠ (nb078AlphaDummy1208) := by
  simpa only [nb078AlphaDummy1207, nb078AlphaDummy1208] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1051))).fv ∪
        ((Class.cv (nb078AlphaDummy1050))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_295 (h : Var) :
    (nb078AlphaDummy1059 h) ∉
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1059] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪ ((Class.cv (nb078AlphaDummy1053 h))).fv)
      0

theorem nb078_fresh_296 (h : Var) :
    (nb078AlphaDummy1060 h) ∉
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1060] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪ ((Class.cv (nb078AlphaDummy1053 h))).fv)
      1

theorem nb078_distinct_297 (h : Var) :
    (nb078AlphaDummy1059 h) ≠ (nb078AlphaDummy1060 h) := by
  simpa only [nb078AlphaDummy1059, nb078AlphaDummy1060] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_298 (h : Var) :
    (nb078AlphaDummy1095 h) ∉
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1054 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1095] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪ ((Class.cv (nb078AlphaDummy1054 h))).fv)
      0

theorem nb078_fresh_299 (h : Var) :
    (nb078AlphaDummy1096 h) ∉
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1054 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1096] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪ ((Class.cv (nb078AlphaDummy1054 h))).fv)
      1

theorem nb078_distinct_300 (h : Var) :
    (nb078AlphaDummy1095 h) ≠ (nb078AlphaDummy1096 h) := by
  simpa only [nb078AlphaDummy1095, nb078AlphaDummy1096] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1054 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_301 (h : Var) :
    (nb078AlphaDummy1209 h) ∉
      (((Class.cv (nb078AlphaDummy1054 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1209] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1054 h))).fv ∪ ((Class.cv (nb078AlphaDummy1053 h))).fv)
      0

theorem nb078_fresh_302 (h : Var) :
    (nb078AlphaDummy1210 h) ∉
      (((Class.cv (nb078AlphaDummy1054 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1210] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1054 h))).fv ∪ ((Class.cv (nb078AlphaDummy1053 h))).fv)
      1

theorem nb078_distinct_303 (h : Var) :
    (nb078AlphaDummy1209 h) ≠ (nb078AlphaDummy1210 h) := by
  simpa only [nb078AlphaDummy1209, nb078AlphaDummy1210] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1054 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_304 :
    (nb078AlphaDummy1065) ∉ (((Class.cv (nb078AlphaDummy1058))).fv) := by
  simpa only [nb078AlphaDummy1065] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1058))).fv) 0

theorem nb078_fresh_305 :
    (nb078AlphaDummy1066) ∉ (((Class.cv (nb078AlphaDummy1058))).fv) := by
  simpa only [nb078AlphaDummy1066] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1058))).fv) 1

theorem nb078_distinct_306 : (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1066) := by
  simpa only [nb078AlphaDummy1065, nb078AlphaDummy1066] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1058))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_307 (h : Var) :
    (nb078AlphaDummy1067 h) ∉ (((Class.cv (nb078AlphaDummy1060 h))).fv) := by
  simpa only [nb078AlphaDummy1067] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1060 h))).fv) 0

theorem nb078_fresh_308 (h : Var) :
    (nb078AlphaDummy1068 h) ∉ (((Class.cv (nb078AlphaDummy1060 h))).fv) := by
  simpa only [nb078AlphaDummy1068] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1060 h))).fv) 1

theorem nb078_distinct_309 (h : Var) :
    (nb078AlphaDummy1067 h) ≠ (nb078AlphaDummy1068 h) := by
  simpa only [nb078AlphaDummy1067, nb078AlphaDummy1068] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1060 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_310 :
    (nb078AlphaDummy1071) ∉
      (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1071] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_311 :
    (nb078AlphaDummy1072) ∉
      (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1072] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_312 :
    (nb078AlphaDummy1073) ∉
      (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1073] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_313 : (nb078AlphaDummy1071) ≠ (nb078AlphaDummy1072) := by
  simpa only [nb078AlphaDummy1071, nb078AlphaDummy1072] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_314 : (nb078AlphaDummy1071) ≠ (nb078AlphaDummy1073) := by
  simpa only [nb078AlphaDummy1071, nb078AlphaDummy1073] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_315 : (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1073) := by
  simpa only [nb078AlphaDummy1072, nb078AlphaDummy1073] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_316 (h : Var) :
    (nb078AlphaDummy1074 h) ∉
      (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1074] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_317 (h : Var) :
    (nb078AlphaDummy1075 h) ∉
      (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1075] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_318 (h : Var) :
    (nb078AlphaDummy1076 h) ∉
      (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1076] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_319 (h : Var) :
    (nb078AlphaDummy1074 h) ≠ (nb078AlphaDummy1075 h) := by
  simpa only [nb078AlphaDummy1074, nb078AlphaDummy1075] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_320 (h : Var) :
    (nb078AlphaDummy1074 h) ≠ (nb078AlphaDummy1076 h) := by
  simpa only [nb078AlphaDummy1074, nb078AlphaDummy1076] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_321 (h : Var) :
    (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1076 h) := by
  simpa only [nb078AlphaDummy1075, nb078AlphaDummy1076] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_322 :
    (nb078AlphaDummy1083) ∉
      (((Class.cv (nb078AlphaDummy1072))).fv ∪ ((Class.cv (nb078AlphaDummy1072))).fv) :=
  by
  simpa only [nb078AlphaDummy1083] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1072))).fv ∪ ((Class.cv (nb078AlphaDummy1072))).fv)
      0

theorem nb078_fresh_323 :
    (nb078AlphaDummy1079) ∉
      (((Class.cv (nb078AlphaDummy1072))).fv ∪ ((Class.cv (nb078AlphaDummy1073))).fv) :=
  by
  simpa only [nb078AlphaDummy1079] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1072))).fv ∪ ((Class.cv (nb078AlphaDummy1073))).fv)
      0

theorem nb078_fresh_324 :
    (nb078AlphaDummy1085) ∉
      (((Class.cv (nb078AlphaDummy1073))).fv ∪ ((Class.cv (nb078AlphaDummy1073))).fv) :=
  by
  simpa only [nb078AlphaDummy1085] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1073))).fv ∪ ((Class.cv (nb078AlphaDummy1073))).fv)
      0

theorem nb078_fresh_325 (h : Var) :
    (nb078AlphaDummy1084 h) ∉
      (((Class.cv (nb078AlphaDummy1075 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1075 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1084] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1075 h))).fv ∪ ((Class.cv (nb078AlphaDummy1075 h))).fv)
      0

theorem nb078_fresh_326 (h : Var) :
    (nb078AlphaDummy1080 h) ∉
      (((Class.cv (nb078AlphaDummy1075 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1076 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1080] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1075 h))).fv ∪ ((Class.cv (nb078AlphaDummy1076 h))).fv)
      0

theorem nb078_fresh_327 (h : Var) :
    (nb078AlphaDummy1086 h) ∉
      (((Class.cv (nb078AlphaDummy1076 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1076 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1086] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1076 h))).fv ∪ ((Class.cv (nb078AlphaDummy1076 h))).fv)
      0

theorem nb078_fresh_328 :
    (nb078AlphaDummy1101) ∉ (((Class.cv (nb078AlphaDummy1094))).fv) := by
  simpa only [nb078AlphaDummy1101] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1094))).fv) 0

theorem nb078_fresh_329 :
    (nb078AlphaDummy1102) ∉ (((Class.cv (nb078AlphaDummy1094))).fv) := by
  simpa only [nb078AlphaDummy1102] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1094))).fv) 1

theorem nb078_distinct_330 : (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1102) := by
  simpa only [nb078AlphaDummy1101, nb078AlphaDummy1102] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1094))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_331 (h : Var) :
    (nb078AlphaDummy1103 h) ∉ (((Class.cv (nb078AlphaDummy1096 h))).fv) := by
  simpa only [nb078AlphaDummy1103] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1096 h))).fv) 0

theorem nb078_fresh_332 (h : Var) :
    (nb078AlphaDummy1104 h) ∉ (((Class.cv (nb078AlphaDummy1096 h))).fv) := by
  simpa only [nb078AlphaDummy1104] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1096 h))).fv) 1

theorem nb078_distinct_333 (h : Var) :
    (nb078AlphaDummy1103 h) ≠ (nb078AlphaDummy1104 h) := by
  simpa only [nb078AlphaDummy1103, nb078AlphaDummy1104] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1096 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_334 :
    (nb078AlphaDummy121) ∉
      (((Class.cv (nb078AlphaDummy110))).fv ∪ ((Class.cv (nb078AlphaDummy110))).fv) :=
  by
  simpa only [nb078AlphaDummy121] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy110))).fv ∪ ((Class.cv (nb078AlphaDummy110))).fv)
      0

theorem nb078_fresh_335 :
    (nb078AlphaDummy117) ∉
      (((Class.cv (nb078AlphaDummy110))).fv ∪ ((Class.cv (nb078AlphaDummy111))).fv) :=
  by
  simpa only [nb078AlphaDummy117] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy110))).fv ∪ ((Class.cv (nb078AlphaDummy111))).fv)
      0

theorem nb078_fresh_336 :
    (nb078AlphaDummy1107) ∉
      (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1107] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_337 :
    (nb078AlphaDummy1108) ∉
      (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1108] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_338 :
    (nb078AlphaDummy1109) ∉
      (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1109] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_339 : (nb078AlphaDummy1107) ≠ (nb078AlphaDummy1108) := by
  simpa only [nb078AlphaDummy1107, nb078AlphaDummy1108] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_340 : (nb078AlphaDummy1107) ≠ (nb078AlphaDummy1109) := by
  simpa only [nb078AlphaDummy1107, nb078AlphaDummy1109] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_341 : (nb078AlphaDummy1108) ≠ (nb078AlphaDummy1109) := by
  simpa only [nb078AlphaDummy1108, nb078AlphaDummy1109] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_342 (h : Var) :
    (nb078AlphaDummy1110 h) ∉
      (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1110] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_343 (h : Var) :
    (nb078AlphaDummy1111 h) ∉
      (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1111] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_344 (h : Var) :
    (nb078AlphaDummy1112 h) ∉
      (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1112] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_345 (h : Var) :
    (nb078AlphaDummy1110 h) ≠ (nb078AlphaDummy1111 h) := by
  simpa only [nb078AlphaDummy1110, nb078AlphaDummy1111] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_346 (h : Var) :
    (nb078AlphaDummy1110 h) ≠ (nb078AlphaDummy1112 h) := by
  simpa only [nb078AlphaDummy1110, nb078AlphaDummy1112] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_347 (h : Var) :
    (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1112 h) := by
  simpa only [nb078AlphaDummy1111, nb078AlphaDummy1112] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_348 :
    (nb078AlphaDummy1119) ∉
      (((Class.cv (nb078AlphaDummy1108))).fv ∪ ((Class.cv (nb078AlphaDummy1108))).fv) :=
  by
  simpa only [nb078AlphaDummy1119] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1108))).fv ∪ ((Class.cv (nb078AlphaDummy1108))).fv)
      0

theorem nb078_fresh_349 :
    (nb078AlphaDummy1115) ∉
      (((Class.cv (nb078AlphaDummy1108))).fv ∪ ((Class.cv (nb078AlphaDummy1109))).fv) :=
  by
  simpa only [nb078AlphaDummy1115] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1108))).fv ∪ ((Class.cv (nb078AlphaDummy1109))).fv)
      0

theorem nb078_fresh_350 :
    (nb078AlphaDummy1121) ∉
      (((Class.cv (nb078AlphaDummy1109))).fv ∪ ((Class.cv (nb078AlphaDummy1109))).fv) :=
  by
  simpa only [nb078AlphaDummy1121] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1109))).fv ∪ ((Class.cv (nb078AlphaDummy1109))).fv)
      0

theorem nb078_fresh_351 :
    (nb078AlphaDummy123) ∉
      (((Class.cv (nb078AlphaDummy111))).fv ∪ ((Class.cv (nb078AlphaDummy111))).fv) :=
  by
  simpa only [nb078AlphaDummy123] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy111))).fv ∪ ((Class.cv (nb078AlphaDummy111))).fv)
      0

theorem nb078_fresh_352 (h : Var) :
    (nb078AlphaDummy1120 h) ∉
      (((Class.cv (nb078AlphaDummy1111 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1111 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1120] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1111 h))).fv ∪ ((Class.cv (nb078AlphaDummy1111 h))).fv)
      0

theorem nb078_fresh_353 (h : Var) :
    (nb078AlphaDummy1116 h) ∉
      (((Class.cv (nb078AlphaDummy1111 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1112 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1116] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1111 h))).fv ∪ ((Class.cv (nb078AlphaDummy1112 h))).fv)
      0

theorem nb078_fresh_354 (h : Var) :
    (nb078AlphaDummy1122 h) ∉
      (((Class.cv (nb078AlphaDummy1112 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1112 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1122] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1112 h))).fv ∪ ((Class.cv (nb078AlphaDummy1112 h))).fv)
      0

theorem nb078_fresh_355 :
    (nb078AlphaDummy1135) ∉
      (((Class.cv (nb078AlphaDummy1129))).fv ∪ ((Class.cv (nb078AlphaDummy1130))).fv) :=
  by
  simpa only [nb078AlphaDummy1135] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1129))).fv ∪ ((Class.cv (nb078AlphaDummy1130))).fv)
      0

theorem nb078_fresh_356 :
    (nb078AlphaDummy1136) ∉
      (((Class.cv (nb078AlphaDummy1129))).fv ∪ ((Class.cv (nb078AlphaDummy1130))).fv) :=
  by
  simpa only [nb078AlphaDummy1136] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1129))).fv ∪ ((Class.cv (nb078AlphaDummy1130))).fv)
      1

theorem nb078_distinct_357 : (nb078AlphaDummy1135) ≠ (nb078AlphaDummy1136) := by
  simpa only [nb078AlphaDummy1135, nb078AlphaDummy1136] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1129))).fv ∪
        ((Class.cv (nb078AlphaDummy1130))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_358 (f : Var) :
    (nb078AlphaDummy122 f) ∉
      (((Class.cv (nb078AlphaDummy113 f))).fv ∪ ((Class.cv (nb078AlphaDummy113 f))).fv) :=
  by
  simpa only [nb078AlphaDummy122] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy113 f))).fv ∪ ((Class.cv (nb078AlphaDummy113 f))).fv)
      0

theorem nb078_fresh_359 (f : Var) :
    (nb078AlphaDummy118 f) ∉
      (((Class.cv (nb078AlphaDummy113 f))).fv ∪ ((Class.cv (nb078AlphaDummy114 f))).fv) :=
  by
  simpa only [nb078AlphaDummy118] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy113 f))).fv ∪ ((Class.cv (nb078AlphaDummy114 f))).fv)
      0

theorem nb078_fresh_360 :
    (nb078AlphaDummy1171) ∉
      (((Class.cv (nb078AlphaDummy1130))).fv ∪ ((Class.cv (nb078AlphaDummy1129))).fv) :=
  by
  simpa only [nb078AlphaDummy1171] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1130))).fv ∪ ((Class.cv (nb078AlphaDummy1129))).fv)
      0

theorem nb078_fresh_361 :
    (nb078AlphaDummy1172) ∉
      (((Class.cv (nb078AlphaDummy1130))).fv ∪ ((Class.cv (nb078AlphaDummy1129))).fv) :=
  by
  simpa only [nb078AlphaDummy1172] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1130))).fv ∪ ((Class.cv (nb078AlphaDummy1129))).fv)
      1

theorem nb078_distinct_362 : (nb078AlphaDummy1171) ≠ (nb078AlphaDummy1172) := by
  simpa only [nb078AlphaDummy1171, nb078AlphaDummy1172] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1130))).fv ∪
        ((Class.cv (nb078AlphaDummy1129))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_363 (h : Var) :
    (nb078AlphaDummy1137 h) ∉
      (((Class.cv (nb078AlphaDummy1131 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1132 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1137] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1131 h))).fv ∪ ((Class.cv (nb078AlphaDummy1132 h))).fv)
      0

theorem nb078_fresh_364 (h : Var) :
    (nb078AlphaDummy1138 h) ∉
      (((Class.cv (nb078AlphaDummy1131 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1132 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1138] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1131 h))).fv ∪ ((Class.cv (nb078AlphaDummy1132 h))).fv)
      1

theorem nb078_distinct_365 (h : Var) :
    (nb078AlphaDummy1137 h) ≠ (nb078AlphaDummy1138 h) := by
  simpa only [nb078AlphaDummy1137, nb078AlphaDummy1138] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1131 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1132 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_366 (h : Var) :
    (nb078AlphaDummy1173 h) ∉
      (((Class.cv (nb078AlphaDummy1132 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1131 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1173] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1132 h))).fv ∪ ((Class.cv (nb078AlphaDummy1131 h))).fv)
      0

theorem nb078_fresh_367 (h : Var) :
    (nb078AlphaDummy1174 h) ∉
      (((Class.cv (nb078AlphaDummy1132 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1131 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1174] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1132 h))).fv ∪ ((Class.cv (nb078AlphaDummy1131 h))).fv)
      1

theorem nb078_distinct_368 (h : Var) :
    (nb078AlphaDummy1173 h) ≠ (nb078AlphaDummy1174 h) := by
  simpa only [nb078AlphaDummy1173, nb078AlphaDummy1174] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1132 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1131 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_369 :
    (nb078AlphaDummy1143) ∉ (((Class.cv (nb078AlphaDummy1136))).fv) := by
  simpa only [nb078AlphaDummy1143] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1136))).fv) 0

theorem nb078_fresh_370 :
    (nb078AlphaDummy1144) ∉ (((Class.cv (nb078AlphaDummy1136))).fv) := by
  simpa only [nb078AlphaDummy1144] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1136))).fv) 1

theorem nb078_distinct_371 : (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1144) := by
  simpa only [nb078AlphaDummy1143, nb078AlphaDummy1144] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1136))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_372 (h : Var) :
    (nb078AlphaDummy1145 h) ∉ (((Class.cv (nb078AlphaDummy1138 h))).fv) := by
  simpa only [nb078AlphaDummy1145] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1138 h))).fv) 0

theorem nb078_fresh_373 (h : Var) :
    (nb078AlphaDummy1146 h) ∉ (((Class.cv (nb078AlphaDummy1138 h))).fv) := by
  simpa only [nb078AlphaDummy1146] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1138 h))).fv) 1

theorem nb078_distinct_374 (h : Var) :
    (nb078AlphaDummy1145 h) ≠ (nb078AlphaDummy1146 h) := by
  simpa only [nb078AlphaDummy1145, nb078AlphaDummy1146] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1138 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_375 (f : Var) :
    (nb078AlphaDummy124 f) ∉
      (((Class.cv (nb078AlphaDummy114 f))).fv ∪ ((Class.cv (nb078AlphaDummy114 f))).fv) :=
  by
  simpa only [nb078AlphaDummy124] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy114 f))).fv ∪ ((Class.cv (nb078AlphaDummy114 f))).fv)
      0

theorem nb078_fresh_376 :
    (nb078AlphaDummy1149) ∉
      (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1149] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_377 :
    (nb078AlphaDummy1150) ∉
      (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1150] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_378 :
    (nb078AlphaDummy1151) ∉
      (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1151] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_379 : (nb078AlphaDummy1149) ≠ (nb078AlphaDummy1150) := by
  simpa only [nb078AlphaDummy1149, nb078AlphaDummy1150] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_380 : (nb078AlphaDummy1149) ≠ (nb078AlphaDummy1151) := by
  simpa only [nb078AlphaDummy1149, nb078AlphaDummy1151] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_381 : (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1151) := by
  simpa only [nb078AlphaDummy1150, nb078AlphaDummy1151] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_382 (h : Var) :
    (nb078AlphaDummy1152 h) ∉
      (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1152] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_383 (h : Var) :
    (nb078AlphaDummy1153 h) ∉
      (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1153] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_384 (h : Var) :
    (nb078AlphaDummy1154 h) ∉
      (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1154] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_385 (h : Var) :
    (nb078AlphaDummy1152 h) ≠ (nb078AlphaDummy1153 h) := by
  simpa only [nb078AlphaDummy1152, nb078AlphaDummy1153] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_386 (h : Var) :
    (nb078AlphaDummy1152 h) ≠ (nb078AlphaDummy1154 h) := by
  simpa only [nb078AlphaDummy1152, nb078AlphaDummy1154] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_387 (h : Var) :
    (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1154 h) := by
  simpa only [nb078AlphaDummy1153, nb078AlphaDummy1154] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_388 :
    (nb078AlphaDummy1161) ∉
      (((Class.cv (nb078AlphaDummy1150))).fv ∪ ((Class.cv (nb078AlphaDummy1150))).fv) :=
  by
  simpa only [nb078AlphaDummy1161] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1150))).fv ∪ ((Class.cv (nb078AlphaDummy1150))).fv)
      0

theorem nb078_fresh_389 :
    (nb078AlphaDummy1157) ∉
      (((Class.cv (nb078AlphaDummy1150))).fv ∪ ((Class.cv (nb078AlphaDummy1151))).fv) :=
  by
  simpa only [nb078AlphaDummy1157] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1150))).fv ∪ ((Class.cv (nb078AlphaDummy1151))).fv)
      0

theorem nb078_fresh_390 :
    (nb078AlphaDummy1163) ∉
      (((Class.cv (nb078AlphaDummy1151))).fv ∪ ((Class.cv (nb078AlphaDummy1151))).fv) :=
  by
  simpa only [nb078AlphaDummy1163] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1151))).fv ∪ ((Class.cv (nb078AlphaDummy1151))).fv)
      0

theorem nb078_fresh_391 (h : Var) :
    (nb078AlphaDummy1162 h) ∉
      (((Class.cv (nb078AlphaDummy1153 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1153 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1162] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1153 h))).fv ∪ ((Class.cv (nb078AlphaDummy1153 h))).fv)
      0

theorem nb078_fresh_392 (h : Var) :
    (nb078AlphaDummy1158 h) ∉
      (((Class.cv (nb078AlphaDummy1153 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1154 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1158] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1153 h))).fv ∪ ((Class.cv (nb078AlphaDummy1154 h))).fv)
      0

theorem nb078_fresh_393 (h : Var) :
    (nb078AlphaDummy1164 h) ∉
      (((Class.cv (nb078AlphaDummy1154 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1154 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1164] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1154 h))).fv ∪ ((Class.cv (nb078AlphaDummy1154 h))).fv)
      0

theorem nb078_fresh_394 :
    (nb078AlphaDummy1179) ∉ (((Class.cv (nb078AlphaDummy1172))).fv) := by
  simpa only [nb078AlphaDummy1179] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1172))).fv) 0

theorem nb078_fresh_395 :
    (nb078AlphaDummy1180) ∉ (((Class.cv (nb078AlphaDummy1172))).fv) := by
  simpa only [nb078AlphaDummy1180] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1172))).fv) 1

theorem nb078_distinct_396 : (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1180) := by
  simpa only [nb078AlphaDummy1179, nb078AlphaDummy1180] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1172))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_397 (h : Var) :
    (nb078AlphaDummy1181 h) ∉ (((Class.cv (nb078AlphaDummy1174 h))).fv) := by
  simpa only [nb078AlphaDummy1181] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1174 h))).fv) 0

theorem nb078_fresh_398 (h : Var) :
    (nb078AlphaDummy1182 h) ∉ (((Class.cv (nb078AlphaDummy1174 h))).fv) := by
  simpa only [nb078AlphaDummy1182] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1174 h))).fv) 1

theorem nb078_distinct_399 (h : Var) :
    (nb078AlphaDummy1181 h) ≠ (nb078AlphaDummy1182 h) := by
  simpa only [nb078AlphaDummy1181, nb078AlphaDummy1182] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1174 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_400 :
    (nb078AlphaDummy1185) ∉
      (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1185] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_401 :
    (nb078AlphaDummy1186) ∉
      (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1186] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_402 :
    (nb078AlphaDummy1187) ∉
      (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1187] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_403 : (nb078AlphaDummy1185) ≠ (nb078AlphaDummy1186) := by
  simpa only [nb078AlphaDummy1185, nb078AlphaDummy1186] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (i :=
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

theorem nb078_distinct_404 : (nb078AlphaDummy1185) ≠ (nb078AlphaDummy1187) := by
  simpa only [nb078AlphaDummy1185, nb078AlphaDummy1187] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_405 : (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1187) := by
  simpa only [nb078AlphaDummy1186, nb078AlphaDummy1187] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_406 (h : Var) :
    (nb078AlphaDummy1188 h) ∉
      (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1188] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_407 (h : Var) :
    (nb078AlphaDummy1189 h) ∉
      (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1189] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_408 (h : Var) :
    (nb078AlphaDummy1190 h) ∉
      (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1190] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_409 (h : Var) :
    (nb078AlphaDummy1188 h) ≠ (nb078AlphaDummy1189 h) := by
  simpa only [nb078AlphaDummy1188, nb078AlphaDummy1189] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_410 (h : Var) :
    (nb078AlphaDummy1188 h) ≠ (nb078AlphaDummy1190 h) := by
  simpa only [nb078AlphaDummy1188, nb078AlphaDummy1190] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_411 (h : Var) :
    (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1190 h) := by
  simpa only [nb078AlphaDummy1189, nb078AlphaDummy1190] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_412 :
    (nb078AlphaDummy1197) ∉
      (((Class.cv (nb078AlphaDummy1186))).fv ∪ ((Class.cv (nb078AlphaDummy1186))).fv) :=
  by
  simpa only [nb078AlphaDummy1197] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1186))).fv ∪ ((Class.cv (nb078AlphaDummy1186))).fv)
      0

theorem nb078_fresh_413 :
    (nb078AlphaDummy1193) ∉
      (((Class.cv (nb078AlphaDummy1186))).fv ∪ ((Class.cv (nb078AlphaDummy1187))).fv) :=
  by
  simpa only [nb078AlphaDummy1193] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1186))).fv ∪ ((Class.cv (nb078AlphaDummy1187))).fv)
      0

theorem nb078_fresh_414 :
    (nb078AlphaDummy1199) ∉
      (((Class.cv (nb078AlphaDummy1187))).fv ∪ ((Class.cv (nb078AlphaDummy1187))).fv) :=
  by
  simpa only [nb078AlphaDummy1199] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1187))).fv ∪ ((Class.cv (nb078AlphaDummy1187))).fv)
      0

theorem nb078_fresh_415 (h : Var) :
    (nb078AlphaDummy1198 h) ∉
      (((Class.cv (nb078AlphaDummy1189 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1189 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1198] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1189 h))).fv ∪ ((Class.cv (nb078AlphaDummy1189 h))).fv)
      0

theorem nb078_fresh_416 (h : Var) :
    (nb078AlphaDummy1194 h) ∉
      (((Class.cv (nb078AlphaDummy1189 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1190 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1194] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1189 h))).fv ∪ ((Class.cv (nb078AlphaDummy1190 h))).fv)
      0

theorem nb078_fresh_417 (h : Var) :
    (nb078AlphaDummy1200 h) ∉
      (((Class.cv (nb078AlphaDummy1190 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1190 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1200] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1190 h))).fv ∪ ((Class.cv (nb078AlphaDummy1190 h))).fv)
      0

theorem nb078_fresh_418 :
    (nb078AlphaDummy1215) ∉ (((Class.cv (nb078AlphaDummy1208))).fv) := by
  simpa only [nb078AlphaDummy1215] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1208))).fv) 0

theorem nb078_fresh_419 :
    (nb078AlphaDummy1216) ∉ (((Class.cv (nb078AlphaDummy1208))).fv) := by
  simpa only [nb078AlphaDummy1216] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1208))).fv) 1

theorem nb078_distinct_420 : (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1216) := by
  simpa only [nb078AlphaDummy1215, nb078AlphaDummy1216] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1208))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_421 (h : Var) :
    (nb078AlphaDummy1217 h) ∉ (((Class.cv (nb078AlphaDummy1210 h))).fv) := by
  simpa only [nb078AlphaDummy1217] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1210 h))).fv) 0

theorem nb078_fresh_422 (h : Var) :
    (nb078AlphaDummy1218 h) ∉ (((Class.cv (nb078AlphaDummy1210 h))).fv) := by
  simpa only [nb078AlphaDummy1218] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1210 h))).fv) 1

theorem nb078_distinct_423 (h : Var) :
    (nb078AlphaDummy1217 h) ≠ (nb078AlphaDummy1218 h) := by
  simpa only [nb078AlphaDummy1217, nb078AlphaDummy1218] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1210 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_424 :
    (nb078AlphaDummy1221) ∉
      (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1221] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_425 :
    (nb078AlphaDummy1222) ∉
      (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1222] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_426 :
    (nb078AlphaDummy1223) ∉
      (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1223] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_427 : (nb078AlphaDummy1221) ≠ (nb078AlphaDummy1222) := by
  simpa only [nb078AlphaDummy1221, nb078AlphaDummy1222] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_428 : (nb078AlphaDummy1221) ≠ (nb078AlphaDummy1223) := by
  simpa only [nb078AlphaDummy1221, nb078AlphaDummy1223] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_429 : (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1223) := by
  simpa only [nb078AlphaDummy1222, nb078AlphaDummy1223] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_430 (h : Var) :
    (nb078AlphaDummy1224 h) ∉
      (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1224] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_431 (h : Var) :
    (nb078AlphaDummy1225 h) ∉
      (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1225] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_432 (h : Var) :
    (nb078AlphaDummy1226 h) ∉
      (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy1226] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_433 (h : Var) :
    (nb078AlphaDummy1224 h) ≠ (nb078AlphaDummy1225 h) := by
  simpa only [nb078AlphaDummy1224, nb078AlphaDummy1225] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_distinct_434 (h : Var) :
    (nb078AlphaDummy1224 h) ≠ (nb078AlphaDummy1226 h) := by
  simpa only [nb078AlphaDummy1224, nb078AlphaDummy1226] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb078_distinct_435 (h : Var) :
    (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1226 h) := by
  simpa only [nb078AlphaDummy1225, nb078AlphaDummy1226] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb078_fresh_436 :
    (nb078AlphaDummy1233) ∉
      (((Class.cv (nb078AlphaDummy1222))).fv ∪ ((Class.cv (nb078AlphaDummy1222))).fv) :=
  by
  simpa only [nb078AlphaDummy1233] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1222))).fv ∪ ((Class.cv (nb078AlphaDummy1222))).fv)
      0

theorem nb078_fresh_437 :
    (nb078AlphaDummy1229) ∉
      (((Class.cv (nb078AlphaDummy1222))).fv ∪ ((Class.cv (nb078AlphaDummy1223))).fv) :=
  by
  simpa only [nb078AlphaDummy1229] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1222))).fv ∪ ((Class.cv (nb078AlphaDummy1223))).fv)
      0

theorem nb078_fresh_438 :
    (nb078AlphaDummy1235) ∉
      (((Class.cv (nb078AlphaDummy1223))).fv ∪ ((Class.cv (nb078AlphaDummy1223))).fv) :=
  by
  simpa only [nb078AlphaDummy1235] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1223))).fv ∪ ((Class.cv (nb078AlphaDummy1223))).fv)
      0

theorem nb078_fresh_439 (h : Var) :
    (nb078AlphaDummy1234 h) ∉
      (((Class.cv (nb078AlphaDummy1225 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1225 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1234] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1225 h))).fv ∪ ((Class.cv (nb078AlphaDummy1225 h))).fv)
      0

theorem nb078_fresh_440 (h : Var) :
    (nb078AlphaDummy1230 h) ∉
      (((Class.cv (nb078AlphaDummy1225 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1226 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1230] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1225 h))).fv ∪ ((Class.cv (nb078AlphaDummy1226 h))).fv)
      0

theorem nb078_fresh_441 (h : Var) :
    (nb078AlphaDummy1236 h) ∉
      (((Class.cv (nb078AlphaDummy1226 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1226 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1236] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1226 h))).fv ∪ ((Class.cv (nb078AlphaDummy1226 h))).fv)
      0

theorem nb078_fresh_442 :
    (nb078AlphaDummy139) ∉ (((Class.cv (nb078AlphaDummy132))).fv) := by
  simpa only [nb078AlphaDummy139] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy132))).fv) 0

theorem nb078_fresh_443 :
    (nb078AlphaDummy140) ∉ (((Class.cv (nb078AlphaDummy132))).fv) := by
  simpa only [nb078AlphaDummy140] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy132))).fv) 1

theorem nb078_distinct_444 : (nb078AlphaDummy139) ≠ (nb078AlphaDummy140) := by
  simpa only [nb078AlphaDummy139, nb078AlphaDummy140] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy132))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_445 (f : Var) :
    (nb078AlphaDummy141 f) ∉ (((Class.cv (nb078AlphaDummy134 f))).fv) := by
  simpa only [nb078AlphaDummy141] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy134 f))).fv) 0

theorem nb078_fresh_446 (f : Var) :
    (nb078AlphaDummy142 f) ∉ (((Class.cv (nb078AlphaDummy134 f))).fv) := by
  simpa only [nb078AlphaDummy142] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy134 f))).fv) 1

theorem nb078_distinct_447 (f : Var) :
    (nb078AlphaDummy141 f) ≠ (nb078AlphaDummy142 f) := by
  simpa only [nb078AlphaDummy141, nb078AlphaDummy142] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy134 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_448 :
    (nb078AlphaDummy145) ∉
      (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy145] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_449 :
    (nb078AlphaDummy146) ∉
      (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy146] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_450 :
    (nb078AlphaDummy147) ∉
      (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy147] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_451 : (nb078AlphaDummy145) ≠ (nb078AlphaDummy146) := by
  simpa only [nb078AlphaDummy145, nb078AlphaDummy146] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_452 : (nb078AlphaDummy145) ≠ (nb078AlphaDummy147) := by
  simpa only [nb078AlphaDummy145, nb078AlphaDummy147] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_453 : (nb078AlphaDummy146) ≠ (nb078AlphaDummy147) := by
  simpa only [nb078AlphaDummy146, nb078AlphaDummy147] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_454 (f : Var) :
    (nb078AlphaDummy148 f) ∉
      (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy148] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_455 (f : Var) :
    (nb078AlphaDummy149 f) ∉
      (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy149] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_456 (f : Var) :
    (nb078AlphaDummy150 f) ∉
      (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy150] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_457 (f : Var) :
    (nb078AlphaDummy148 f) ≠ (nb078AlphaDummy149 f) := by
  simpa only [nb078AlphaDummy148, nb078AlphaDummy149] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_458 (f : Var) :
    (nb078AlphaDummy148 f) ≠ (nb078AlphaDummy150 f) := by
  simpa only [nb078AlphaDummy148, nb078AlphaDummy150] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_459 (f : Var) :
    (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy150 f) := by
  simpa only [nb078AlphaDummy149, nb078AlphaDummy150] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_460 :
    (nb078AlphaDummy157) ∉
      (((Class.cv (nb078AlphaDummy146))).fv ∪ ((Class.cv (nb078AlphaDummy146))).fv) :=
  by
  simpa only [nb078AlphaDummy157] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy146))).fv ∪ ((Class.cv (nb078AlphaDummy146))).fv)
      0

theorem nb078_fresh_461 :
    (nb078AlphaDummy153) ∉
      (((Class.cv (nb078AlphaDummy146))).fv ∪ ((Class.cv (nb078AlphaDummy147))).fv) :=
  by
  simpa only [nb078AlphaDummy153] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy146))).fv ∪ ((Class.cv (nb078AlphaDummy147))).fv)
      0

theorem nb078_fresh_462 :
    (nb078AlphaDummy159) ∉
      (((Class.cv (nb078AlphaDummy147))).fv ∪ ((Class.cv (nb078AlphaDummy147))).fv) :=
  by
  simpa only [nb078AlphaDummy159] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy147))).fv ∪ ((Class.cv (nb078AlphaDummy147))).fv)
      0

theorem nb078_fresh_463 (f : Var) :
    (nb078AlphaDummy158 f) ∉
      (((Class.cv (nb078AlphaDummy149 f))).fv ∪ ((Class.cv (nb078AlphaDummy149 f))).fv) :=
  by
  simpa only [nb078AlphaDummy158] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy149 f))).fv ∪ ((Class.cv (nb078AlphaDummy149 f))).fv)
      0

theorem nb078_fresh_464 (f : Var) :
    (nb078AlphaDummy154 f) ∉
      (((Class.cv (nb078AlphaDummy149 f))).fv ∪ ((Class.cv (nb078AlphaDummy150 f))).fv) :=
  by
  simpa only [nb078AlphaDummy154] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy149 f))).fv ∪ ((Class.cv (nb078AlphaDummy150 f))).fv)
      0

theorem nb078_fresh_465 (f : Var) :
    (nb078AlphaDummy160 f) ∉
      (((Class.cv (nb078AlphaDummy150 f))).fv ∪ ((Class.cv (nb078AlphaDummy150 f))).fv) :=
  by
  simpa only [nb078AlphaDummy160] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy150 f))).fv ∪ ((Class.cv (nb078AlphaDummy150 f))).fv)
      0

theorem nb078_fresh_466 :
    (nb078AlphaDummy175) ∉ (((Class.cv (nb078AlphaDummy168))).fv) := by
  simpa only [nb078AlphaDummy175] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy168))).fv) 0

theorem nb078_fresh_467 :
    (nb078AlphaDummy176) ∉ (((Class.cv (nb078AlphaDummy168))).fv) := by
  simpa only [nb078AlphaDummy176] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy168))).fv) 1

theorem nb078_distinct_468 : (nb078AlphaDummy175) ≠ (nb078AlphaDummy176) := by
  simpa only [nb078AlphaDummy175, nb078AlphaDummy176] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy168))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_469 (f : Var) :
    (nb078AlphaDummy177 f) ∉ (((Class.cv (nb078AlphaDummy170 f))).fv) := by
  simpa only [nb078AlphaDummy177] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy170 f))).fv) 0

theorem nb078_fresh_470 (f : Var) :
    (nb078AlphaDummy178 f) ∉ (((Class.cv (nb078AlphaDummy170 f))).fv) := by
  simpa only [nb078AlphaDummy178] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy170 f))).fv) 1

theorem nb078_distinct_471 (f : Var) :
    (nb078AlphaDummy177 f) ≠ (nb078AlphaDummy178 f) := by
  simpa only [nb078AlphaDummy177, nb078AlphaDummy178] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy170 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_472 :
    (nb078AlphaDummy181) ∉
      (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy181] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_473 :
    (nb078AlphaDummy182) ∉
      (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy182] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_474 :
    (nb078AlphaDummy183) ∉
      (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy183] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_475 : (nb078AlphaDummy181) ≠ (nb078AlphaDummy182) := by
  simpa only [nb078AlphaDummy181, nb078AlphaDummy182] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_476 : (nb078AlphaDummy181) ≠ (nb078AlphaDummy183) := by
  simpa only [nb078AlphaDummy181, nb078AlphaDummy183] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_477 : (nb078AlphaDummy182) ≠ (nb078AlphaDummy183) := by
  simpa only [nb078AlphaDummy182, nb078AlphaDummy183] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_478 (f : Var) :
    (nb078AlphaDummy184 f) ∉
      (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy184] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_479 (f : Var) :
    (nb078AlphaDummy185 f) ∉
      (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy185] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_480 (f : Var) :
    (nb078AlphaDummy186 f) ∉
      (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy186] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_481 (f : Var) :
    (nb078AlphaDummy184 f) ≠ (nb078AlphaDummy185 f) := by
  simpa only [nb078AlphaDummy184, nb078AlphaDummy185] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_482 (f : Var) :
    (nb078AlphaDummy184 f) ≠ (nb078AlphaDummy186 f) := by
  simpa only [nb078AlphaDummy184, nb078AlphaDummy186] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_483 (f : Var) :
    (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy186 f) := by
  simpa only [nb078AlphaDummy185, nb078AlphaDummy186] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_484 :
    (nb078AlphaDummy193) ∉
      (((Class.cv (nb078AlphaDummy182))).fv ∪ ((Class.cv (nb078AlphaDummy182))).fv) :=
  by
  simpa only [nb078AlphaDummy193] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy182))).fv ∪ ((Class.cv (nb078AlphaDummy182))).fv)
      0

theorem nb078_fresh_485 :
    (nb078AlphaDummy189) ∉
      (((Class.cv (nb078AlphaDummy182))).fv ∪ ((Class.cv (nb078AlphaDummy183))).fv) :=
  by
  simpa only [nb078AlphaDummy189] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy182))).fv ∪ ((Class.cv (nb078AlphaDummy183))).fv)
      0

theorem nb078_fresh_486 :
    (nb078AlphaDummy195) ∉
      (((Class.cv (nb078AlphaDummy183))).fv ∪ ((Class.cv (nb078AlphaDummy183))).fv) :=
  by
  simpa only [nb078AlphaDummy195] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy183))).fv ∪ ((Class.cv (nb078AlphaDummy183))).fv)
      0

theorem nb078_fresh_487 (f : Var) :
    (nb078AlphaDummy194 f) ∉
      (((Class.cv (nb078AlphaDummy185 f))).fv ∪ ((Class.cv (nb078AlphaDummy185 f))).fv) :=
  by
  simpa only [nb078AlphaDummy194] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy185 f))).fv ∪ ((Class.cv (nb078AlphaDummy185 f))).fv)
      0

theorem nb078_fresh_488 (f : Var) :
    (nb078AlphaDummy190 f) ∉
      (((Class.cv (nb078AlphaDummy185 f))).fv ∪ ((Class.cv (nb078AlphaDummy186 f))).fv) :=
  by
  simpa only [nb078AlphaDummy190] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy185 f))).fv ∪ ((Class.cv (nb078AlphaDummy186 f))).fv)
      0

theorem nb078_fresh_489 (f : Var) :
    (nb078AlphaDummy196 f) ∉
      (((Class.cv (nb078AlphaDummy186 f))).fv ∪ ((Class.cv (nb078AlphaDummy186 f))).fv) :=
  by
  simpa only [nb078AlphaDummy196] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy186 f))).fv ∪ ((Class.cv (nb078AlphaDummy186 f))).fv)
      0

theorem nb078_fresh_490 :
    (nb078AlphaDummy207) ∉
      (((Class.cv (nb078AlphaDummy204))).fv ∪ ((Class.cv (nb078AlphaDummy203))).fv) :=
  by
  simpa only [nb078AlphaDummy207] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy204))).fv ∪ ((Class.cv (nb078AlphaDummy203))).fv)
      0

theorem nb078_fresh_491 :
    (nb078AlphaDummy208) ∉
      (((Class.cv (nb078AlphaDummy204))).fv ∪ ((Class.cv (nb078AlphaDummy203))).fv) :=
  by
  simpa only [nb078AlphaDummy208] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy204))).fv ∪ ((Class.cv (nb078AlphaDummy203))).fv)
      1

theorem nb078_distinct_492 : (nb078AlphaDummy207) ≠ (nb078AlphaDummy208) := by
  simpa only [nb078AlphaDummy207, nb078AlphaDummy208] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy204))).fv ∪ ((Class.cv (nb078AlphaDummy203))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_493 (f : Var) :
    (nb078AlphaDummy209 f) ∉
      (((Class.cv (nb078AlphaDummy206 f))).fv ∪ ((Class.cv (nb078AlphaDummy205 f))).fv) :=
  by
  simpa only [nb078AlphaDummy209] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy206 f))).fv ∪ ((Class.cv (nb078AlphaDummy205 f))).fv)
      0

theorem nb078_fresh_494 (f : Var) :
    (nb078AlphaDummy210 f) ∉
      (((Class.cv (nb078AlphaDummy206 f))).fv ∪ ((Class.cv (nb078AlphaDummy205 f))).fv) :=
  by
  simpa only [nb078AlphaDummy210] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy206 f))).fv ∪ ((Class.cv (nb078AlphaDummy205 f))).fv)
      1

theorem nb078_distinct_495 (f : Var) :
    (nb078AlphaDummy209 f) ≠ (nb078AlphaDummy210 f) := by
  simpa only [nb078AlphaDummy209, nb078AlphaDummy210] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy206 f))).fv ∪
        ((Class.cv (nb078AlphaDummy205 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_496 :
    (nb078AlphaDummy215) ∉ (((Class.cv (nb078AlphaDummy208))).fv) := by
  simpa only [nb078AlphaDummy215] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy208))).fv) 0

theorem nb078_fresh_497 :
    (nb078AlphaDummy216) ∉ (((Class.cv (nb078AlphaDummy208))).fv) := by
  simpa only [nb078AlphaDummy216] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy208))).fv) 1

theorem nb078_distinct_498 : (nb078AlphaDummy215) ≠ (nb078AlphaDummy216) := by
  simpa only [nb078AlphaDummy215, nb078AlphaDummy216] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy208))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_499 (f : Var) :
    (nb078AlphaDummy217 f) ∉ (((Class.cv (nb078AlphaDummy210 f))).fv) := by
  simpa only [nb078AlphaDummy217] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy210 f))).fv) 0

theorem nb078_fresh_500 (f : Var) :
    (nb078AlphaDummy218 f) ∉ (((Class.cv (nb078AlphaDummy210 f))).fv) := by
  simpa only [nb078AlphaDummy218] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy210 f))).fv) 1

theorem nb078_distinct_501 (f : Var) :
    (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy218 f) := by
  simpa only [nb078AlphaDummy217, nb078AlphaDummy218] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy210 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_502 :
    (nb078AlphaDummy221) ∉
      (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy221] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_503 :
    (nb078AlphaDummy222) ∉
      (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy222] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_504 :
    (nb078AlphaDummy223) ∉
      (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy223] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_505 : (nb078AlphaDummy221) ≠ (nb078AlphaDummy222) := by
  simpa only [nb078AlphaDummy221, nb078AlphaDummy222] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_506 : (nb078AlphaDummy221) ≠ (nb078AlphaDummy223) := by
  simpa only [nb078AlphaDummy221, nb078AlphaDummy223] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_507 : (nb078AlphaDummy222) ≠ (nb078AlphaDummy223) := by
  simpa only [nb078AlphaDummy222, nb078AlphaDummy223] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_508 (f : Var) :
    (nb078AlphaDummy224 f) ∉
      (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy224] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_509 (f : Var) :
    (nb078AlphaDummy225 f) ∉
      (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy225] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_510 (f : Var) :
    (nb078AlphaDummy226 f) ∉
      (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy226] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_511 (f : Var) :
    (nb078AlphaDummy224 f) ≠ (nb078AlphaDummy225 f) := by
  simpa only [nb078AlphaDummy224, nb078AlphaDummy225] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_512 (f : Var) :
    (nb078AlphaDummy224 f) ≠ (nb078AlphaDummy226 f) := by
  simpa only [nb078AlphaDummy224, nb078AlphaDummy226] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_513 (f : Var) :
    (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy226 f) := by
  simpa only [nb078AlphaDummy225, nb078AlphaDummy226] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_514 :
    (nb078AlphaDummy233) ∉
      (((Class.cv (nb078AlphaDummy222))).fv ∪ ((Class.cv (nb078AlphaDummy222))).fv) :=
  by
  simpa only [nb078AlphaDummy233] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy222))).fv ∪ ((Class.cv (nb078AlphaDummy222))).fv)
      0

theorem nb078_fresh_515 :
    (nb078AlphaDummy229) ∉
      (((Class.cv (nb078AlphaDummy222))).fv ∪ ((Class.cv (nb078AlphaDummy223))).fv) :=
  by
  simpa only [nb078AlphaDummy229] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy222))).fv ∪ ((Class.cv (nb078AlphaDummy223))).fv)
      0

theorem nb078_fresh_516 :
    (nb078AlphaDummy235) ∉
      (((Class.cv (nb078AlphaDummy223))).fv ∪ ((Class.cv (nb078AlphaDummy223))).fv) :=
  by
  simpa only [nb078AlphaDummy235] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy223))).fv ∪ ((Class.cv (nb078AlphaDummy223))).fv)
      0

theorem nb078_fresh_517 (f : Var) :
    (nb078AlphaDummy234 f) ∉
      (((Class.cv (nb078AlphaDummy225 f))).fv ∪ ((Class.cv (nb078AlphaDummy225 f))).fv) :=
  by
  simpa only [nb078AlphaDummy234] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy225 f))).fv ∪ ((Class.cv (nb078AlphaDummy225 f))).fv)
      0

theorem nb078_fresh_518 (f : Var) :
    (nb078AlphaDummy230 f) ∉
      (((Class.cv (nb078AlphaDummy225 f))).fv ∪ ((Class.cv (nb078AlphaDummy226 f))).fv) :=
  by
  simpa only [nb078AlphaDummy230] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy225 f))).fv ∪ ((Class.cv (nb078AlphaDummy226 f))).fv)
      0

theorem nb078_fresh_519 (f : Var) :
    (nb078AlphaDummy236 f) ∉
      (((Class.cv (nb078AlphaDummy226 f))).fv ∪ ((Class.cv (nb078AlphaDummy226 f))).fv) :=
  by
  simpa only [nb078AlphaDummy236] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy226 f))).fv ∪ ((Class.cv (nb078AlphaDummy226 f))).fv)
      0

theorem nb078_fresh_520 :
    (nb078AlphaDummy247) ∉
      (((Class.cv (nb078AlphaDummy244))).fv ∪ ((Class.cv (nb078AlphaDummy243))).fv) :=
  by
  simpa only [nb078AlphaDummy247] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy244))).fv ∪ ((Class.cv (nb078AlphaDummy243))).fv)
      0

theorem nb078_fresh_521 :
    (nb078AlphaDummy248) ∉
      (((Class.cv (nb078AlphaDummy244))).fv ∪ ((Class.cv (nb078AlphaDummy243))).fv) :=
  by
  simpa only [nb078AlphaDummy248] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy244))).fv ∪ ((Class.cv (nb078AlphaDummy243))).fv)
      1

theorem nb078_distinct_522 : (nb078AlphaDummy247) ≠ (nb078AlphaDummy248) := by
  simpa only [nb078AlphaDummy247, nb078AlphaDummy248] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy244))).fv ∪ ((Class.cv (nb078AlphaDummy243))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_523 (f : Var) :
    (nb078AlphaDummy249 f) ∉
      (((Class.cv (nb078AlphaDummy246 f))).fv ∪ ((Class.cv (nb078AlphaDummy245 f))).fv) :=
  by
  simpa only [nb078AlphaDummy249] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy246 f))).fv ∪ ((Class.cv (nb078AlphaDummy245 f))).fv)
      0

theorem nb078_fresh_524 (f : Var) :
    (nb078AlphaDummy250 f) ∉
      (((Class.cv (nb078AlphaDummy246 f))).fv ∪ ((Class.cv (nb078AlphaDummy245 f))).fv) :=
  by
  simpa only [nb078AlphaDummy250] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy246 f))).fv ∪ ((Class.cv (nb078AlphaDummy245 f))).fv)
      1

theorem nb078_distinct_525 (f : Var) :
    (nb078AlphaDummy249 f) ≠ (nb078AlphaDummy250 f) := by
  simpa only [nb078AlphaDummy249, nb078AlphaDummy250] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy246 f))).fv ∪
        ((Class.cv (nb078AlphaDummy245 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_526 :
    (nb078AlphaDummy255) ∉ (((Class.cv (nb078AlphaDummy248))).fv) := by
  simpa only [nb078AlphaDummy255] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy248))).fv) 0

theorem nb078_fresh_527 :
    (nb078AlphaDummy256) ∉ (((Class.cv (nb078AlphaDummy248))).fv) := by
  simpa only [nb078AlphaDummy256] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy248))).fv) 1

theorem nb078_distinct_528 : (nb078AlphaDummy255) ≠ (nb078AlphaDummy256) := by
  simpa only [nb078AlphaDummy255, nb078AlphaDummy256] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy248))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_529 (f : Var) :
    (nb078AlphaDummy257 f) ∉ (((Class.cv (nb078AlphaDummy250 f))).fv) := by
  simpa only [nb078AlphaDummy257] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy250 f))).fv) 0

theorem nb078_fresh_530 (f : Var) :
    (nb078AlphaDummy258 f) ∉ (((Class.cv (nb078AlphaDummy250 f))).fv) := by
  simpa only [nb078AlphaDummy258] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy250 f))).fv) 1

theorem nb078_distinct_531 (f : Var) :
    (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy258 f) := by
  simpa only [nb078AlphaDummy257, nb078AlphaDummy258] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy250 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_532 :
    (nb078AlphaDummy261) ∉
      (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy261] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_533 :
    (nb078AlphaDummy262) ∉
      (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy262] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_534 :
    (nb078AlphaDummy263) ∉
      (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy263] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_535 : (nb078AlphaDummy261) ≠ (nb078AlphaDummy262) := by
  simpa only [nb078AlphaDummy261, nb078AlphaDummy262] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_536 : (nb078AlphaDummy261) ≠ (nb078AlphaDummy263) := by
  simpa only [nb078AlphaDummy261, nb078AlphaDummy263] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_537 : (nb078AlphaDummy262) ≠ (nb078AlphaDummy263) := by
  simpa only [nb078AlphaDummy262, nb078AlphaDummy263] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_538 (f : Var) :
    (nb078AlphaDummy264 f) ∉
      (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy264] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_539 (f : Var) :
    (nb078AlphaDummy265 f) ∉
      (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy265] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_540 (f : Var) :
    (nb078AlphaDummy266 f) ∉
      (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy266] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_541 (f : Var) :
    (nb078AlphaDummy264 f) ≠ (nb078AlphaDummy265 f) := by
  simpa only [nb078AlphaDummy264, nb078AlphaDummy265] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_542 (f : Var) :
    (nb078AlphaDummy264 f) ≠ (nb078AlphaDummy266 f) := by
  simpa only [nb078AlphaDummy264, nb078AlphaDummy266] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_543 (f : Var) :
    (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy266 f) := by
  simpa only [nb078AlphaDummy265, nb078AlphaDummy266] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_544 :
    (nb078AlphaDummy273) ∉
      (((Class.cv (nb078AlphaDummy262))).fv ∪ ((Class.cv (nb078AlphaDummy262))).fv) :=
  by
  simpa only [nb078AlphaDummy273] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy262))).fv ∪ ((Class.cv (nb078AlphaDummy262))).fv)
      0

theorem nb078_fresh_545 :
    (nb078AlphaDummy269) ∉
      (((Class.cv (nb078AlphaDummy262))).fv ∪ ((Class.cv (nb078AlphaDummy263))).fv) :=
  by
  simpa only [nb078AlphaDummy269] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy262))).fv ∪ ((Class.cv (nb078AlphaDummy263))).fv)
      0

theorem nb078_fresh_546 :
    (nb078AlphaDummy275) ∉
      (((Class.cv (nb078AlphaDummy263))).fv ∪ ((Class.cv (nb078AlphaDummy263))).fv) :=
  by
  simpa only [nb078AlphaDummy275] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy263))).fv ∪ ((Class.cv (nb078AlphaDummy263))).fv)
      0

theorem nb078_fresh_547 (f : Var) :
    (nb078AlphaDummy274 f) ∉
      (((Class.cv (nb078AlphaDummy265 f))).fv ∪ ((Class.cv (nb078AlphaDummy265 f))).fv) :=
  by
  simpa only [nb078AlphaDummy274] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy265 f))).fv ∪ ((Class.cv (nb078AlphaDummy265 f))).fv)
      0

theorem nb078_fresh_548 (f : Var) :
    (nb078AlphaDummy270 f) ∉
      (((Class.cv (nb078AlphaDummy265 f))).fv ∪ ((Class.cv (nb078AlphaDummy266 f))).fv) :=
  by
  simpa only [nb078AlphaDummy270] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy265 f))).fv ∪ ((Class.cv (nb078AlphaDummy266 f))).fv)
      0

theorem nb078_fresh_549 (f : Var) :
    (nb078AlphaDummy276 f) ∉
      (((Class.cv (nb078AlphaDummy266 f))).fv ∪ ((Class.cv (nb078AlphaDummy266 f))).fv) :=
  by
  simpa only [nb078AlphaDummy276] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy266 f))).fv ∪ ((Class.cv (nb078AlphaDummy266 f))).fv)
      0

theorem nb078_fresh_550 :
    (nb078AlphaDummy295) ∉
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) :=
  by
  simpa only [nb078AlphaDummy295] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv)
      0

theorem nb078_fresh_551 :
    (nb078AlphaDummy296) ∉
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) :=
  by
  simpa only [nb078AlphaDummy296] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv)
      1

theorem nb078_distinct_552 : (nb078AlphaDummy295) ≠ (nb078AlphaDummy296) := by
  simpa only [nb078AlphaDummy295, nb078AlphaDummy296] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_553 :
    (nb078AlphaDummy331) ∉
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy289))).fv) :=
  by
  simpa only [nb078AlphaDummy331] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy289))).fv)
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
    (nb078AlphaDummy332) ∉
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy289))).fv) :=
  by
  simpa only [nb078AlphaDummy332] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy289))).fv)
      1

theorem nb078_distinct_555 : (nb078AlphaDummy331) ≠ (nb078AlphaDummy332) := by
  simpa only [nb078AlphaDummy331, nb078AlphaDummy332] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy289))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_556 :
    (nb078AlphaDummy445) ∉
      (((Class.cv (nb078AlphaDummy289))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) :=
  by
  simpa only [nb078AlphaDummy445] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy289))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv)
      0

theorem nb078_fresh_557 :
    (nb078AlphaDummy446) ∉
      (((Class.cv (nb078AlphaDummy289))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) :=
  by
  simpa only [nb078AlphaDummy446] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy289))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv)
      1

theorem nb078_distinct_558 : (nb078AlphaDummy445) ≠ (nb078AlphaDummy446) := by
  simpa only [nb078AlphaDummy445, nb078AlphaDummy446] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy289))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_559 (g : Var) :
    (nb078AlphaDummy297 g) ∉
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv) :=
  by
  simpa only [nb078AlphaDummy297] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv)
      0

theorem nb078_fresh_560 (g : Var) :
    (nb078AlphaDummy298 g) ∉
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv) :=
  by
  simpa only [nb078AlphaDummy298] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv)
      1

theorem nb078_distinct_561 (g : Var) :
    (nb078AlphaDummy297 g) ≠ (nb078AlphaDummy298 g) := by
  simpa only [nb078AlphaDummy297, nb078AlphaDummy298] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy290 g))).fv ∪
        ((Class.cv (nb078AlphaDummy291 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_562 (g : Var) :
    (nb078AlphaDummy333 g) ∉
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy292 g))).fv) :=
  by
  simpa only [nb078AlphaDummy333] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy292 g))).fv)
      0

theorem nb078_fresh_563 (g : Var) :
    (nb078AlphaDummy334 g) ∉
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy292 g))).fv) :=
  by
  simpa only [nb078AlphaDummy334] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy290 g))).fv ∪ ((Class.cv (nb078AlphaDummy292 g))).fv)
      1

theorem nb078_distinct_564 (g : Var) :
    (nb078AlphaDummy333 g) ≠ (nb078AlphaDummy334 g) := by
  simpa only [nb078AlphaDummy333, nb078AlphaDummy334] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy290 g))).fv ∪
        ((Class.cv (nb078AlphaDummy292 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_565 (g : Var) :
    (nb078AlphaDummy447 g) ∉
      (((Class.cv (nb078AlphaDummy292 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv) :=
  by
  simpa only [nb078AlphaDummy447] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy292 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv)
      0

theorem nb078_fresh_566 (g : Var) :
    (nb078AlphaDummy448 g) ∉
      (((Class.cv (nb078AlphaDummy292 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv) :=
  by
  simpa only [nb078AlphaDummy448] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy292 g))).fv ∪ ((Class.cv (nb078AlphaDummy291 g))).fv)
      1

theorem nb078_distinct_567 (g : Var) :
    (nb078AlphaDummy447 g) ≠ (nb078AlphaDummy448 g) := by
  simpa only [nb078AlphaDummy447, nb078AlphaDummy448] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy292 g))).fv ∪
        ((Class.cv (nb078AlphaDummy291 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_568 :
    (nb078AlphaDummy303) ∉ (((Class.cv (nb078AlphaDummy296))).fv) := by
  simpa only [nb078AlphaDummy303] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy296))).fv) 0

theorem nb078_fresh_569 :
    (nb078AlphaDummy304) ∉ (((Class.cv (nb078AlphaDummy296))).fv) := by
  simpa only [nb078AlphaDummy304] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy296))).fv) 1

theorem nb078_distinct_570 : (nb078AlphaDummy303) ≠ (nb078AlphaDummy304) := by
  simpa only [nb078AlphaDummy303, nb078AlphaDummy304] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy296))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_571 (g : Var) :
    (nb078AlphaDummy305 g) ∉ (((Class.cv (nb078AlphaDummy298 g))).fv) := by
  simpa only [nb078AlphaDummy305] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy298 g))).fv) 0

theorem nb078_fresh_572 (g : Var) :
    (nb078AlphaDummy306 g) ∉ (((Class.cv (nb078AlphaDummy298 g))).fv) := by
  simpa only [nb078AlphaDummy306] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy298 g))).fv) 1

theorem nb078_distinct_573 (g : Var) :
    (nb078AlphaDummy305 g) ≠ (nb078AlphaDummy306 g) := by
  simpa only [nb078AlphaDummy305, nb078AlphaDummy306] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy298 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_574 :
    (nb078AlphaDummy309) ∉
      (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy309] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_575 :
    (nb078AlphaDummy310) ∉
      (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy310] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_576 :
    (nb078AlphaDummy311) ∉
      (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy311] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_577 : (nb078AlphaDummy309) ≠ (nb078AlphaDummy310) := by
  simpa only [nb078AlphaDummy309, nb078AlphaDummy310] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_578 : (nb078AlphaDummy309) ≠ (nb078AlphaDummy311) := by
  simpa only [nb078AlphaDummy309, nb078AlphaDummy311] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_579 : (nb078AlphaDummy310) ≠ (nb078AlphaDummy311) := by
  simpa only [nb078AlphaDummy310, nb078AlphaDummy311] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_580 (g : Var) :
    (nb078AlphaDummy312 g) ∉
      (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy312] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_581 (g : Var) :
    (nb078AlphaDummy313 g) ∉
      (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy313] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_582 (g : Var) :
    (nb078AlphaDummy314 g) ∉
      (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy314] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_583 (g : Var) :
    (nb078AlphaDummy312 g) ≠ (nb078AlphaDummy313 g) := by
  simpa only [nb078AlphaDummy312, nb078AlphaDummy313] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_584 (g : Var) :
    (nb078AlphaDummy312 g) ≠ (nb078AlphaDummy314 g) := by
  simpa only [nb078AlphaDummy312, nb078AlphaDummy314] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_585 (g : Var) :
    (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy314 g) := by
  simpa only [nb078AlphaDummy313, nb078AlphaDummy314] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_586 :
    (nb078AlphaDummy321) ∉
      (((Class.cv (nb078AlphaDummy310))).fv ∪ ((Class.cv (nb078AlphaDummy310))).fv) :=
  by
  simpa only [nb078AlphaDummy321] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy310))).fv ∪ ((Class.cv (nb078AlphaDummy310))).fv)
      0

theorem nb078_fresh_587 :
    (nb078AlphaDummy317) ∉
      (((Class.cv (nb078AlphaDummy310))).fv ∪ ((Class.cv (nb078AlphaDummy311))).fv) :=
  by
  simpa only [nb078AlphaDummy317] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy310))).fv ∪ ((Class.cv (nb078AlphaDummy311))).fv)
      0

theorem nb078_fresh_588 :
    (nb078AlphaDummy323) ∉
      (((Class.cv (nb078AlphaDummy311))).fv ∪ ((Class.cv (nb078AlphaDummy311))).fv) :=
  by
  simpa only [nb078AlphaDummy323] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy311))).fv ∪ ((Class.cv (nb078AlphaDummy311))).fv)
      0

theorem nb078_fresh_589 (g : Var) :
    (nb078AlphaDummy322 g) ∉
      (((Class.cv (nb078AlphaDummy313 g))).fv ∪ ((Class.cv (nb078AlphaDummy313 g))).fv) :=
  by
  simpa only [nb078AlphaDummy322] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy313 g))).fv ∪ ((Class.cv (nb078AlphaDummy313 g))).fv)
      0

theorem nb078_fresh_590 (g : Var) :
    (nb078AlphaDummy318 g) ∉
      (((Class.cv (nb078AlphaDummy313 g))).fv ∪ ((Class.cv (nb078AlphaDummy314 g))).fv) :=
  by
  simpa only [nb078AlphaDummy318] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy313 g))).fv ∪ ((Class.cv (nb078AlphaDummy314 g))).fv)
      0

theorem nb078_fresh_591 (g : Var) :
    (nb078AlphaDummy324 g) ∉
      (((Class.cv (nb078AlphaDummy314 g))).fv ∪ ((Class.cv (nb078AlphaDummy314 g))).fv) :=
  by
  simpa only [nb078AlphaDummy324] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy314 g))).fv ∪ ((Class.cv (nb078AlphaDummy314 g))).fv)
      0

theorem nb078_fresh_592 :
    (nb078AlphaDummy339) ∉ (((Class.cv (nb078AlphaDummy332))).fv) := by
  simpa only [nb078AlphaDummy339] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy332))).fv) 0

theorem nb078_fresh_593 :
    (nb078AlphaDummy340) ∉ (((Class.cv (nb078AlphaDummy332))).fv) := by
  simpa only [nb078AlphaDummy340] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy332))).fv) 1

theorem nb078_distinct_594 : (nb078AlphaDummy339) ≠ (nb078AlphaDummy340) := by
  simpa only [nb078AlphaDummy339, nb078AlphaDummy340] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy332))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_595 (g : Var) :
    (nb078AlphaDummy341 g) ∉ (((Class.cv (nb078AlphaDummy334 g))).fv) := by
  simpa only [nb078AlphaDummy341] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy334 g))).fv) 0

theorem nb078_fresh_596 (g : Var) :
    (nb078AlphaDummy342 g) ∉ (((Class.cv (nb078AlphaDummy334 g))).fv) := by
  simpa only [nb078AlphaDummy342] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy334 g))).fv) 1

theorem nb078_distinct_597 (g : Var) :
    (nb078AlphaDummy341 g) ≠ (nb078AlphaDummy342 g) := by
  simpa only [nb078AlphaDummy341, nb078AlphaDummy342] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy334 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_598 :
    (nb078AlphaDummy345) ∉
      (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy345] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_599 :
    (nb078AlphaDummy346) ∉
      (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy346] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_600 :
    (nb078AlphaDummy347) ∉
      (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy347] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_601 : (nb078AlphaDummy345) ≠ (nb078AlphaDummy346) := by
  simpa only [nb078AlphaDummy345, nb078AlphaDummy346] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_602 : (nb078AlphaDummy345) ≠ (nb078AlphaDummy347) := by
  simpa only [nb078AlphaDummy345, nb078AlphaDummy347] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_603 : (nb078AlphaDummy346) ≠ (nb078AlphaDummy347) := by
  simpa only [nb078AlphaDummy346, nb078AlphaDummy347] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_604 (g : Var) :
    (nb078AlphaDummy348 g) ∉
      (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy348] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_605 (g : Var) :
    (nb078AlphaDummy349 g) ∉
      (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy349] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_606 (g : Var) :
    (nb078AlphaDummy350 g) ∉
      (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy350] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_607 (g : Var) :
    (nb078AlphaDummy348 g) ≠ (nb078AlphaDummy349 g) := by
  simpa only [nb078AlphaDummy348, nb078AlphaDummy349] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_608 (g : Var) :
    (nb078AlphaDummy348 g) ≠ (nb078AlphaDummy350 g) := by
  simpa only [nb078AlphaDummy348, nb078AlphaDummy350] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_609 (g : Var) :
    (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy350 g) := by
  simpa only [nb078AlphaDummy349, nb078AlphaDummy350] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_610 :
    (nb078AlphaDummy357) ∉
      (((Class.cv (nb078AlphaDummy346))).fv ∪ ((Class.cv (nb078AlphaDummy346))).fv) :=
  by
  simpa only [nb078AlphaDummy357] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy346))).fv ∪ ((Class.cv (nb078AlphaDummy346))).fv)
      0

theorem nb078_fresh_611 :
    (nb078AlphaDummy353) ∉
      (((Class.cv (nb078AlphaDummy346))).fv ∪ ((Class.cv (nb078AlphaDummy347))).fv) :=
  by
  simpa only [nb078AlphaDummy353] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy346))).fv ∪ ((Class.cv (nb078AlphaDummy347))).fv)
      0

theorem nb078_fresh_612 :
    (nb078AlphaDummy359) ∉
      (((Class.cv (nb078AlphaDummy347))).fv ∪ ((Class.cv (nb078AlphaDummy347))).fv) :=
  by
  simpa only [nb078AlphaDummy359] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy347))).fv ∪ ((Class.cv (nb078AlphaDummy347))).fv)
      0

theorem nb078_fresh_613 (g : Var) :
    (nb078AlphaDummy358 g) ∉
      (((Class.cv (nb078AlphaDummy349 g))).fv ∪ ((Class.cv (nb078AlphaDummy349 g))).fv) :=
  by
  simpa only [nb078AlphaDummy358] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy349 g))).fv ∪ ((Class.cv (nb078AlphaDummy349 g))).fv)
      0

theorem nb078_fresh_614 (g : Var) :
    (nb078AlphaDummy354 g) ∉
      (((Class.cv (nb078AlphaDummy349 g))).fv ∪ ((Class.cv (nb078AlphaDummy350 g))).fv) :=
  by
  simpa only [nb078AlphaDummy354] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy349 g))).fv ∪ ((Class.cv (nb078AlphaDummy350 g))).fv)
      0

theorem nb078_fresh_615 (g : Var) :
    (nb078AlphaDummy360 g) ∉
      (((Class.cv (nb078AlphaDummy350 g))).fv ∪ ((Class.cv (nb078AlphaDummy350 g))).fv) :=
  by
  simpa only [nb078AlphaDummy360] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy350 g))).fv ∪ ((Class.cv (nb078AlphaDummy350 g))).fv)
      0

theorem nb078_fresh_616 :
    (nb078AlphaDummy373) ∉
      (((Class.cv (nb078AlphaDummy367))).fv ∪ ((Class.cv (nb078AlphaDummy368))).fv) :=
  by
  simpa only [nb078AlphaDummy373] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy367))).fv ∪ ((Class.cv (nb078AlphaDummy368))).fv)
      0

theorem nb078_fresh_617 :
    (nb078AlphaDummy374) ∉
      (((Class.cv (nb078AlphaDummy367))).fv ∪ ((Class.cv (nb078AlphaDummy368))).fv) :=
  by
  simpa only [nb078AlphaDummy374] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy367))).fv ∪ ((Class.cv (nb078AlphaDummy368))).fv)
      1

theorem nb078_distinct_618 : (nb078AlphaDummy373) ≠ (nb078AlphaDummy374) := by
  simpa only [nb078AlphaDummy373, nb078AlphaDummy374] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy367))).fv ∪ ((Class.cv (nb078AlphaDummy368))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_619 :
    (nb078AlphaDummy409) ∉
      (((Class.cv (nb078AlphaDummy368))).fv ∪ ((Class.cv (nb078AlphaDummy367))).fv) :=
  by
  simpa only [nb078AlphaDummy409] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy368))).fv ∪ ((Class.cv (nb078AlphaDummy367))).fv)
      0

theorem nb078_fresh_620 :
    (nb078AlphaDummy410) ∉
      (((Class.cv (nb078AlphaDummy368))).fv ∪ ((Class.cv (nb078AlphaDummy367))).fv) :=
  by
  simpa only [nb078AlphaDummy410] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy368))).fv ∪ ((Class.cv (nb078AlphaDummy367))).fv)
      1

theorem nb078_distinct_621 : (nb078AlphaDummy409) ≠ (nb078AlphaDummy410) := by
  simpa only [nb078AlphaDummy409, nb078AlphaDummy410] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy368))).fv ∪ ((Class.cv (nb078AlphaDummy367))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_622 (g : Var) :
    (nb078AlphaDummy375 g) ∉
      (((Class.cv (nb078AlphaDummy369 g))).fv ∪ ((Class.cv (nb078AlphaDummy370 g))).fv) :=
  by
  simpa only [nb078AlphaDummy375] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy369 g))).fv ∪ ((Class.cv (nb078AlphaDummy370 g))).fv)
      0

theorem nb078_fresh_623 (g : Var) :
    (nb078AlphaDummy376 g) ∉
      (((Class.cv (nb078AlphaDummy369 g))).fv ∪ ((Class.cv (nb078AlphaDummy370 g))).fv) :=
  by
  simpa only [nb078AlphaDummy376] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy369 g))).fv ∪ ((Class.cv (nb078AlphaDummy370 g))).fv)
      1

theorem nb078_distinct_624 (g : Var) :
    (nb078AlphaDummy375 g) ≠ (nb078AlphaDummy376 g) := by
  simpa only [nb078AlphaDummy375, nb078AlphaDummy376] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy369 g))).fv ∪
        ((Class.cv (nb078AlphaDummy370 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_625 (g : Var) :
    (nb078AlphaDummy411 g) ∉
      (((Class.cv (nb078AlphaDummy370 g))).fv ∪ ((Class.cv (nb078AlphaDummy369 g))).fv) :=
  by
  simpa only [nb078AlphaDummy411] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy370 g))).fv ∪ ((Class.cv (nb078AlphaDummy369 g))).fv)
      0

theorem nb078_fresh_626 (g : Var) :
    (nb078AlphaDummy412 g) ∉
      (((Class.cv (nb078AlphaDummy370 g))).fv ∪ ((Class.cv (nb078AlphaDummy369 g))).fv) :=
  by
  simpa only [nb078AlphaDummy412] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy370 g))).fv ∪ ((Class.cv (nb078AlphaDummy369 g))).fv)
      1

theorem nb078_distinct_627 (g : Var) :
    (nb078AlphaDummy411 g) ≠ (nb078AlphaDummy412 g) := by
  simpa only [nb078AlphaDummy411, nb078AlphaDummy412] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy370 g))).fv ∪
        ((Class.cv (nb078AlphaDummy369 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_628 :
    (nb078AlphaDummy381) ∉ (((Class.cv (nb078AlphaDummy374))).fv) := by
  simpa only [nb078AlphaDummy381] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy374))).fv) 0

theorem nb078_fresh_629 :
    (nb078AlphaDummy382) ∉ (((Class.cv (nb078AlphaDummy374))).fv) := by
  simpa only [nb078AlphaDummy382] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy374))).fv) 1

theorem nb078_distinct_630 : (nb078AlphaDummy381) ≠ (nb078AlphaDummy382) := by
  simpa only [nb078AlphaDummy381, nb078AlphaDummy382] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy374))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_631 (g : Var) :
    (nb078AlphaDummy383 g) ∉ (((Class.cv (nb078AlphaDummy376 g))).fv) := by
  simpa only [nb078AlphaDummy383] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy376 g))).fv) 0

theorem nb078_fresh_632 (g : Var) :
    (nb078AlphaDummy384 g) ∉ (((Class.cv (nb078AlphaDummy376 g))).fv) := by
  simpa only [nb078AlphaDummy384] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy376 g))).fv) 1

theorem nb078_distinct_633 (g : Var) :
    (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy384 g) := by
  simpa only [nb078AlphaDummy383, nb078AlphaDummy384] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy376 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_634 :
    (nb078AlphaDummy387) ∉
      (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy387] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_635 :
    (nb078AlphaDummy388) ∉
      (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy388] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_636 :
    (nb078AlphaDummy389) ∉
      (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy389] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_637 : (nb078AlphaDummy387) ≠ (nb078AlphaDummy388) := by
  simpa only [nb078AlphaDummy387, nb078AlphaDummy388] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_638 : (nb078AlphaDummy387) ≠ (nb078AlphaDummy389) := by
  simpa only [nb078AlphaDummy387, nb078AlphaDummy389] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_639 : (nb078AlphaDummy388) ≠ (nb078AlphaDummy389) := by
  simpa only [nb078AlphaDummy388, nb078AlphaDummy389] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_640 (g : Var) :
    (nb078AlphaDummy390 g) ∉
      (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy390] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_641 (g : Var) :
    (nb078AlphaDummy391 g) ∉
      (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy391] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_642 (g : Var) :
    (nb078AlphaDummy392 g) ∉
      (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy392] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_643 (g : Var) :
    (nb078AlphaDummy390 g) ≠ (nb078AlphaDummy391 g) := by
  simpa only [nb078AlphaDummy390, nb078AlphaDummy391] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_644 (g : Var) :
    (nb078AlphaDummy390 g) ≠ (nb078AlphaDummy392 g) := by
  simpa only [nb078AlphaDummy390, nb078AlphaDummy392] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_645 (g : Var) :
    (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy392 g) := by
  simpa only [nb078AlphaDummy391, nb078AlphaDummy392] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_646 :
    (nb078AlphaDummy399) ∉
      (((Class.cv (nb078AlphaDummy388))).fv ∪ ((Class.cv (nb078AlphaDummy388))).fv) :=
  by
  simpa only [nb078AlphaDummy399] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy388))).fv ∪ ((Class.cv (nb078AlphaDummy388))).fv)
      0

theorem nb078_fresh_647 :
    (nb078AlphaDummy395) ∉
      (((Class.cv (nb078AlphaDummy388))).fv ∪ ((Class.cv (nb078AlphaDummy389))).fv) :=
  by
  simpa only [nb078AlphaDummy395] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy388))).fv ∪ ((Class.cv (nb078AlphaDummy389))).fv)
      0

theorem nb078_fresh_648 :
    (nb078AlphaDummy401) ∉
      (((Class.cv (nb078AlphaDummy389))).fv ∪ ((Class.cv (nb078AlphaDummy389))).fv) :=
  by
  simpa only [nb078AlphaDummy401] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy389))).fv ∪ ((Class.cv (nb078AlphaDummy389))).fv)
      0

theorem nb078_fresh_649 (g : Var) :
    (nb078AlphaDummy400 g) ∉
      (((Class.cv (nb078AlphaDummy391 g))).fv ∪ ((Class.cv (nb078AlphaDummy391 g))).fv) :=
  by
  simpa only [nb078AlphaDummy400] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy391 g))).fv ∪ ((Class.cv (nb078AlphaDummy391 g))).fv)
      0

theorem nb078_fresh_650 (g : Var) :
    (nb078AlphaDummy396 g) ∉
      (((Class.cv (nb078AlphaDummy391 g))).fv ∪ ((Class.cv (nb078AlphaDummy392 g))).fv) :=
  by
  simpa only [nb078AlphaDummy396] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy391 g))).fv ∪ ((Class.cv (nb078AlphaDummy392 g))).fv)
      0

theorem nb078_fresh_651 (g : Var) :
    (nb078AlphaDummy402 g) ∉
      (((Class.cv (nb078AlphaDummy392 g))).fv ∪ ((Class.cv (nb078AlphaDummy392 g))).fv) :=
  by
  simpa only [nb078AlphaDummy402] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy392 g))).fv ∪ ((Class.cv (nb078AlphaDummy392 g))).fv)
      0

theorem nb078_fresh_652 :
    (nb078AlphaDummy417) ∉ (((Class.cv (nb078AlphaDummy410))).fv) := by
  simpa only [nb078AlphaDummy417] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy410))).fv) 0

theorem nb078_fresh_653 :
    (nb078AlphaDummy418) ∉ (((Class.cv (nb078AlphaDummy410))).fv) := by
  simpa only [nb078AlphaDummy418] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy410))).fv) 1

theorem nb078_distinct_654 : (nb078AlphaDummy417) ≠ (nb078AlphaDummy418) := by
  simpa only [nb078AlphaDummy417, nb078AlphaDummy418] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy410))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_655 (g : Var) :
    (nb078AlphaDummy419 g) ∉ (((Class.cv (nb078AlphaDummy412 g))).fv) := by
  simpa only [nb078AlphaDummy419] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy412 g))).fv) 0

theorem nb078_fresh_656 (g : Var) :
    (nb078AlphaDummy420 g) ∉ (((Class.cv (nb078AlphaDummy412 g))).fv) := by
  simpa only [nb078AlphaDummy420] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy412 g))).fv) 1

theorem nb078_distinct_657 (g : Var) :
    (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy420 g) := by
  simpa only [nb078AlphaDummy419, nb078AlphaDummy420] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy412 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_658 :
    (nb078AlphaDummy423) ∉
      (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy423] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_659 :
    (nb078AlphaDummy424) ∉
      (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy424] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_660 :
    (nb078AlphaDummy425) ∉
      (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy425] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_661 : (nb078AlphaDummy423) ≠ (nb078AlphaDummy424) := by
  simpa only [nb078AlphaDummy423, nb078AlphaDummy424] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_662 : (nb078AlphaDummy423) ≠ (nb078AlphaDummy425) := by
  simpa only [nb078AlphaDummy423, nb078AlphaDummy425] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_663 : (nb078AlphaDummy424) ≠ (nb078AlphaDummy425) := by
  simpa only [nb078AlphaDummy424, nb078AlphaDummy425] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_664 (g : Var) :
    (nb078AlphaDummy426 g) ∉
      (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy426] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_665 (g : Var) :
    (nb078AlphaDummy427 g) ∉
      (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy427] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_666 (g : Var) :
    (nb078AlphaDummy428 g) ∉
      (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy428] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_667 (g : Var) :
    (nb078AlphaDummy426 g) ≠ (nb078AlphaDummy427 g) := by
  simpa only [nb078AlphaDummy426, nb078AlphaDummy427] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_668 (g : Var) :
    (nb078AlphaDummy426 g) ≠ (nb078AlphaDummy428 g) := by
  simpa only [nb078AlphaDummy426, nb078AlphaDummy428] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_669 (g : Var) :
    (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy428 g) := by
  simpa only [nb078AlphaDummy427, nb078AlphaDummy428] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_670 :
    (nb078AlphaDummy435) ∉
      (((Class.cv (nb078AlphaDummy424))).fv ∪ ((Class.cv (nb078AlphaDummy424))).fv) :=
  by
  simpa only [nb078AlphaDummy435] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy424))).fv ∪ ((Class.cv (nb078AlphaDummy424))).fv)
      0

theorem nb078_fresh_671 :
    (nb078AlphaDummy431) ∉
      (((Class.cv (nb078AlphaDummy424))).fv ∪ ((Class.cv (nb078AlphaDummy425))).fv) :=
  by
  simpa only [nb078AlphaDummy431] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy424))).fv ∪ ((Class.cv (nb078AlphaDummy425))).fv)
      0

theorem nb078_fresh_672 :
    (nb078AlphaDummy437) ∉
      (((Class.cv (nb078AlphaDummy425))).fv ∪ ((Class.cv (nb078AlphaDummy425))).fv) :=
  by
  simpa only [nb078AlphaDummy437] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy425))).fv ∪ ((Class.cv (nb078AlphaDummy425))).fv)
      0

theorem nb078_fresh_673 (g : Var) :
    (nb078AlphaDummy436 g) ∉
      (((Class.cv (nb078AlphaDummy427 g))).fv ∪ ((Class.cv (nb078AlphaDummy427 g))).fv) :=
  by
  simpa only [nb078AlphaDummy436] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy427 g))).fv ∪ ((Class.cv (nb078AlphaDummy427 g))).fv)
      0

theorem nb078_fresh_674 (g : Var) :
    (nb078AlphaDummy432 g) ∉
      (((Class.cv (nb078AlphaDummy427 g))).fv ∪ ((Class.cv (nb078AlphaDummy428 g))).fv) :=
  by
  simpa only [nb078AlphaDummy432] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy427 g))).fv ∪ ((Class.cv (nb078AlphaDummy428 g))).fv)
      0

theorem nb078_fresh_675 (g : Var) :
    (nb078AlphaDummy438 g) ∉
      (((Class.cv (nb078AlphaDummy428 g))).fv ∪ ((Class.cv (nb078AlphaDummy428 g))).fv) :=
  by
  simpa only [nb078AlphaDummy438] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy428 g))).fv ∪ ((Class.cv (nb078AlphaDummy428 g))).fv)
      0

theorem nb078_fresh_676 :
    (nb078AlphaDummy453) ∉ (((Class.cv (nb078AlphaDummy446))).fv) := by
  simpa only [nb078AlphaDummy453] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy446))).fv) 0

theorem nb078_fresh_677 :
    (nb078AlphaDummy454) ∉ (((Class.cv (nb078AlphaDummy446))).fv) := by
  simpa only [nb078AlphaDummy454] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy446))).fv) 1

theorem nb078_distinct_678 : (nb078AlphaDummy453) ≠ (nb078AlphaDummy454) := by
  simpa only [nb078AlphaDummy453, nb078AlphaDummy454] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy446))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_679 (g : Var) :
    (nb078AlphaDummy455 g) ∉ (((Class.cv (nb078AlphaDummy448 g))).fv) := by
  simpa only [nb078AlphaDummy455] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy448 g))).fv) 0

theorem nb078_fresh_680 (g : Var) :
    (nb078AlphaDummy456 g) ∉ (((Class.cv (nb078AlphaDummy448 g))).fv) := by
  simpa only [nb078AlphaDummy456] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy448 g))).fv) 1

theorem nb078_distinct_681 (g : Var) :
    (nb078AlphaDummy455 g) ≠ (nb078AlphaDummy456 g) := by
  simpa only [nb078AlphaDummy455, nb078AlphaDummy456] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy448 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_682 :
    (nb078AlphaDummy459) ∉
      (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy459] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_683 :
    (nb078AlphaDummy460) ∉
      (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy460] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_684 :
    (nb078AlphaDummy461) ∉
      (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy461] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_685 : (nb078AlphaDummy459) ≠ (nb078AlphaDummy460) := by
  simpa only [nb078AlphaDummy459, nb078AlphaDummy460] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_686 : (nb078AlphaDummy459) ≠ (nb078AlphaDummy461) := by
  simpa only [nb078AlphaDummy459, nb078AlphaDummy461] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_687 : (nb078AlphaDummy460) ≠ (nb078AlphaDummy461) := by
  simpa only [nb078AlphaDummy460, nb078AlphaDummy461] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_688 (g : Var) :
    (nb078AlphaDummy462 g) ∉
      (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy462] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_689 (g : Var) :
    (nb078AlphaDummy463 g) ∉
      (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy463] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_690 (g : Var) :
    (nb078AlphaDummy464 g) ∉
      (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy464] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_691 (g : Var) :
    (nb078AlphaDummy462 g) ≠ (nb078AlphaDummy463 g) := by
  simpa only [nb078AlphaDummy462, nb078AlphaDummy463] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_692 (g : Var) :
    (nb078AlphaDummy462 g) ≠ (nb078AlphaDummy464 g) := by
  simpa only [nb078AlphaDummy462, nb078AlphaDummy464] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_693 (g : Var) :
    (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy464 g) := by
  simpa only [nb078AlphaDummy463, nb078AlphaDummy464] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_694 :
    (nb078AlphaDummy471) ∉
      (((Class.cv (nb078AlphaDummy460))).fv ∪ ((Class.cv (nb078AlphaDummy460))).fv) :=
  by
  simpa only [nb078AlphaDummy471] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy460))).fv ∪ ((Class.cv (nb078AlphaDummy460))).fv)
      0

theorem nb078_fresh_695 :
    (nb078AlphaDummy467) ∉
      (((Class.cv (nb078AlphaDummy460))).fv ∪ ((Class.cv (nb078AlphaDummy461))).fv) :=
  by
  simpa only [nb078AlphaDummy467] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy460))).fv ∪ ((Class.cv (nb078AlphaDummy461))).fv)
      0

theorem nb078_fresh_696 :
    (nb078AlphaDummy473) ∉
      (((Class.cv (nb078AlphaDummy461))).fv ∪ ((Class.cv (nb078AlphaDummy461))).fv) :=
  by
  simpa only [nb078AlphaDummy473] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy461))).fv ∪ ((Class.cv (nb078AlphaDummy461))).fv)
      0

theorem nb078_fresh_697 (g : Var) :
    (nb078AlphaDummy472 g) ∉
      (((Class.cv (nb078AlphaDummy463 g))).fv ∪ ((Class.cv (nb078AlphaDummy463 g))).fv) :=
  by
  simpa only [nb078AlphaDummy472] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy463 g))).fv ∪ ((Class.cv (nb078AlphaDummy463 g))).fv)
      0

theorem nb078_fresh_698 (g : Var) :
    (nb078AlphaDummy468 g) ∉
      (((Class.cv (nb078AlphaDummy463 g))).fv ∪ ((Class.cv (nb078AlphaDummy464 g))).fv) :=
  by
  simpa only [nb078AlphaDummy468] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy463 g))).fv ∪ ((Class.cv (nb078AlphaDummy464 g))).fv)
      0

theorem nb078_fresh_699 (g : Var) :
    (nb078AlphaDummy474 g) ∉
      (((Class.cv (nb078AlphaDummy464 g))).fv ∪ ((Class.cv (nb078AlphaDummy464 g))).fv) :=
  by
  simpa only [nb078AlphaDummy474] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy464 g))).fv ∪ ((Class.cv (nb078AlphaDummy464 g))).fv)
      0

theorem nb078_fresh_700 :
    (nb078AlphaDummy485) ∉
      (((Class.cv (nb078AlphaDummy482))).fv ∪ ((Class.cv (nb078AlphaDummy481))).fv) :=
  by
  simpa only [nb078AlphaDummy485] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy482))).fv ∪ ((Class.cv (nb078AlphaDummy481))).fv)
      0

theorem nb078_fresh_701 :
    (nb078AlphaDummy486) ∉
      (((Class.cv (nb078AlphaDummy482))).fv ∪ ((Class.cv (nb078AlphaDummy481))).fv) :=
  by
  simpa only [nb078AlphaDummy486] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy482))).fv ∪ ((Class.cv (nb078AlphaDummy481))).fv)
      1

theorem nb078_distinct_702 : (nb078AlphaDummy485) ≠ (nb078AlphaDummy486) := by
  simpa only [nb078AlphaDummy485, nb078AlphaDummy486] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy482))).fv ∪ ((Class.cv (nb078AlphaDummy481))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_703 (g : Var) :
    (nb078AlphaDummy487 g) ∉
      (((Class.cv (nb078AlphaDummy484 g))).fv ∪ ((Class.cv (nb078AlphaDummy483 g))).fv) :=
  by
  simpa only [nb078AlphaDummy487] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy484 g))).fv ∪ ((Class.cv (nb078AlphaDummy483 g))).fv)
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
    (nb078AlphaDummy488 g) ∉
      (((Class.cv (nb078AlphaDummy484 g))).fv ∪ ((Class.cv (nb078AlphaDummy483 g))).fv) :=
  by
  simpa only [nb078AlphaDummy488] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy484 g))).fv ∪ ((Class.cv (nb078AlphaDummy483 g))).fv)
      1

theorem nb078_distinct_705 (g : Var) :
    (nb078AlphaDummy487 g) ≠ (nb078AlphaDummy488 g) := by
  simpa only [nb078AlphaDummy487, nb078AlphaDummy488] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy484 g))).fv ∪
        ((Class.cv (nb078AlphaDummy483 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_706 :
    (nb078AlphaDummy493) ∉ (((Class.cv (nb078AlphaDummy486))).fv) := by
  simpa only [nb078AlphaDummy493] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy486))).fv) 0

theorem nb078_fresh_707 :
    (nb078AlphaDummy494) ∉ (((Class.cv (nb078AlphaDummy486))).fv) := by
  simpa only [nb078AlphaDummy494] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy486))).fv) 1

theorem nb078_distinct_708 : (nb078AlphaDummy493) ≠ (nb078AlphaDummy494) := by
  simpa only [nb078AlphaDummy493, nb078AlphaDummy494] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy486))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_709 (g : Var) :
    (nb078AlphaDummy495 g) ∉ (((Class.cv (nb078AlphaDummy488 g))).fv) := by
  simpa only [nb078AlphaDummy495] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy488 g))).fv) 0

theorem nb078_fresh_710 (g : Var) :
    (nb078AlphaDummy496 g) ∉ (((Class.cv (nb078AlphaDummy488 g))).fv) := by
  simpa only [nb078AlphaDummy496] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy488 g))).fv) 1

theorem nb078_distinct_711 (g : Var) :
    (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy496 g) := by
  simpa only [nb078AlphaDummy495, nb078AlphaDummy496] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy488 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_712 :
    (nb078AlphaDummy499) ∉
      (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy499] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_713 :
    (nb078AlphaDummy500) ∉
      (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy500] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_714 :
    (nb078AlphaDummy501) ∉
      (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy501] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_715 : (nb078AlphaDummy499) ≠ (nb078AlphaDummy500) := by
  simpa only [nb078AlphaDummy499, nb078AlphaDummy500] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_716 : (nb078AlphaDummy499) ≠ (nb078AlphaDummy501) := by
  simpa only [nb078AlphaDummy499, nb078AlphaDummy501] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_717 : (nb078AlphaDummy500) ≠ (nb078AlphaDummy501) := by
  simpa only [nb078AlphaDummy500, nb078AlphaDummy501] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_718 (g : Var) :
    (nb078AlphaDummy502 g) ∉
      (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy502] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_719 (g : Var) :
    (nb078AlphaDummy503 g) ∉
      (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy503] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_720 (g : Var) :
    (nb078AlphaDummy504 g) ∉
      (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy504] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_721 (g : Var) :
    (nb078AlphaDummy502 g) ≠ (nb078AlphaDummy503 g) := by
  simpa only [nb078AlphaDummy502, nb078AlphaDummy503] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_722 (g : Var) :
    (nb078AlphaDummy502 g) ≠ (nb078AlphaDummy504 g) := by
  simpa only [nb078AlphaDummy502, nb078AlphaDummy504] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_723 (g : Var) :
    (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy504 g) := by
  simpa only [nb078AlphaDummy503, nb078AlphaDummy504] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_724 :
    (nb078AlphaDummy511) ∉
      (((Class.cv (nb078AlphaDummy500))).fv ∪ ((Class.cv (nb078AlphaDummy500))).fv) :=
  by
  simpa only [nb078AlphaDummy511] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy500))).fv ∪ ((Class.cv (nb078AlphaDummy500))).fv)
      0

theorem nb078_fresh_725 :
    (nb078AlphaDummy507) ∉
      (((Class.cv (nb078AlphaDummy500))).fv ∪ ((Class.cv (nb078AlphaDummy501))).fv) :=
  by
  simpa only [nb078AlphaDummy507] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy500))).fv ∪ ((Class.cv (nb078AlphaDummy501))).fv)
      0

theorem nb078_fresh_726 :
    (nb078AlphaDummy513) ∉
      (((Class.cv (nb078AlphaDummy501))).fv ∪ ((Class.cv (nb078AlphaDummy501))).fv) :=
  by
  simpa only [nb078AlphaDummy513] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy501))).fv ∪ ((Class.cv (nb078AlphaDummy501))).fv)
      0

theorem nb078_fresh_727 (g : Var) :
    (nb078AlphaDummy512 g) ∉
      (((Class.cv (nb078AlphaDummy503 g))).fv ∪ ((Class.cv (nb078AlphaDummy503 g))).fv) :=
  by
  simpa only [nb078AlphaDummy512] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy503 g))).fv ∪ ((Class.cv (nb078AlphaDummy503 g))).fv)
      0

theorem nb078_fresh_728 (g : Var) :
    (nb078AlphaDummy508 g) ∉
      (((Class.cv (nb078AlphaDummy503 g))).fv ∪ ((Class.cv (nb078AlphaDummy504 g))).fv) :=
  by
  simpa only [nb078AlphaDummy508] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy503 g))).fv ∪ ((Class.cv (nb078AlphaDummy504 g))).fv)
      0

theorem nb078_fresh_729 (g : Var) :
    (nb078AlphaDummy514 g) ∉
      (((Class.cv (nb078AlphaDummy504 g))).fv ∪ ((Class.cv (nb078AlphaDummy504 g))).fv) :=
  by
  simpa only [nb078AlphaDummy514] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy504 g))).fv ∪ ((Class.cv (nb078AlphaDummy504 g))).fv)
      0

theorem nb078_fresh_730 :
    (nb078AlphaDummy529) ∉
      (((Class.cv (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv) :=
  by
  simpa only [nb078AlphaDummy529] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv)
      0

theorem nb078_fresh_731 :
    (nb078AlphaDummy530) ∉
      (((Class.cv (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv) :=
  by
  simpa only [nb078AlphaDummy530] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv)
      1

theorem nb078_distinct_732 : (nb078AlphaDummy529) ≠ (nb078AlphaDummy530) := by
  simpa only [nb078AlphaDummy529, nb078AlphaDummy530] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_733 (g : Var) :
    (nb078AlphaDummy531 g) ∉
      (((Class.cv (nb078AlphaDummy528 g))).fv ∪ ((Class.cv (nb078AlphaDummy527 g))).fv) :=
  by
  simpa only [nb078AlphaDummy531] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy528 g))).fv ∪ ((Class.cv (nb078AlphaDummy527 g))).fv)
      0

theorem nb078_fresh_734 (g : Var) :
    (nb078AlphaDummy532 g) ∉
      (((Class.cv (nb078AlphaDummy528 g))).fv ∪ ((Class.cv (nb078AlphaDummy527 g))).fv) :=
  by
  simpa only [nb078AlphaDummy532] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy528 g))).fv ∪ ((Class.cv (nb078AlphaDummy527 g))).fv)
      1

theorem nb078_distinct_735 (g : Var) :
    (nb078AlphaDummy531 g) ≠ (nb078AlphaDummy532 g) := by
  simpa only [nb078AlphaDummy531, nb078AlphaDummy532] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy528 g))).fv ∪
        ((Class.cv (nb078AlphaDummy527 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_736 :
    (nb078AlphaDummy537) ∉ (((Class.cv (nb078AlphaDummy530))).fv) := by
  simpa only [nb078AlphaDummy537] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy530))).fv) 0

theorem nb078_fresh_737 :
    (nb078AlphaDummy538) ∉ (((Class.cv (nb078AlphaDummy530))).fv) := by
  simpa only [nb078AlphaDummy538] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy530))).fv) 1

theorem nb078_distinct_738 : (nb078AlphaDummy537) ≠ (nb078AlphaDummy538) := by
  simpa only [nb078AlphaDummy537, nb078AlphaDummy538] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy530))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_739 (g : Var) :
    (nb078AlphaDummy539 g) ∉ (((Class.cv (nb078AlphaDummy532 g))).fv) := by
  simpa only [nb078AlphaDummy539] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy532 g))).fv) 0

theorem nb078_fresh_740 (g : Var) :
    (nb078AlphaDummy540 g) ∉ (((Class.cv (nb078AlphaDummy532 g))).fv) := by
  simpa only [nb078AlphaDummy540] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy532 g))).fv) 1

theorem nb078_distinct_741 (g : Var) :
    (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy540 g) := by
  simpa only [nb078AlphaDummy539, nb078AlphaDummy540] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy532 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_742 :
    (nb078AlphaDummy543) ∉
      (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy543] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_743 :
    (nb078AlphaDummy544) ∉
      (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy544] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_744 :
    (nb078AlphaDummy545) ∉
      (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy545] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_745 : (nb078AlphaDummy543) ≠ (nb078AlphaDummy544) := by
  simpa only [nb078AlphaDummy543, nb078AlphaDummy544] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_746 : (nb078AlphaDummy543) ≠ (nb078AlphaDummy545) := by
  simpa only [nb078AlphaDummy543, nb078AlphaDummy545] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_747 : (nb078AlphaDummy544) ≠ (nb078AlphaDummy545) := by
  simpa only [nb078AlphaDummy544, nb078AlphaDummy545] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_748 (g : Var) :
    (nb078AlphaDummy546 g) ∉
      (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy546] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_749 (g : Var) :
    (nb078AlphaDummy547 g) ∉
      (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy547] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_750 (g : Var) :
    (nb078AlphaDummy548 g) ∉
      (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy548] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_751 (g : Var) :
    (nb078AlphaDummy546 g) ≠ (nb078AlphaDummy547 g) := by
  simpa only [nb078AlphaDummy546, nb078AlphaDummy547] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_752 (g : Var) :
    (nb078AlphaDummy546 g) ≠ (nb078AlphaDummy548 g) := by
  simpa only [nb078AlphaDummy546, nb078AlphaDummy548] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_753 (g : Var) :
    (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy548 g) := by
  simpa only [nb078AlphaDummy547, nb078AlphaDummy548] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_754 :
    (nb078AlphaDummy555) ∉
      (((Class.cv (nb078AlphaDummy544))).fv ∪ ((Class.cv (nb078AlphaDummy544))).fv) :=
  by
  simpa only [nb078AlphaDummy555] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy544))).fv ∪ ((Class.cv (nb078AlphaDummy544))).fv)
      0

theorem nb078_fresh_755 :
    (nb078AlphaDummy551) ∉
      (((Class.cv (nb078AlphaDummy544))).fv ∪ ((Class.cv (nb078AlphaDummy545))).fv) :=
  by
  simpa only [nb078AlphaDummy551] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy544))).fv ∪ ((Class.cv (nb078AlphaDummy545))).fv)
      0

theorem nb078_fresh_756 :
    (nb078AlphaDummy557) ∉
      (((Class.cv (nb078AlphaDummy545))).fv ∪ ((Class.cv (nb078AlphaDummy545))).fv) :=
  by
  simpa only [nb078AlphaDummy557] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy545))).fv ∪ ((Class.cv (nb078AlphaDummy545))).fv)
      0

theorem nb078_fresh_757 (g : Var) :
    (nb078AlphaDummy556 g) ∉
      (((Class.cv (nb078AlphaDummy547 g))).fv ∪ ((Class.cv (nb078AlphaDummy547 g))).fv) :=
  by
  simpa only [nb078AlphaDummy556] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy547 g))).fv ∪ ((Class.cv (nb078AlphaDummy547 g))).fv)
      0

theorem nb078_fresh_758 (g : Var) :
    (nb078AlphaDummy552 g) ∉
      (((Class.cv (nb078AlphaDummy547 g))).fv ∪ ((Class.cv (nb078AlphaDummy548 g))).fv) :=
  by
  simpa only [nb078AlphaDummy552] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy547 g))).fv ∪ ((Class.cv (nb078AlphaDummy548 g))).fv)
      0

theorem nb078_fresh_759 (g : Var) :
    (nb078AlphaDummy558 g) ∉
      (((Class.cv (nb078AlphaDummy548 g))).fv ∪ ((Class.cv (nb078AlphaDummy548 g))).fv) :=
  by
  simpa only [nb078AlphaDummy558] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy548 g))).fv ∪ ((Class.cv (nb078AlphaDummy548 g))).fv)
      0

theorem nb078_fresh_760 :
    (nb078AlphaDummy577) ∉
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) :=
  by
  simpa only [nb078AlphaDummy577] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv)
      0

theorem nb078_fresh_761 :
    (nb078AlphaDummy578) ∉
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) :=
  by
  simpa only [nb078AlphaDummy578] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv)
      1

theorem nb078_distinct_762 : (nb078AlphaDummy577) ≠ (nb078AlphaDummy578) := by
  simpa only [nb078AlphaDummy577, nb078AlphaDummy578] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_763 :
    (nb078AlphaDummy613) ∉
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy571))).fv) :=
  by
  simpa only [nb078AlphaDummy613] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy571))).fv)
      0

theorem nb078_fresh_764 :
    (nb078AlphaDummy614) ∉
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy571))).fv) :=
  by
  simpa only [nb078AlphaDummy614] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy571))).fv)
      1

theorem nb078_distinct_765 : (nb078AlphaDummy613) ≠ (nb078AlphaDummy614) := by
  simpa only [nb078AlphaDummy613, nb078AlphaDummy614] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy571))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_766 :
    (nb078AlphaDummy727) ∉
      (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) :=
  by
  simpa only [nb078AlphaDummy727] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv)
      0

theorem nb078_fresh_767 :
    (nb078AlphaDummy728) ∉
      (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) :=
  by
  simpa only [nb078AlphaDummy728] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv)
      1

theorem nb078_distinct_768 : (nb078AlphaDummy727) ≠ (nb078AlphaDummy728) := by
  simpa only [nb078AlphaDummy727, nb078AlphaDummy728] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_769 (g : Var) :
    (nb078AlphaDummy579 g) ∉
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv) :=
  by
  simpa only [nb078AlphaDummy579] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv)
      0

theorem nb078_fresh_770 (g : Var) :
    (nb078AlphaDummy580 g) ∉
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv) :=
  by
  simpa only [nb078AlphaDummy580] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv)
      1

theorem nb078_distinct_771 (g : Var) :
    (nb078AlphaDummy579 g) ≠ (nb078AlphaDummy580 g) := by
  simpa only [nb078AlphaDummy579, nb078AlphaDummy580] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy572 g))).fv ∪
        ((Class.cv (nb078AlphaDummy573 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_772 (g : Var) :
    (nb078AlphaDummy615 g) ∉
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy574 g))).fv) :=
  by
  simpa only [nb078AlphaDummy615] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy574 g))).fv)
      0

theorem nb078_fresh_773 (g : Var) :
    (nb078AlphaDummy616 g) ∉
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy574 g))).fv) :=
  by
  simpa only [nb078AlphaDummy616] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy572 g))).fv ∪ ((Class.cv (nb078AlphaDummy574 g))).fv)
      1

theorem nb078_distinct_774 (g : Var) :
    (nb078AlphaDummy615 g) ≠ (nb078AlphaDummy616 g) := by
  simpa only [nb078AlphaDummy615, nb078AlphaDummy616] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy572 g))).fv ∪
        ((Class.cv (nb078AlphaDummy574 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_775 (g : Var) :
    (nb078AlphaDummy729 g) ∉
      (((Class.cv (nb078AlphaDummy574 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv) :=
  by
  simpa only [nb078AlphaDummy729] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy574 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv)
      0

theorem nb078_fresh_776 (g : Var) :
    (nb078AlphaDummy730 g) ∉
      (((Class.cv (nb078AlphaDummy574 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv) :=
  by
  simpa only [nb078AlphaDummy730] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy574 g))).fv ∪ ((Class.cv (nb078AlphaDummy573 g))).fv)
      1

theorem nb078_distinct_777 (g : Var) :
    (nb078AlphaDummy729 g) ≠ (nb078AlphaDummy730 g) := by
  simpa only [nb078AlphaDummy729, nb078AlphaDummy730] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy574 g))).fv ∪
        ((Class.cv (nb078AlphaDummy573 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_778 :
    (nb078AlphaDummy585) ∉ (((Class.cv (nb078AlphaDummy578))).fv) := by
  simpa only [nb078AlphaDummy585] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy578))).fv) 0

theorem nb078_fresh_779 :
    (nb078AlphaDummy586) ∉ (((Class.cv (nb078AlphaDummy578))).fv) := by
  simpa only [nb078AlphaDummy586] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy578))).fv) 1

theorem nb078_distinct_780 : (nb078AlphaDummy585) ≠ (nb078AlphaDummy586) := by
  simpa only [nb078AlphaDummy585, nb078AlphaDummy586] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy578))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_781 (g : Var) :
    (nb078AlphaDummy587 g) ∉ (((Class.cv (nb078AlphaDummy580 g))).fv) := by
  simpa only [nb078AlphaDummy587] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy580 g))).fv) 0

theorem nb078_fresh_782 (g : Var) :
    (nb078AlphaDummy588 g) ∉ (((Class.cv (nb078AlphaDummy580 g))).fv) := by
  simpa only [nb078AlphaDummy588] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy580 g))).fv) 1

theorem nb078_distinct_783 (g : Var) :
    (nb078AlphaDummy587 g) ≠ (nb078AlphaDummy588 g) := by
  simpa only [nb078AlphaDummy587, nb078AlphaDummy588] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy580 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_784 :
    (nb078AlphaDummy591) ∉
      (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy591] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_785 :
    (nb078AlphaDummy592) ∉
      (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy592] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_786 :
    (nb078AlphaDummy593) ∉
      (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy593] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_787 : (nb078AlphaDummy591) ≠ (nb078AlphaDummy592) := by
  simpa only [nb078AlphaDummy591, nb078AlphaDummy592] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_788 : (nb078AlphaDummy591) ≠ (nb078AlphaDummy593) := by
  simpa only [nb078AlphaDummy591, nb078AlphaDummy593] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_789 : (nb078AlphaDummy592) ≠ (nb078AlphaDummy593) := by
  simpa only [nb078AlphaDummy592, nb078AlphaDummy593] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_790 (g : Var) :
    (nb078AlphaDummy594 g) ∉
      (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy594] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_791 (g : Var) :
    (nb078AlphaDummy595 g) ∉
      (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy595] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_792 (g : Var) :
    (nb078AlphaDummy596 g) ∉
      (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy596] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_793 (g : Var) :
    (nb078AlphaDummy594 g) ≠ (nb078AlphaDummy595 g) := by
  simpa only [nb078AlphaDummy594, nb078AlphaDummy595] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_794 (g : Var) :
    (nb078AlphaDummy594 g) ≠ (nb078AlphaDummy596 g) := by
  simpa only [nb078AlphaDummy594, nb078AlphaDummy596] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_795 (g : Var) :
    (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy596 g) := by
  simpa only [nb078AlphaDummy595, nb078AlphaDummy596] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_796 :
    (nb078AlphaDummy603) ∉
      (((Class.cv (nb078AlphaDummy592))).fv ∪ ((Class.cv (nb078AlphaDummy592))).fv) :=
  by
  simpa only [nb078AlphaDummy603] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy592))).fv ∪ ((Class.cv (nb078AlphaDummy592))).fv)
      0

theorem nb078_fresh_797 :
    (nb078AlphaDummy599) ∉
      (((Class.cv (nb078AlphaDummy592))).fv ∪ ((Class.cv (nb078AlphaDummy593))).fv) :=
  by
  simpa only [nb078AlphaDummy599] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy592))).fv ∪ ((Class.cv (nb078AlphaDummy593))).fv)
      0

theorem nb078_fresh_798 :
    (nb078AlphaDummy605) ∉
      (((Class.cv (nb078AlphaDummy593))).fv ∪ ((Class.cv (nb078AlphaDummy593))).fv) :=
  by
  simpa only [nb078AlphaDummy605] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy593))).fv ∪ ((Class.cv (nb078AlphaDummy593))).fv)
      0

theorem nb078_fresh_799 (g : Var) :
    (nb078AlphaDummy604 g) ∉
      (((Class.cv (nb078AlphaDummy595 g))).fv ∪ ((Class.cv (nb078AlphaDummy595 g))).fv) :=
  by
  simpa only [nb078AlphaDummy604] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy595 g))).fv ∪ ((Class.cv (nb078AlphaDummy595 g))).fv)
      0

theorem nb078_fresh_800 (g : Var) :
    (nb078AlphaDummy600 g) ∉
      (((Class.cv (nb078AlphaDummy595 g))).fv ∪ ((Class.cv (nb078AlphaDummy596 g))).fv) :=
  by
  simpa only [nb078AlphaDummy600] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy595 g))).fv ∪ ((Class.cv (nb078AlphaDummy596 g))).fv)
      0

theorem nb078_fresh_801 (g : Var) :
    (nb078AlphaDummy606 g) ∉
      (((Class.cv (nb078AlphaDummy596 g))).fv ∪ ((Class.cv (nb078AlphaDummy596 g))).fv) :=
  by
  simpa only [nb078AlphaDummy606] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy596 g))).fv ∪ ((Class.cv (nb078AlphaDummy596 g))).fv)
      0

theorem nb078_fresh_802 :
    (nb078AlphaDummy621) ∉ (((Class.cv (nb078AlphaDummy614))).fv) := by
  simpa only [nb078AlphaDummy621] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy614))).fv) 0

theorem nb078_fresh_803 :
    (nb078AlphaDummy622) ∉ (((Class.cv (nb078AlphaDummy614))).fv) := by
  simpa only [nb078AlphaDummy622] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy614))).fv) 1

theorem nb078_distinct_804 : (nb078AlphaDummy621) ≠ (nb078AlphaDummy622) := by
  simpa only [nb078AlphaDummy621, nb078AlphaDummy622] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy614))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_805 (g : Var) :
    (nb078AlphaDummy623 g) ∉ (((Class.cv (nb078AlphaDummy616 g))).fv) := by
  simpa only [nb078AlphaDummy623] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy616 g))).fv) 0

theorem nb078_fresh_806 (g : Var) :
    (nb078AlphaDummy624 g) ∉ (((Class.cv (nb078AlphaDummy616 g))).fv) := by
  simpa only [nb078AlphaDummy624] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy616 g))).fv) 1

theorem nb078_distinct_807 (g : Var) :
    (nb078AlphaDummy623 g) ≠ (nb078AlphaDummy624 g) := by
  simpa only [nb078AlphaDummy623, nb078AlphaDummy624] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy616 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_808 :
    (nb078AlphaDummy627) ∉
      (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy627] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_809 :
    (nb078AlphaDummy628) ∉
      (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy628] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_810 :
    (nb078AlphaDummy629) ∉
      (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy629] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_811 : (nb078AlphaDummy627) ≠ (nb078AlphaDummy628) := by
  simpa only [nb078AlphaDummy627, nb078AlphaDummy628] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_812 : (nb078AlphaDummy627) ≠ (nb078AlphaDummy629) := by
  simpa only [nb078AlphaDummy627, nb078AlphaDummy629] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_813 : (nb078AlphaDummy628) ≠ (nb078AlphaDummy629) := by
  simpa only [nb078AlphaDummy628, nb078AlphaDummy629] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_814 (g : Var) :
    (nb078AlphaDummy630 g) ∉
      (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy630] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_815 (g : Var) :
    (nb078AlphaDummy631 g) ∉
      (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy631] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_816 (g : Var) :
    (nb078AlphaDummy632 g) ∉
      (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy632] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_817 (g : Var) :
    (nb078AlphaDummy630 g) ≠ (nb078AlphaDummy631 g) := by
  simpa only [nb078AlphaDummy630, nb078AlphaDummy631] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_818 (g : Var) :
    (nb078AlphaDummy630 g) ≠ (nb078AlphaDummy632 g) := by
  simpa only [nb078AlphaDummy630, nb078AlphaDummy632] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_819 (g : Var) :
    (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy632 g) := by
  simpa only [nb078AlphaDummy631, nb078AlphaDummy632] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_820 :
    (nb078AlphaDummy639) ∉
      (((Class.cv (nb078AlphaDummy628))).fv ∪ ((Class.cv (nb078AlphaDummy628))).fv) :=
  by
  simpa only [nb078AlphaDummy639] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy628))).fv ∪ ((Class.cv (nb078AlphaDummy628))).fv)
      0

theorem nb078_fresh_821 :
    (nb078AlphaDummy635) ∉
      (((Class.cv (nb078AlphaDummy628))).fv ∪ ((Class.cv (nb078AlphaDummy629))).fv) :=
  by
  simpa only [nb078AlphaDummy635] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy628))).fv ∪ ((Class.cv (nb078AlphaDummy629))).fv)
      0

theorem nb078_fresh_822 :
    (nb078AlphaDummy641) ∉
      (((Class.cv (nb078AlphaDummy629))).fv ∪ ((Class.cv (nb078AlphaDummy629))).fv) :=
  by
  simpa only [nb078AlphaDummy641] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy629))).fv ∪ ((Class.cv (nb078AlphaDummy629))).fv)
      0

theorem nb078_fresh_823 (g : Var) :
    (nb078AlphaDummy640 g) ∉
      (((Class.cv (nb078AlphaDummy631 g))).fv ∪ ((Class.cv (nb078AlphaDummy631 g))).fv) :=
  by
  simpa only [nb078AlphaDummy640] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy631 g))).fv ∪ ((Class.cv (nb078AlphaDummy631 g))).fv)
      0

theorem nb078_fresh_824 (g : Var) :
    (nb078AlphaDummy636 g) ∉
      (((Class.cv (nb078AlphaDummy631 g))).fv ∪ ((Class.cv (nb078AlphaDummy632 g))).fv) :=
  by
  simpa only [nb078AlphaDummy636] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy631 g))).fv ∪ ((Class.cv (nb078AlphaDummy632 g))).fv)
      0

theorem nb078_fresh_825 (g : Var) :
    (nb078AlphaDummy642 g) ∉
      (((Class.cv (nb078AlphaDummy632 g))).fv ∪ ((Class.cv (nb078AlphaDummy632 g))).fv) :=
  by
  simpa only [nb078AlphaDummy642] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy632 g))).fv ∪ ((Class.cv (nb078AlphaDummy632 g))).fv)
      0

theorem nb078_fresh_826 :
    (nb078AlphaDummy655) ∉
      (((Class.cv (nb078AlphaDummy649))).fv ∪ ((Class.cv (nb078AlphaDummy650))).fv) :=
  by
  simpa only [nb078AlphaDummy655] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy649))).fv ∪ ((Class.cv (nb078AlphaDummy650))).fv)
      0

theorem nb078_fresh_827 :
    (nb078AlphaDummy656) ∉
      (((Class.cv (nb078AlphaDummy649))).fv ∪ ((Class.cv (nb078AlphaDummy650))).fv) :=
  by
  simpa only [nb078AlphaDummy656] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy649))).fv ∪ ((Class.cv (nb078AlphaDummy650))).fv)
      1

theorem nb078_distinct_828 : (nb078AlphaDummy655) ≠ (nb078AlphaDummy656) := by
  simpa only [nb078AlphaDummy655, nb078AlphaDummy656] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy649))).fv ∪ ((Class.cv (nb078AlphaDummy650))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_829 :
    (nb078AlphaDummy691) ∉
      (((Class.cv (nb078AlphaDummy650))).fv ∪ ((Class.cv (nb078AlphaDummy649))).fv) :=
  by
  simpa only [nb078AlphaDummy691] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy650))).fv ∪ ((Class.cv (nb078AlphaDummy649))).fv)
      0

theorem nb078_fresh_830 :
    (nb078AlphaDummy692) ∉
      (((Class.cv (nb078AlphaDummy650))).fv ∪ ((Class.cv (nb078AlphaDummy649))).fv) :=
  by
  simpa only [nb078AlphaDummy692] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy650))).fv ∪ ((Class.cv (nb078AlphaDummy649))).fv)
      1

theorem nb078_distinct_831 : (nb078AlphaDummy691) ≠ (nb078AlphaDummy692) := by
  simpa only [nb078AlphaDummy691, nb078AlphaDummy692] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy650))).fv ∪ ((Class.cv (nb078AlphaDummy649))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_832 (g : Var) :
    (nb078AlphaDummy657 g) ∉
      (((Class.cv (nb078AlphaDummy651 g))).fv ∪ ((Class.cv (nb078AlphaDummy652 g))).fv) :=
  by
  simpa only [nb078AlphaDummy657] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy651 g))).fv ∪ ((Class.cv (nb078AlphaDummy652 g))).fv)
      0

theorem nb078_fresh_833 (g : Var) :
    (nb078AlphaDummy658 g) ∉
      (((Class.cv (nb078AlphaDummy651 g))).fv ∪ ((Class.cv (nb078AlphaDummy652 g))).fv) :=
  by
  simpa only [nb078AlphaDummy658] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy651 g))).fv ∪ ((Class.cv (nb078AlphaDummy652 g))).fv)
      1

theorem nb078_distinct_834 (g : Var) :
    (nb078AlphaDummy657 g) ≠ (nb078AlphaDummy658 g) := by
  simpa only [nb078AlphaDummy657, nb078AlphaDummy658] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy651 g))).fv ∪
        ((Class.cv (nb078AlphaDummy652 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_835 (g : Var) :
    (nb078AlphaDummy693 g) ∉
      (((Class.cv (nb078AlphaDummy652 g))).fv ∪ ((Class.cv (nb078AlphaDummy651 g))).fv) :=
  by
  simpa only [nb078AlphaDummy693] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy652 g))).fv ∪ ((Class.cv (nb078AlphaDummy651 g))).fv)
      0

theorem nb078_fresh_836 (g : Var) :
    (nb078AlphaDummy694 g) ∉
      (((Class.cv (nb078AlphaDummy652 g))).fv ∪ ((Class.cv (nb078AlphaDummy651 g))).fv) :=
  by
  simpa only [nb078AlphaDummy694] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy652 g))).fv ∪ ((Class.cv (nb078AlphaDummy651 g))).fv)
      1

theorem nb078_distinct_837 (g : Var) :
    (nb078AlphaDummy693 g) ≠ (nb078AlphaDummy694 g) := by
  simpa only [nb078AlphaDummy693, nb078AlphaDummy694] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy652 g))).fv ∪
        ((Class.cv (nb078AlphaDummy651 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_838 :
    (nb078AlphaDummy663) ∉ (((Class.cv (nb078AlphaDummy656))).fv) := by
  simpa only [nb078AlphaDummy663] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy656))).fv) 0

theorem nb078_fresh_839 :
    (nb078AlphaDummy664) ∉ (((Class.cv (nb078AlphaDummy656))).fv) := by
  simpa only [nb078AlphaDummy664] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy656))).fv) 1

theorem nb078_distinct_840 : (nb078AlphaDummy663) ≠ (nb078AlphaDummy664) := by
  simpa only [nb078AlphaDummy663, nb078AlphaDummy664] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy656))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_841 (g : Var) :
    (nb078AlphaDummy665 g) ∉ (((Class.cv (nb078AlphaDummy658 g))).fv) := by
  simpa only [nb078AlphaDummy665] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy658 g))).fv) 0

theorem nb078_fresh_842 (g : Var) :
    (nb078AlphaDummy666 g) ∉ (((Class.cv (nb078AlphaDummy658 g))).fv) := by
  simpa only [nb078AlphaDummy666] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy658 g))).fv) 1

theorem nb078_distinct_843 (g : Var) :
    (nb078AlphaDummy665 g) ≠ (nb078AlphaDummy666 g) := by
  simpa only [nb078AlphaDummy665, nb078AlphaDummy666] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy658 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_844 :
    (nb078AlphaDummy669) ∉
      (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy669] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_845 :
    (nb078AlphaDummy670) ∉
      (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy670] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_846 :
    (nb078AlphaDummy671) ∉
      (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy671] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_847 : (nb078AlphaDummy669) ≠ (nb078AlphaDummy670) := by
  simpa only [nb078AlphaDummy669, nb078AlphaDummy670] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_848 : (nb078AlphaDummy669) ≠ (nb078AlphaDummy671) := by
  simpa only [nb078AlphaDummy669, nb078AlphaDummy671] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_849 : (nb078AlphaDummy670) ≠ (nb078AlphaDummy671) := by
  simpa only [nb078AlphaDummy670, nb078AlphaDummy671] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_850 (g : Var) :
    (nb078AlphaDummy672 g) ∉
      (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy672] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_851 (g : Var) :
    (nb078AlphaDummy673 g) ∉
      (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy673] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_852 (g : Var) :
    (nb078AlphaDummy674 g) ∉
      (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy674] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_853 (g : Var) :
    (nb078AlphaDummy672 g) ≠ (nb078AlphaDummy673 g) := by
  simpa only [nb078AlphaDummy672, nb078AlphaDummy673] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (i :=
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
    (nb078AlphaDummy672 g) ≠ (nb078AlphaDummy674 g) := by
  simpa only [nb078AlphaDummy672, nb078AlphaDummy674] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_855 (g : Var) :
    (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy674 g) := by
  simpa only [nb078AlphaDummy673, nb078AlphaDummy674] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_856 :
    (nb078AlphaDummy681) ∉
      (((Class.cv (nb078AlphaDummy670))).fv ∪ ((Class.cv (nb078AlphaDummy670))).fv) :=
  by
  simpa only [nb078AlphaDummy681] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy670))).fv ∪ ((Class.cv (nb078AlphaDummy670))).fv)
      0

theorem nb078_fresh_857 :
    (nb078AlphaDummy677) ∉
      (((Class.cv (nb078AlphaDummy670))).fv ∪ ((Class.cv (nb078AlphaDummy671))).fv) :=
  by
  simpa only [nb078AlphaDummy677] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy670))).fv ∪ ((Class.cv (nb078AlphaDummy671))).fv)
      0

theorem nb078_fresh_858 :
    (nb078AlphaDummy683) ∉
      (((Class.cv (nb078AlphaDummy671))).fv ∪ ((Class.cv (nb078AlphaDummy671))).fv) :=
  by
  simpa only [nb078AlphaDummy683] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy671))).fv ∪ ((Class.cv (nb078AlphaDummy671))).fv)
      0

theorem nb078_fresh_859 (g : Var) :
    (nb078AlphaDummy682 g) ∉
      (((Class.cv (nb078AlphaDummy673 g))).fv ∪ ((Class.cv (nb078AlphaDummy673 g))).fv) :=
  by
  simpa only [nb078AlphaDummy682] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy673 g))).fv ∪ ((Class.cv (nb078AlphaDummy673 g))).fv)
      0

theorem nb078_fresh_860 (g : Var) :
    (nb078AlphaDummy678 g) ∉
      (((Class.cv (nb078AlphaDummy673 g))).fv ∪ ((Class.cv (nb078AlphaDummy674 g))).fv) :=
  by
  simpa only [nb078AlphaDummy678] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy673 g))).fv ∪ ((Class.cv (nb078AlphaDummy674 g))).fv)
      0

theorem nb078_fresh_861 (g : Var) :
    (nb078AlphaDummy684 g) ∉
      (((Class.cv (nb078AlphaDummy674 g))).fv ∪ ((Class.cv (nb078AlphaDummy674 g))).fv) :=
  by
  simpa only [nb078AlphaDummy684] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy674 g))).fv ∪ ((Class.cv (nb078AlphaDummy674 g))).fv)
      0

theorem nb078_fresh_862 :
    (nb078AlphaDummy699) ∉ (((Class.cv (nb078AlphaDummy692))).fv) := by
  simpa only [nb078AlphaDummy699] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy692))).fv) 0

theorem nb078_fresh_863 :
    (nb078AlphaDummy700) ∉ (((Class.cv (nb078AlphaDummy692))).fv) := by
  simpa only [nb078AlphaDummy700] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy692))).fv) 1

theorem nb078_distinct_864 : (nb078AlphaDummy699) ≠ (nb078AlphaDummy700) := by
  simpa only [nb078AlphaDummy699, nb078AlphaDummy700] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy692))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_865 (g : Var) :
    (nb078AlphaDummy701 g) ∉ (((Class.cv (nb078AlphaDummy694 g))).fv) := by
  simpa only [nb078AlphaDummy701] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy694 g))).fv) 0

theorem nb078_fresh_866 (g : Var) :
    (nb078AlphaDummy702 g) ∉ (((Class.cv (nb078AlphaDummy694 g))).fv) := by
  simpa only [nb078AlphaDummy702] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy694 g))).fv) 1

theorem nb078_distinct_867 (g : Var) :
    (nb078AlphaDummy701 g) ≠ (nb078AlphaDummy702 g) := by
  simpa only [nb078AlphaDummy701, nb078AlphaDummy702] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy694 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_868 :
    (nb078AlphaDummy705) ∉
      (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy705] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_869 :
    (nb078AlphaDummy706) ∉
      (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy706] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_870 :
    (nb078AlphaDummy707) ∉
      (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy707] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_871 : (nb078AlphaDummy705) ≠ (nb078AlphaDummy706) := by
  simpa only [nb078AlphaDummy705, nb078AlphaDummy706] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_872 : (nb078AlphaDummy705) ≠ (nb078AlphaDummy707) := by
  simpa only [nb078AlphaDummy705, nb078AlphaDummy707] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_873 : (nb078AlphaDummy706) ≠ (nb078AlphaDummy707) := by
  simpa only [nb078AlphaDummy706, nb078AlphaDummy707] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_874 (g : Var) :
    (nb078AlphaDummy708 g) ∉
      (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy708] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_875 (g : Var) :
    (nb078AlphaDummy709 g) ∉
      (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy709] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_876 (g : Var) :
    (nb078AlphaDummy710 g) ∉
      (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy710] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_877 (g : Var) :
    (nb078AlphaDummy708 g) ≠ (nb078AlphaDummy709 g) := by
  simpa only [nb078AlphaDummy708, nb078AlphaDummy709] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_878 (g : Var) :
    (nb078AlphaDummy708 g) ≠ (nb078AlphaDummy710 g) := by
  simpa only [nb078AlphaDummy708, nb078AlphaDummy710] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_879 (g : Var) :
    (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy710 g) := by
  simpa only [nb078AlphaDummy709, nb078AlphaDummy710] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_880 :
    (nb078AlphaDummy717) ∉
      (((Class.cv (nb078AlphaDummy706))).fv ∪ ((Class.cv (nb078AlphaDummy706))).fv) :=
  by
  simpa only [nb078AlphaDummy717] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy706))).fv ∪ ((Class.cv (nb078AlphaDummy706))).fv)
      0

theorem nb078_fresh_881 :
    (nb078AlphaDummy713) ∉
      (((Class.cv (nb078AlphaDummy706))).fv ∪ ((Class.cv (nb078AlphaDummy707))).fv) :=
  by
  simpa only [nb078AlphaDummy713] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy706))).fv ∪ ((Class.cv (nb078AlphaDummy707))).fv)
      0

theorem nb078_fresh_882 :
    (nb078AlphaDummy719) ∉
      (((Class.cv (nb078AlphaDummy707))).fv ∪ ((Class.cv (nb078AlphaDummy707))).fv) :=
  by
  simpa only [nb078AlphaDummy719] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy707))).fv ∪ ((Class.cv (nb078AlphaDummy707))).fv)
      0

theorem nb078_fresh_883 (g : Var) :
    (nb078AlphaDummy718 g) ∉
      (((Class.cv (nb078AlphaDummy709 g))).fv ∪ ((Class.cv (nb078AlphaDummy709 g))).fv) :=
  by
  simpa only [nb078AlphaDummy718] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy709 g))).fv ∪ ((Class.cv (nb078AlphaDummy709 g))).fv)
      0

theorem nb078_fresh_884 (g : Var) :
    (nb078AlphaDummy714 g) ∉
      (((Class.cv (nb078AlphaDummy709 g))).fv ∪ ((Class.cv (nb078AlphaDummy710 g))).fv) :=
  by
  simpa only [nb078AlphaDummy714] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy709 g))).fv ∪ ((Class.cv (nb078AlphaDummy710 g))).fv)
      0

theorem nb078_fresh_885 (g : Var) :
    (nb078AlphaDummy720 g) ∉
      (((Class.cv (nb078AlphaDummy710 g))).fv ∪ ((Class.cv (nb078AlphaDummy710 g))).fv) :=
  by
  simpa only [nb078AlphaDummy720] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy710 g))).fv ∪ ((Class.cv (nb078AlphaDummy710 g))).fv)
      0

theorem nb078_fresh_886 :
    (nb078AlphaDummy735) ∉ (((Class.cv (nb078AlphaDummy728))).fv) := by
  simpa only [nb078AlphaDummy735] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy728))).fv) 0

theorem nb078_fresh_887 :
    (nb078AlphaDummy736) ∉ (((Class.cv (nb078AlphaDummy728))).fv) := by
  simpa only [nb078AlphaDummy736] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy728))).fv) 1

theorem nb078_distinct_888 : (nb078AlphaDummy735) ≠ (nb078AlphaDummy736) := by
  simpa only [nb078AlphaDummy735, nb078AlphaDummy736] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy728))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_889 (g : Var) :
    (nb078AlphaDummy737 g) ∉ (((Class.cv (nb078AlphaDummy730 g))).fv) := by
  simpa only [nb078AlphaDummy737] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy730 g))).fv) 0

theorem nb078_fresh_890 (g : Var) :
    (nb078AlphaDummy738 g) ∉ (((Class.cv (nb078AlphaDummy730 g))).fv) := by
  simpa only [nb078AlphaDummy738] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy730 g))).fv) 1

theorem nb078_distinct_891 (g : Var) :
    (nb078AlphaDummy737 g) ≠ (nb078AlphaDummy738 g) := by
  simpa only [nb078AlphaDummy737, nb078AlphaDummy738] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy730 g))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_892 :
    (nb078AlphaDummy741) ∉
      (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy741] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_893 :
    (nb078AlphaDummy742) ∉
      (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy742] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_894 :
    (nb078AlphaDummy743) ∉
      (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy743] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_895 : (nb078AlphaDummy741) ≠ (nb078AlphaDummy742) := by
  simpa only [nb078AlphaDummy741, nb078AlphaDummy742] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_896 : (nb078AlphaDummy741) ≠ (nb078AlphaDummy743) := by
  simpa only [nb078AlphaDummy741, nb078AlphaDummy743] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_897 : (nb078AlphaDummy742) ≠ (nb078AlphaDummy743) := by
  simpa only [nb078AlphaDummy742, nb078AlphaDummy743] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_898 (g : Var) :
    (nb078AlphaDummy744 g) ∉
      (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy744] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_899 (g : Var) :
    (nb078AlphaDummy745 g) ∉
      (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy745] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_900 (g : Var) :
    (nb078AlphaDummy746 g) ∉
      (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy746] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_901 (g : Var) :
    (nb078AlphaDummy744 g) ≠ (nb078AlphaDummy745 g) := by
  simpa only [nb078AlphaDummy744, nb078AlphaDummy745] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_902 (g : Var) :
    (nb078AlphaDummy744 g) ≠ (nb078AlphaDummy746 g) := by
  simpa only [nb078AlphaDummy744, nb078AlphaDummy746] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_903 (g : Var) :
    (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy746 g) := by
  simpa only [nb078AlphaDummy745, nb078AlphaDummy746] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_904 :
    (nb078AlphaDummy753) ∉
      (((Class.cv (nb078AlphaDummy742))).fv ∪ ((Class.cv (nb078AlphaDummy742))).fv) :=
  by
  simpa only [nb078AlphaDummy753] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy742))).fv ∪ ((Class.cv (nb078AlphaDummy742))).fv)
      0

theorem nb078_fresh_905 :
    (nb078AlphaDummy749) ∉
      (((Class.cv (nb078AlphaDummy742))).fv ∪ ((Class.cv (nb078AlphaDummy743))).fv) :=
  by
  simpa only [nb078AlphaDummy749] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy742))).fv ∪ ((Class.cv (nb078AlphaDummy743))).fv)
      0

theorem nb078_fresh_906 :
    (nb078AlphaDummy755) ∉
      (((Class.cv (nb078AlphaDummy743))).fv ∪ ((Class.cv (nb078AlphaDummy743))).fv) :=
  by
  simpa only [nb078AlphaDummy755] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy743))).fv ∪ ((Class.cv (nb078AlphaDummy743))).fv)
      0

theorem nb078_fresh_907 (g : Var) :
    (nb078AlphaDummy754 g) ∉
      (((Class.cv (nb078AlphaDummy745 g))).fv ∪ ((Class.cv (nb078AlphaDummy745 g))).fv) :=
  by
  simpa only [nb078AlphaDummy754] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy745 g))).fv ∪ ((Class.cv (nb078AlphaDummy745 g))).fv)
      0

theorem nb078_fresh_908 (g : Var) :
    (nb078AlphaDummy750 g) ∉
      (((Class.cv (nb078AlphaDummy745 g))).fv ∪ ((Class.cv (nb078AlphaDummy746 g))).fv) :=
  by
  simpa only [nb078AlphaDummy750] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy745 g))).fv ∪ ((Class.cv (nb078AlphaDummy746 g))).fv)
      0

theorem nb078_fresh_909 (g : Var) :
    (nb078AlphaDummy756 g) ∉
      (((Class.cv (nb078AlphaDummy746 g))).fv ∪ ((Class.cv (nb078AlphaDummy746 g))).fv) :=
  by
  simpa only [nb078AlphaDummy756] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy746 g))).fv ∪ ((Class.cv (nb078AlphaDummy746 g))).fv)
      0

theorem nb078_fresh_910 :
    (nb078AlphaDummy775) ∉
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) :=
  by
  simpa only [nb078AlphaDummy775] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv)
      0

theorem nb078_fresh_911 :
    (nb078AlphaDummy776) ∉
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) :=
  by
  simpa only [nb078AlphaDummy776] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv)
      1

theorem nb078_distinct_912 : (nb078AlphaDummy775) ≠ (nb078AlphaDummy776) := by
  simpa only [nb078AlphaDummy775, nb078AlphaDummy776] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_913 :
    (nb078AlphaDummy811) ∉
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy769))).fv) :=
  by
  simpa only [nb078AlphaDummy811] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy769))).fv)
      0

theorem nb078_fresh_914 :
    (nb078AlphaDummy812) ∉
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy769))).fv) :=
  by
  simpa only [nb078AlphaDummy812] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy769))).fv)
      1

theorem nb078_distinct_915 : (nb078AlphaDummy811) ≠ (nb078AlphaDummy812) := by
  simpa only [nb078AlphaDummy811, nb078AlphaDummy812] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy769))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_916 :
    (nb078AlphaDummy925) ∉
      (((Class.cv (nb078AlphaDummy769))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) :=
  by
  simpa only [nb078AlphaDummy925] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy769))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv)
      0

theorem nb078_fresh_917 :
    (nb078AlphaDummy926) ∉
      (((Class.cv (nb078AlphaDummy769))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) :=
  by
  simpa only [nb078AlphaDummy926] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy769))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv)
      1

theorem nb078_distinct_918 : (nb078AlphaDummy925) ≠ (nb078AlphaDummy926) := by
  simpa only [nb078AlphaDummy925, nb078AlphaDummy926] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy769))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_919 (h : Var) :
    (nb078AlphaDummy777 h) ∉
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv) :=
  by
  simpa only [nb078AlphaDummy777] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv)
      0

theorem nb078_fresh_920 (h : Var) :
    (nb078AlphaDummy778 h) ∉
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv) :=
  by
  simpa only [nb078AlphaDummy778] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv)
      1

theorem nb078_distinct_921 (h : Var) :
    (nb078AlphaDummy777 h) ≠ (nb078AlphaDummy778 h) := by
  simpa only [nb078AlphaDummy777, nb078AlphaDummy778] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy770 h))).fv ∪
        ((Class.cv (nb078AlphaDummy771 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_922 (h : Var) :
    (nb078AlphaDummy813 h) ∉
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy772 h))).fv) :=
  by
  simpa only [nb078AlphaDummy813] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy772 h))).fv)
      0

theorem nb078_fresh_923 (h : Var) :
    (nb078AlphaDummy814 h) ∉
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy772 h))).fv) :=
  by
  simpa only [nb078AlphaDummy814] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy772 h))).fv)
      1

theorem nb078_distinct_924 (h : Var) :
    (nb078AlphaDummy813 h) ≠ (nb078AlphaDummy814 h) := by
  simpa only [nb078AlphaDummy813, nb078AlphaDummy814] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy770 h))).fv ∪
        ((Class.cv (nb078AlphaDummy772 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_925 (h : Var) :
    (nb078AlphaDummy927 h) ∉
      (((Class.cv (nb078AlphaDummy772 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv) :=
  by
  simpa only [nb078AlphaDummy927] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy772 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv)
      0

theorem nb078_fresh_926 (h : Var) :
    (nb078AlphaDummy928 h) ∉
      (((Class.cv (nb078AlphaDummy772 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv) :=
  by
  simpa only [nb078AlphaDummy928] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy772 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv)
      1

theorem nb078_distinct_927 (h : Var) :
    (nb078AlphaDummy927 h) ≠ (nb078AlphaDummy928 h) := by
  simpa only [nb078AlphaDummy927, nb078AlphaDummy928] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy772 h))).fv ∪
        ((Class.cv (nb078AlphaDummy771 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_928 :
    (nb078AlphaDummy783) ∉ (((Class.cv (nb078AlphaDummy776))).fv) := by
  simpa only [nb078AlphaDummy783] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy776))).fv) 0

theorem nb078_fresh_929 :
    (nb078AlphaDummy784) ∉ (((Class.cv (nb078AlphaDummy776))).fv) := by
  simpa only [nb078AlphaDummy784] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy776))).fv) 1

theorem nb078_distinct_930 : (nb078AlphaDummy783) ≠ (nb078AlphaDummy784) := by
  simpa only [nb078AlphaDummy783, nb078AlphaDummy784] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy776))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_931 (h : Var) :
    (nb078AlphaDummy785 h) ∉ (((Class.cv (nb078AlphaDummy778 h))).fv) := by
  simpa only [nb078AlphaDummy785] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy778 h))).fv) 0

theorem nb078_fresh_932 (h : Var) :
    (nb078AlphaDummy786 h) ∉ (((Class.cv (nb078AlphaDummy778 h))).fv) := by
  simpa only [nb078AlphaDummy786] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy778 h))).fv) 1

theorem nb078_distinct_933 (h : Var) :
    (nb078AlphaDummy785 h) ≠ (nb078AlphaDummy786 h) := by
  simpa only [nb078AlphaDummy785, nb078AlphaDummy786] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy778 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_934 :
    (nb078AlphaDummy789) ∉
      (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy789] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_935 :
    (nb078AlphaDummy790) ∉
      (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy790] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_936 :
    (nb078AlphaDummy791) ∉
      (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy791] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_937 : (nb078AlphaDummy789) ≠ (nb078AlphaDummy790) := by
  simpa only [nb078AlphaDummy789, nb078AlphaDummy790] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_938 : (nb078AlphaDummy789) ≠ (nb078AlphaDummy791) := by
  simpa only [nb078AlphaDummy789, nb078AlphaDummy791] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_939 : (nb078AlphaDummy790) ≠ (nb078AlphaDummy791) := by
  simpa only [nb078AlphaDummy790, nb078AlphaDummy791] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_940 (h : Var) :
    (nb078AlphaDummy792 h) ∉
      (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy792] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_941 (h : Var) :
    (nb078AlphaDummy793 h) ∉
      (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy793] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_942 (h : Var) :
    (nb078AlphaDummy794 h) ∉
      (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy794] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_943 (h : Var) :
    (nb078AlphaDummy792 h) ≠ (nb078AlphaDummy793 h) := by
  simpa only [nb078AlphaDummy792, nb078AlphaDummy793] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_944 (h : Var) :
    (nb078AlphaDummy792 h) ≠ (nb078AlphaDummy794 h) := by
  simpa only [nb078AlphaDummy792, nb078AlphaDummy794] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_945 (h : Var) :
    (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy794 h) := by
  simpa only [nb078AlphaDummy793, nb078AlphaDummy794] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_946 :
    (nb078AlphaDummy801) ∉
      (((Class.cv (nb078AlphaDummy790))).fv ∪ ((Class.cv (nb078AlphaDummy790))).fv) :=
  by
  simpa only [nb078AlphaDummy801] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy790))).fv ∪ ((Class.cv (nb078AlphaDummy790))).fv)
      0

theorem nb078_fresh_947 :
    (nb078AlphaDummy797) ∉
      (((Class.cv (nb078AlphaDummy790))).fv ∪ ((Class.cv (nb078AlphaDummy791))).fv) :=
  by
  simpa only [nb078AlphaDummy797] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy790))).fv ∪ ((Class.cv (nb078AlphaDummy791))).fv)
      0

theorem nb078_fresh_948 :
    (nb078AlphaDummy803) ∉
      (((Class.cv (nb078AlphaDummy791))).fv ∪ ((Class.cv (nb078AlphaDummy791))).fv) :=
  by
  simpa only [nb078AlphaDummy803] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy791))).fv ∪ ((Class.cv (nb078AlphaDummy791))).fv)
      0

theorem nb078_fresh_949 (h : Var) :
    (nb078AlphaDummy802 h) ∉
      (((Class.cv (nb078AlphaDummy793 h))).fv ∪ ((Class.cv (nb078AlphaDummy793 h))).fv) :=
  by
  simpa only [nb078AlphaDummy802] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy793 h))).fv ∪ ((Class.cv (nb078AlphaDummy793 h))).fv)
      0

theorem nb078_fresh_950 (h : Var) :
    (nb078AlphaDummy798 h) ∉
      (((Class.cv (nb078AlphaDummy793 h))).fv ∪ ((Class.cv (nb078AlphaDummy794 h))).fv) :=
  by
  simpa only [nb078AlphaDummy798] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy793 h))).fv ∪ ((Class.cv (nb078AlphaDummy794 h))).fv)
      0

theorem nb078_fresh_951 (h : Var) :
    (nb078AlphaDummy804 h) ∉
      (((Class.cv (nb078AlphaDummy794 h))).fv ∪ ((Class.cv (nb078AlphaDummy794 h))).fv) :=
  by
  simpa only [nb078AlphaDummy804] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy794 h))).fv ∪ ((Class.cv (nb078AlphaDummy794 h))).fv)
      0

theorem nb078_fresh_952 :
    (nb078AlphaDummy819) ∉ (((Class.cv (nb078AlphaDummy812))).fv) := by
  simpa only [nb078AlphaDummy819] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy812))).fv) 0

theorem nb078_fresh_953 :
    (nb078AlphaDummy820) ∉ (((Class.cv (nb078AlphaDummy812))).fv) := by
  simpa only [nb078AlphaDummy820] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy812))).fv) 1

theorem nb078_distinct_954 : (nb078AlphaDummy819) ≠ (nb078AlphaDummy820) := by
  simpa only [nb078AlphaDummy819, nb078AlphaDummy820] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy812))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_955 (h : Var) :
    (nb078AlphaDummy821 h) ∉ (((Class.cv (nb078AlphaDummy814 h))).fv) := by
  simpa only [nb078AlphaDummy821] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy814 h))).fv) 0

theorem nb078_fresh_956 (h : Var) :
    (nb078AlphaDummy822 h) ∉ (((Class.cv (nb078AlphaDummy814 h))).fv) := by
  simpa only [nb078AlphaDummy822] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy814 h))).fv) 1

theorem nb078_distinct_957 (h : Var) :
    (nb078AlphaDummy821 h) ≠ (nb078AlphaDummy822 h) := by
  simpa only [nb078AlphaDummy821, nb078AlphaDummy822] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy814 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_958 :
    (nb078AlphaDummy825) ∉
      (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy825] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_959 :
    (nb078AlphaDummy826) ∉
      (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy826] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_960 :
    (nb078AlphaDummy827) ∉
      (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy827] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_961 : (nb078AlphaDummy825) ≠ (nb078AlphaDummy826) := by
  simpa only [nb078AlphaDummy825, nb078AlphaDummy826] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_962 : (nb078AlphaDummy825) ≠ (nb078AlphaDummy827) := by
  simpa only [nb078AlphaDummy825, nb078AlphaDummy827] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_963 : (nb078AlphaDummy826) ≠ (nb078AlphaDummy827) := by
  simpa only [nb078AlphaDummy826, nb078AlphaDummy827] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_964 (h : Var) :
    (nb078AlphaDummy828 h) ∉
      (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy828] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_965 (h : Var) :
    (nb078AlphaDummy829 h) ∉
      (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy829] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_966 (h : Var) :
    (nb078AlphaDummy830 h) ∉
      (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy830] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_967 (h : Var) :
    (nb078AlphaDummy828 h) ≠ (nb078AlphaDummy829 h) := by
  simpa only [nb078AlphaDummy828, nb078AlphaDummy829] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_968 (h : Var) :
    (nb078AlphaDummy828 h) ≠ (nb078AlphaDummy830 h) := by
  simpa only [nb078AlphaDummy828, nb078AlphaDummy830] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_969 (h : Var) :
    (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy830 h) := by
  simpa only [nb078AlphaDummy829, nb078AlphaDummy830] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_970 :
    (nb078AlphaDummy837) ∉
      (((Class.cv (nb078AlphaDummy826))).fv ∪ ((Class.cv (nb078AlphaDummy826))).fv) :=
  by
  simpa only [nb078AlphaDummy837] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy826))).fv ∪ ((Class.cv (nb078AlphaDummy826))).fv)
      0

theorem nb078_fresh_971 :
    (nb078AlphaDummy833) ∉
      (((Class.cv (nb078AlphaDummy826))).fv ∪ ((Class.cv (nb078AlphaDummy827))).fv) :=
  by
  simpa only [nb078AlphaDummy833] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy826))).fv ∪ ((Class.cv (nb078AlphaDummy827))).fv)
      0

theorem nb078_fresh_972 :
    (nb078AlphaDummy839) ∉
      (((Class.cv (nb078AlphaDummy827))).fv ∪ ((Class.cv (nb078AlphaDummy827))).fv) :=
  by
  simpa only [nb078AlphaDummy839] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy827))).fv ∪ ((Class.cv (nb078AlphaDummy827))).fv)
      0

theorem nb078_fresh_973 (h : Var) :
    (nb078AlphaDummy838 h) ∉
      (((Class.cv (nb078AlphaDummy829 h))).fv ∪ ((Class.cv (nb078AlphaDummy829 h))).fv) :=
  by
  simpa only [nb078AlphaDummy838] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy829 h))).fv ∪ ((Class.cv (nb078AlphaDummy829 h))).fv)
      0

theorem nb078_fresh_974 (h : Var) :
    (nb078AlphaDummy834 h) ∉
      (((Class.cv (nb078AlphaDummy829 h))).fv ∪ ((Class.cv (nb078AlphaDummy830 h))).fv) :=
  by
  simpa only [nb078AlphaDummy834] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy829 h))).fv ∪ ((Class.cv (nb078AlphaDummy830 h))).fv)
      0

theorem nb078_fresh_975 (h : Var) :
    (nb078AlphaDummy840 h) ∉
      (((Class.cv (nb078AlphaDummy830 h))).fv ∪ ((Class.cv (nb078AlphaDummy830 h))).fv) :=
  by
  simpa only [nb078AlphaDummy840] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy830 h))).fv ∪ ((Class.cv (nb078AlphaDummy830 h))).fv)
      0

theorem nb078_fresh_976 :
    (nb078AlphaDummy853) ∉
      (((Class.cv (nb078AlphaDummy847))).fv ∪ ((Class.cv (nb078AlphaDummy848))).fv) :=
  by
  simpa only [nb078AlphaDummy853] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy847))).fv ∪ ((Class.cv (nb078AlphaDummy848))).fv)
      0

theorem nb078_fresh_977 :
    (nb078AlphaDummy854) ∉
      (((Class.cv (nb078AlphaDummy847))).fv ∪ ((Class.cv (nb078AlphaDummy848))).fv) :=
  by
  simpa only [nb078AlphaDummy854] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy847))).fv ∪ ((Class.cv (nb078AlphaDummy848))).fv)
      1

theorem nb078_distinct_978 : (nb078AlphaDummy853) ≠ (nb078AlphaDummy854) := by
  simpa only [nb078AlphaDummy853, nb078AlphaDummy854] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy847))).fv ∪ ((Class.cv (nb078AlphaDummy848))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_979 :
    (nb078AlphaDummy889) ∉
      (((Class.cv (nb078AlphaDummy848))).fv ∪ ((Class.cv (nb078AlphaDummy847))).fv) :=
  by
  simpa only [nb078AlphaDummy889] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy848))).fv ∪ ((Class.cv (nb078AlphaDummy847))).fv)
      0

theorem nb078_fresh_980 :
    (nb078AlphaDummy890) ∉
      (((Class.cv (nb078AlphaDummy848))).fv ∪ ((Class.cv (nb078AlphaDummy847))).fv) :=
  by
  simpa only [nb078AlphaDummy890] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy848))).fv ∪ ((Class.cv (nb078AlphaDummy847))).fv)
      1

theorem nb078_distinct_981 : (nb078AlphaDummy889) ≠ (nb078AlphaDummy890) := by
  simpa only [nb078AlphaDummy889, nb078AlphaDummy890] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy848))).fv ∪ ((Class.cv (nb078AlphaDummy847))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_982 (h : Var) :
    (nb078AlphaDummy855 h) ∉
      (((Class.cv (nb078AlphaDummy849 h))).fv ∪ ((Class.cv (nb078AlphaDummy850 h))).fv) :=
  by
  simpa only [nb078AlphaDummy855] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy849 h))).fv ∪ ((Class.cv (nb078AlphaDummy850 h))).fv)
      0

theorem nb078_fresh_983 (h : Var) :
    (nb078AlphaDummy856 h) ∉
      (((Class.cv (nb078AlphaDummy849 h))).fv ∪ ((Class.cv (nb078AlphaDummy850 h))).fv) :=
  by
  simpa only [nb078AlphaDummy856] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy849 h))).fv ∪ ((Class.cv (nb078AlphaDummy850 h))).fv)
      1

theorem nb078_distinct_984 (h : Var) :
    (nb078AlphaDummy855 h) ≠ (nb078AlphaDummy856 h) := by
  simpa only [nb078AlphaDummy855, nb078AlphaDummy856] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy849 h))).fv ∪
        ((Class.cv (nb078AlphaDummy850 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_985 (h : Var) :
    (nb078AlphaDummy891 h) ∉
      (((Class.cv (nb078AlphaDummy850 h))).fv ∪ ((Class.cv (nb078AlphaDummy849 h))).fv) :=
  by
  simpa only [nb078AlphaDummy891] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy850 h))).fv ∪ ((Class.cv (nb078AlphaDummy849 h))).fv)
      0

theorem nb078_fresh_986 (h : Var) :
    (nb078AlphaDummy892 h) ∉
      (((Class.cv (nb078AlphaDummy850 h))).fv ∪ ((Class.cv (nb078AlphaDummy849 h))).fv) :=
  by
  simpa only [nb078AlphaDummy892] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy850 h))).fv ∪ ((Class.cv (nb078AlphaDummy849 h))).fv)
      1

theorem nb078_distinct_987 (h : Var) :
    (nb078AlphaDummy891 h) ≠ (nb078AlphaDummy892 h) := by
  simpa only [nb078AlphaDummy891, nb078AlphaDummy892] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy850 h))).fv ∪
        ((Class.cv (nb078AlphaDummy849 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_988 :
    (nb078AlphaDummy861) ∉ (((Class.cv (nb078AlphaDummy854))).fv) := by
  simpa only [nb078AlphaDummy861] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy854))).fv) 0

theorem nb078_fresh_989 :
    (nb078AlphaDummy862) ∉ (((Class.cv (nb078AlphaDummy854))).fv) := by
  simpa only [nb078AlphaDummy862] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy854))).fv) 1

theorem nb078_distinct_990 : (nb078AlphaDummy861) ≠ (nb078AlphaDummy862) := by
  simpa only [nb078AlphaDummy861, nb078AlphaDummy862] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy854))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_991 (h : Var) :
    (nb078AlphaDummy863 h) ∉ (((Class.cv (nb078AlphaDummy856 h))).fv) := by
  simpa only [nb078AlphaDummy863] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy856 h))).fv) 0

theorem nb078_fresh_992 (h : Var) :
    (nb078AlphaDummy864 h) ∉ (((Class.cv (nb078AlphaDummy856 h))).fv) := by
  simpa only [nb078AlphaDummy864] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy856 h))).fv) 1

theorem nb078_distinct_993 (h : Var) :
    (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy864 h) := by
  simpa only [nb078AlphaDummy863, nb078AlphaDummy864] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy856 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_994 :
    (nb078AlphaDummy867) ∉
      (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy867] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_995 :
    (nb078AlphaDummy868) ∉
      (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy868] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_996 :
    (nb078AlphaDummy869) ∉
      (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy869] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_997 : (nb078AlphaDummy867) ≠ (nb078AlphaDummy868) := by
  simpa only [nb078AlphaDummy867, nb078AlphaDummy868] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_998 : (nb078AlphaDummy867) ≠ (nb078AlphaDummy869) := by
  simpa only [nb078AlphaDummy867, nb078AlphaDummy869] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_999 : (nb078AlphaDummy868) ≠ (nb078AlphaDummy869) := by
  simpa only [nb078AlphaDummy868, nb078AlphaDummy869] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1000 (h : Var) :
    (nb078AlphaDummy870 h) ∉
      (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy870] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_1001 (h : Var) :
    (nb078AlphaDummy871 h) ∉
      (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy871] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_1002 (h : Var) :
    (nb078AlphaDummy872 h) ∉
      (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy872] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_1003 (h : Var) :
    (nb078AlphaDummy870 h) ≠ (nb078AlphaDummy871 h) := by
  simpa only [nb078AlphaDummy870, nb078AlphaDummy871] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (i :=
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
    (nb078AlphaDummy870 h) ≠ (nb078AlphaDummy872 h) := by
  simpa only [nb078AlphaDummy870, nb078AlphaDummy872] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1005 (h : Var) :
    (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy872 h) := by
  simpa only [nb078AlphaDummy871, nb078AlphaDummy872] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1006 :
    (nb078AlphaDummy879) ∉
      (((Class.cv (nb078AlphaDummy868))).fv ∪ ((Class.cv (nb078AlphaDummy868))).fv) :=
  by
  simpa only [nb078AlphaDummy879] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy868))).fv ∪ ((Class.cv (nb078AlphaDummy868))).fv)
      0

theorem nb078_fresh_1007 :
    (nb078AlphaDummy875) ∉
      (((Class.cv (nb078AlphaDummy868))).fv ∪ ((Class.cv (nb078AlphaDummy869))).fv) :=
  by
  simpa only [nb078AlphaDummy875] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy868))).fv ∪ ((Class.cv (nb078AlphaDummy869))).fv)
      0

theorem nb078_fresh_1008 :
    (nb078AlphaDummy881) ∉
      (((Class.cv (nb078AlphaDummy869))).fv ∪ ((Class.cv (nb078AlphaDummy869))).fv) :=
  by
  simpa only [nb078AlphaDummy881] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy869))).fv ∪ ((Class.cv (nb078AlphaDummy869))).fv)
      0

theorem nb078_fresh_1009 (h : Var) :
    (nb078AlphaDummy880 h) ∉
      (((Class.cv (nb078AlphaDummy871 h))).fv ∪ ((Class.cv (nb078AlphaDummy871 h))).fv) :=
  by
  simpa only [nb078AlphaDummy880] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy871 h))).fv ∪ ((Class.cv (nb078AlphaDummy871 h))).fv)
      0

theorem nb078_fresh_1010 (h : Var) :
    (nb078AlphaDummy876 h) ∉
      (((Class.cv (nb078AlphaDummy871 h))).fv ∪ ((Class.cv (nb078AlphaDummy872 h))).fv) :=
  by
  simpa only [nb078AlphaDummy876] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy871 h))).fv ∪ ((Class.cv (nb078AlphaDummy872 h))).fv)
      0

theorem nb078_fresh_1011 (h : Var) :
    (nb078AlphaDummy882 h) ∉
      (((Class.cv (nb078AlphaDummy872 h))).fv ∪ ((Class.cv (nb078AlphaDummy872 h))).fv) :=
  by
  simpa only [nb078AlphaDummy882] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy872 h))).fv ∪ ((Class.cv (nb078AlphaDummy872 h))).fv)
      0

theorem nb078_fresh_1012 :
    (nb078AlphaDummy897) ∉ (((Class.cv (nb078AlphaDummy890))).fv) := by
  simpa only [nb078AlphaDummy897] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy890))).fv) 0

theorem nb078_fresh_1013 :
    (nb078AlphaDummy898) ∉ (((Class.cv (nb078AlphaDummy890))).fv) := by
  simpa only [nb078AlphaDummy898] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy890))).fv) 1

theorem nb078_distinct_1014 : (nb078AlphaDummy897) ≠ (nb078AlphaDummy898) := by
  simpa only [nb078AlphaDummy897, nb078AlphaDummy898] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy890))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1015 (h : Var) :
    (nb078AlphaDummy899 h) ∉ (((Class.cv (nb078AlphaDummy892 h))).fv) := by
  simpa only [nb078AlphaDummy899] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy892 h))).fv) 0

theorem nb078_fresh_1016 (h : Var) :
    (nb078AlphaDummy900 h) ∉ (((Class.cv (nb078AlphaDummy892 h))).fv) := by
  simpa only [nb078AlphaDummy900] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy892 h))).fv) 1

theorem nb078_distinct_1017 (h : Var) :
    (nb078AlphaDummy899 h) ≠ (nb078AlphaDummy900 h) := by
  simpa only [nb078AlphaDummy899, nb078AlphaDummy900] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy892 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1018 :
    (nb078AlphaDummy903) ∉
      (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy903] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_1019 :
    (nb078AlphaDummy904) ∉
      (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy904] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_1020 :
    (nb078AlphaDummy905) ∉
      (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy905] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_1021 : (nb078AlphaDummy903) ≠ (nb078AlphaDummy904) := by
  simpa only [nb078AlphaDummy903, nb078AlphaDummy904] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1022 : (nb078AlphaDummy903) ≠ (nb078AlphaDummy905) := by
  simpa only [nb078AlphaDummy903, nb078AlphaDummy905] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1023 : (nb078AlphaDummy904) ≠ (nb078AlphaDummy905) := by
  simpa only [nb078AlphaDummy904, nb078AlphaDummy905] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1024 (h : Var) :
    (nb078AlphaDummy906 h) ∉
      (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy906] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_1025 (h : Var) :
    (nb078AlphaDummy907 h) ∉
      (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy907] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_1026 (h : Var) :
    (nb078AlphaDummy908 h) ∉
      (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy908] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_1027 (h : Var) :
    (nb078AlphaDummy906 h) ≠ (nb078AlphaDummy907 h) := by
  simpa only [nb078AlphaDummy906, nb078AlphaDummy907] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1028 (h : Var) :
    (nb078AlphaDummy906 h) ≠ (nb078AlphaDummy908 h) := by
  simpa only [nb078AlphaDummy906, nb078AlphaDummy908] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1029 (h : Var) :
    (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy908 h) := by
  simpa only [nb078AlphaDummy907, nb078AlphaDummy908] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1030 :
    (nb078AlphaDummy915) ∉
      (((Class.cv (nb078AlphaDummy904))).fv ∪ ((Class.cv (nb078AlphaDummy904))).fv) :=
  by
  simpa only [nb078AlphaDummy915] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy904))).fv ∪ ((Class.cv (nb078AlphaDummy904))).fv)
      0

theorem nb078_fresh_1031 :
    (nb078AlphaDummy911) ∉
      (((Class.cv (nb078AlphaDummy904))).fv ∪ ((Class.cv (nb078AlphaDummy905))).fv) :=
  by
  simpa only [nb078AlphaDummy911] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy904))).fv ∪ ((Class.cv (nb078AlphaDummy905))).fv)
      0

theorem nb078_fresh_1032 :
    (nb078AlphaDummy917) ∉
      (((Class.cv (nb078AlphaDummy905))).fv ∪ ((Class.cv (nb078AlphaDummy905))).fv) :=
  by
  simpa only [nb078AlphaDummy917] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy905))).fv ∪ ((Class.cv (nb078AlphaDummy905))).fv)
      0

theorem nb078_fresh_1033 (h : Var) :
    (nb078AlphaDummy916 h) ∉
      (((Class.cv (nb078AlphaDummy907 h))).fv ∪ ((Class.cv (nb078AlphaDummy907 h))).fv) :=
  by
  simpa only [nb078AlphaDummy916] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy907 h))).fv ∪ ((Class.cv (nb078AlphaDummy907 h))).fv)
      0

theorem nb078_fresh_1034 (h : Var) :
    (nb078AlphaDummy912 h) ∉
      (((Class.cv (nb078AlphaDummy907 h))).fv ∪ ((Class.cv (nb078AlphaDummy908 h))).fv) :=
  by
  simpa only [nb078AlphaDummy912] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy907 h))).fv ∪ ((Class.cv (nb078AlphaDummy908 h))).fv)
      0

theorem nb078_fresh_1035 (h : Var) :
    (nb078AlphaDummy918 h) ∉
      (((Class.cv (nb078AlphaDummy908 h))).fv ∪ ((Class.cv (nb078AlphaDummy908 h))).fv) :=
  by
  simpa only [nb078AlphaDummy918] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy908 h))).fv ∪ ((Class.cv (nb078AlphaDummy908 h))).fv)
      0

theorem nb078_fresh_1036 :
    (nb078AlphaDummy933) ∉ (((Class.cv (nb078AlphaDummy926))).fv) := by
  simpa only [nb078AlphaDummy933] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy926))).fv) 0

theorem nb078_fresh_1037 :
    (nb078AlphaDummy934) ∉ (((Class.cv (nb078AlphaDummy926))).fv) := by
  simpa only [nb078AlphaDummy934] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy926))).fv) 1

theorem nb078_distinct_1038 : (nb078AlphaDummy933) ≠ (nb078AlphaDummy934) := by
  simpa only [nb078AlphaDummy933, nb078AlphaDummy934] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy926))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1039 (h : Var) :
    (nb078AlphaDummy935 h) ∉ (((Class.cv (nb078AlphaDummy928 h))).fv) := by
  simpa only [nb078AlphaDummy935] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy928 h))).fv) 0

theorem nb078_fresh_1040 (h : Var) :
    (nb078AlphaDummy936 h) ∉ (((Class.cv (nb078AlphaDummy928 h))).fv) := by
  simpa only [nb078AlphaDummy936] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy928 h))).fv) 1

theorem nb078_distinct_1041 (h : Var) :
    (nb078AlphaDummy935 h) ≠ (nb078AlphaDummy936 h) := by
  simpa only [nb078AlphaDummy935, nb078AlphaDummy936] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy928 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1042 :
    (nb078AlphaDummy939) ∉
      (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy939] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_1043 :
    (nb078AlphaDummy940) ∉
      (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy940] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_1044 :
    (nb078AlphaDummy941) ∉
      (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy941] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_1045 : (nb078AlphaDummy939) ≠ (nb078AlphaDummy940) := by
  simpa only [nb078AlphaDummy939, nb078AlphaDummy940] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1046 : (nb078AlphaDummy939) ≠ (nb078AlphaDummy941) := by
  simpa only [nb078AlphaDummy939, nb078AlphaDummy941] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1047 : (nb078AlphaDummy940) ≠ (nb078AlphaDummy941) := by
  simpa only [nb078AlphaDummy940, nb078AlphaDummy941] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1048 (h : Var) :
    (nb078AlphaDummy942 h) ∉
      (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy942] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_1049 (h : Var) :
    (nb078AlphaDummy943 h) ∉
      (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy943] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_1050 (h : Var) :
    (nb078AlphaDummy944 h) ∉
      (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy944] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_1051 (h : Var) :
    (nb078AlphaDummy942 h) ≠ (nb078AlphaDummy943 h) := by
  simpa only [nb078AlphaDummy942, nb078AlphaDummy943] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1052 (h : Var) :
    (nb078AlphaDummy942 h) ≠ (nb078AlphaDummy944 h) := by
  simpa only [nb078AlphaDummy942, nb078AlphaDummy944] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1053 (h : Var) :
    (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy944 h) := by
  simpa only [nb078AlphaDummy943, nb078AlphaDummy944] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1054 :
    (nb078AlphaDummy951) ∉
      (((Class.cv (nb078AlphaDummy940))).fv ∪ ((Class.cv (nb078AlphaDummy940))).fv) :=
  by
  simpa only [nb078AlphaDummy951] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy940))).fv ∪ ((Class.cv (nb078AlphaDummy940))).fv)
      0

theorem nb078_fresh_1055 :
    (nb078AlphaDummy947) ∉
      (((Class.cv (nb078AlphaDummy940))).fv ∪ ((Class.cv (nb078AlphaDummy941))).fv) :=
  by
  simpa only [nb078AlphaDummy947] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy940))).fv ∪ ((Class.cv (nb078AlphaDummy941))).fv)
      0

theorem nb078_fresh_1056 :
    (nb078AlphaDummy953) ∉
      (((Class.cv (nb078AlphaDummy941))).fv ∪ ((Class.cv (nb078AlphaDummy941))).fv) :=
  by
  simpa only [nb078AlphaDummy953] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy941))).fv ∪ ((Class.cv (nb078AlphaDummy941))).fv)
      0

theorem nb078_fresh_1057 (h : Var) :
    (nb078AlphaDummy952 h) ∉
      (((Class.cv (nb078AlphaDummy943 h))).fv ∪ ((Class.cv (nb078AlphaDummy943 h))).fv) :=
  by
  simpa only [nb078AlphaDummy952] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy943 h))).fv ∪ ((Class.cv (nb078AlphaDummy943 h))).fv)
      0

theorem nb078_fresh_1058 (h : Var) :
    (nb078AlphaDummy948 h) ∉
      (((Class.cv (nb078AlphaDummy943 h))).fv ∪ ((Class.cv (nb078AlphaDummy944 h))).fv) :=
  by
  simpa only [nb078AlphaDummy948] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy943 h))).fv ∪ ((Class.cv (nb078AlphaDummy944 h))).fv)
      0

theorem nb078_fresh_1059 (h : Var) :
    (nb078AlphaDummy954 h) ∉
      (((Class.cv (nb078AlphaDummy944 h))).fv ∪ ((Class.cv (nb078AlphaDummy944 h))).fv) :=
  by
  simpa only [nb078AlphaDummy954] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy944 h))).fv ∪ ((Class.cv (nb078AlphaDummy944 h))).fv)
      0

theorem nb078_fresh_1060 :
    (nb078AlphaDummy965) ∉
      (((Class.cv (nb078AlphaDummy962))).fv ∪ ((Class.cv (nb078AlphaDummy961))).fv) :=
  by
  simpa only [nb078AlphaDummy965] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy962))).fv ∪ ((Class.cv (nb078AlphaDummy961))).fv)
      0

theorem nb078_fresh_1061 :
    (nb078AlphaDummy966) ∉
      (((Class.cv (nb078AlphaDummy962))).fv ∪ ((Class.cv (nb078AlphaDummy961))).fv) :=
  by
  simpa only [nb078AlphaDummy966] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy962))).fv ∪ ((Class.cv (nb078AlphaDummy961))).fv)
      1

theorem nb078_distinct_1062 : (nb078AlphaDummy965) ≠ (nb078AlphaDummy966) := by
  simpa only [nb078AlphaDummy965, nb078AlphaDummy966] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy962))).fv ∪ ((Class.cv (nb078AlphaDummy961))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1063 (h : Var) :
    (nb078AlphaDummy967 h) ∉
      (((Class.cv (nb078AlphaDummy964 h))).fv ∪ ((Class.cv (nb078AlphaDummy963 h))).fv) :=
  by
  simpa only [nb078AlphaDummy967] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy964 h))).fv ∪ ((Class.cv (nb078AlphaDummy963 h))).fv)
      0

theorem nb078_fresh_1064 (h : Var) :
    (nb078AlphaDummy968 h) ∉
      (((Class.cv (nb078AlphaDummy964 h))).fv ∪ ((Class.cv (nb078AlphaDummy963 h))).fv) :=
  by
  simpa only [nb078AlphaDummy968] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy964 h))).fv ∪ ((Class.cv (nb078AlphaDummy963 h))).fv)
      1

theorem nb078_distinct_1065 (h : Var) :
    (nb078AlphaDummy967 h) ≠ (nb078AlphaDummy968 h) := by
  simpa only [nb078AlphaDummy967, nb078AlphaDummy968] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy964 h))).fv ∪
        ((Class.cv (nb078AlphaDummy963 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1066 :
    (nb078AlphaDummy973) ∉ (((Class.cv (nb078AlphaDummy966))).fv) := by
  simpa only [nb078AlphaDummy973] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy966))).fv) 0

theorem nb078_fresh_1067 :
    (nb078AlphaDummy974) ∉ (((Class.cv (nb078AlphaDummy966))).fv) := by
  simpa only [nb078AlphaDummy974] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy966))).fv) 1

theorem nb078_distinct_1068 : (nb078AlphaDummy973) ≠ (nb078AlphaDummy974) := by
  simpa only [nb078AlphaDummy973, nb078AlphaDummy974] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy966))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1069 (h : Var) :
    (nb078AlphaDummy975 h) ∉ (((Class.cv (nb078AlphaDummy968 h))).fv) := by
  simpa only [nb078AlphaDummy975] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy968 h))).fv) 0

theorem nb078_fresh_1070 (h : Var) :
    (nb078AlphaDummy976 h) ∉ (((Class.cv (nb078AlphaDummy968 h))).fv) := by
  simpa only [nb078AlphaDummy976] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy968 h))).fv) 1

theorem nb078_distinct_1071 (h : Var) :
    (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy976 h) := by
  simpa only [nb078AlphaDummy975, nb078AlphaDummy976] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy968 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_1072 :
    (nb078AlphaDummy979) ∉
      (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy979] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_1073 :
    (nb078AlphaDummy980) ∉
      (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy980] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_1074 :
    (nb078AlphaDummy981) ∉
      (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy981] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_1075 : (nb078AlphaDummy979) ≠ (nb078AlphaDummy980) := by
  simpa only [nb078AlphaDummy979, nb078AlphaDummy980] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1076 : (nb078AlphaDummy979) ≠ (nb078AlphaDummy981) := by
  simpa only [nb078AlphaDummy979, nb078AlphaDummy981] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1077 : (nb078AlphaDummy980) ≠ (nb078AlphaDummy981) := by
  simpa only [nb078AlphaDummy980, nb078AlphaDummy981] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1078 (h : Var) :
    (nb078AlphaDummy982 h) ∉
      (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy982] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_1079 (h : Var) :
    (nb078AlphaDummy983 h) ∉
      (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy983] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_1080 (h : Var) :
    (nb078AlphaDummy984 h) ∉
      (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy984] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_1081 (h : Var) :
    (nb078AlphaDummy982 h) ≠ (nb078AlphaDummy983 h) := by
  simpa only [nb078AlphaDummy982, nb078AlphaDummy983] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_1082 (h : Var) :
    (nb078AlphaDummy982 h) ≠ (nb078AlphaDummy984 h) := by
  simpa only [nb078AlphaDummy982, nb078AlphaDummy984] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_1083 (h : Var) :
    (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy984 h) := by
  simpa only [nb078AlphaDummy983, nb078AlphaDummy984] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_1084 :
    (nb078AlphaDummy991) ∉
      (((Class.cv (nb078AlphaDummy980))).fv ∪ ((Class.cv (nb078AlphaDummy980))).fv) :=
  by
  simpa only [nb078AlphaDummy991] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy980))).fv ∪ ((Class.cv (nb078AlphaDummy980))).fv)
      0

theorem nb078_fresh_1085 :
    (nb078AlphaDummy987) ∉
      (((Class.cv (nb078AlphaDummy980))).fv ∪ ((Class.cv (nb078AlphaDummy981))).fv) :=
  by
  simpa only [nb078AlphaDummy987] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy980))).fv ∪ ((Class.cv (nb078AlphaDummy981))).fv)
      0

theorem nb078_fresh_1086 :
    (nb078AlphaDummy993) ∉
      (((Class.cv (nb078AlphaDummy981))).fv ∪ ((Class.cv (nb078AlphaDummy981))).fv) :=
  by
  simpa only [nb078AlphaDummy993] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy981))).fv ∪ ((Class.cv (nb078AlphaDummy981))).fv)
      0

theorem nb078_fresh_1087 (h : Var) :
    (nb078AlphaDummy992 h) ∉
      (((Class.cv (nb078AlphaDummy983 h))).fv ∪ ((Class.cv (nb078AlphaDummy983 h))).fv) :=
  by
  simpa only [nb078AlphaDummy992] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy983 h))).fv ∪ ((Class.cv (nb078AlphaDummy983 h))).fv)
      0

theorem nb078_fresh_1088 (h : Var) :
    (nb078AlphaDummy988 h) ∉
      (((Class.cv (nb078AlphaDummy983 h))).fv ∪ ((Class.cv (nb078AlphaDummy984 h))).fv) :=
  by
  simpa only [nb078AlphaDummy988] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy983 h))).fv ∪ ((Class.cv (nb078AlphaDummy984 h))).fv)
      0

theorem nb078_fresh_1089 (h : Var) :
    (nb078AlphaDummy994 h) ∉
      (((Class.cv (nb078AlphaDummy984 h))).fv ∪ ((Class.cv (nb078AlphaDummy984 h))).fv) :=
  by
  simpa only [nb078AlphaDummy994] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy984 h))).fv ∪ ((Class.cv (nb078AlphaDummy984 h))).fv)
      0

theorem nb078_fresh_1090 (f : Var) : (nb078AlphaDummy091 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb078AlphaDummy091] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb078_fresh_1091 (f : Var) : (nb078AlphaDummy092 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb078AlphaDummy092] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb078_distinct_1092 (f : Var) :
    (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy092 f) := by
  simpa only [nb078AlphaDummy091, nb078AlphaDummy092] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1093 (f : Var) :
    (nb078AlphaDummy012 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb078AlphaDummy012] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0

theorem nb078_fresh_1094 (f : Var) :
    (nb078AlphaDummy013 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb078AlphaDummy013] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1

theorem nb078_fresh_1095 (f : Var) :
    (nb078AlphaDummy014 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb078AlphaDummy014] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2

theorem nb078_distinct_1096 (f : Var) :
    (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy013 f) := by
  simpa only [nb078AlphaDummy012, nb078AlphaDummy013] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_distinct_1097 (f : Var) :
    (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy014 f) := by
  simpa only [nb078AlphaDummy012, nb078AlphaDummy014] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb078_distinct_1098 (f : Var) :
    (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy014 f) := by
  simpa only [nb078AlphaDummy013, nb078AlphaDummy014] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb078_fresh_1099 (f : Var) :
    (nb078AlphaDummy245 f) ∉ (((Class.cv f)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy245] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCvv)).fv) 0

theorem nb078_fresh_1100 (f : Var) :
    (nb078AlphaDummy246 f) ∉ (((Class.cv f)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy246] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCvv)).fv) 1

theorem nb078_distinct_1101 (f : Var) :
    (nb078AlphaDummy245 f) ≠ (nb078AlphaDummy246 f) := by
  simpa only [nb078AlphaDummy245, nb078AlphaDummy246] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1102 (g : Var) : (nb078AlphaDummy369 g) ∉ (((Class.cv g)).fv) := by
  simpa only [nb078AlphaDummy369] using freshVar_not_mem (((Class.cv g)).fv) 0

theorem nb078_fresh_1103 (g : Var) : (nb078AlphaDummy370 g) ∉ (((Class.cv g)).fv) := by
  simpa only [nb078AlphaDummy370] using freshVar_not_mem (((Class.cv g)).fv) 1

theorem nb078_distinct_1104 (g : Var) :
    (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy370 g) := by
  simpa only [nb078AlphaDummy369, nb078AlphaDummy370] using
    (freshVar_injective (((Class.cv g)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1105 (g : Var) :
    (nb078AlphaDummy290 g) ∉ (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) := by
  simpa only [nb078AlphaDummy290] using
    freshVar_not_mem (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) 0

theorem nb078_fresh_1106 (g : Var) :
    (nb078AlphaDummy291 g) ∉ (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) := by
  simpa only [nb078AlphaDummy291] using
    freshVar_not_mem (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) 1

theorem nb078_fresh_1107 (g : Var) :
    (nb078AlphaDummy292 g) ∉ (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) := by
  simpa only [nb078AlphaDummy292] using
    freshVar_not_mem (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) 2

theorem nb078_distinct_1108 (g : Var) :
    (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy291 g) := by
  simpa only [nb078AlphaDummy290, nb078AlphaDummy291] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_distinct_1109 (g : Var) :
    (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy292 g) := by
  simpa only [nb078AlphaDummy290, nb078AlphaDummy292] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb078_distinct_1110 (g : Var) :
    (nb078AlphaDummy291 g) ≠ (nb078AlphaDummy292 g) := by
  simpa only [nb078AlphaDummy291, nb078AlphaDummy292] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb078_fresh_1111 (g : Var) :
    (nb078AlphaDummy527 g) ∉ (((Class.cv g)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy527] using
    freshVar_not_mem (((Class.cv g)).fv ∪ ((synCvv)).fv) 0

theorem nb078_fresh_1112 (g : Var) :
    (nb078AlphaDummy528 g) ∉ (((Class.cv g)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy528] using
    freshVar_not_mem (((Class.cv g)).fv ∪ ((synCvv)).fv) 1

theorem nb078_distinct_1113 (g : Var) :
    (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy528 g) := by
  simpa only [nb078AlphaDummy527, nb078AlphaDummy528] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((synCvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1114 (h : Var) : (nb078AlphaDummy849 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb078AlphaDummy849] using freshVar_not_mem (((Class.cv h)).fv) 0

theorem nb078_fresh_1115 (h : Var) : (nb078AlphaDummy850 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb078AlphaDummy850] using freshVar_not_mem (((Class.cv h)).fv) 1

theorem nb078_distinct_1116 (h : Var) :
    (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy850 h) := by
  simpa only [nb078AlphaDummy849, nb078AlphaDummy850] using
    (freshVar_injective (((Class.cv h)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1117 (h : Var) :
    (nb078AlphaDummy770 h) ∉ (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) := by
  simpa only [nb078AlphaDummy770] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 0

theorem nb078_fresh_1118 (h : Var) :
    (nb078AlphaDummy771 h) ∉ (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) := by
  simpa only [nb078AlphaDummy771] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 1

theorem nb078_fresh_1119 (h : Var) :
    (nb078AlphaDummy772 h) ∉ (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) := by
  simpa only [nb078AlphaDummy772] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 2

theorem nb078_distinct_1120 (h : Var) :
    (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy771 h) := by
  simpa only [nb078AlphaDummy770, nb078AlphaDummy771] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb078_distinct_1121 (h : Var) :
    (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy772 h) := by
  simpa only [nb078AlphaDummy770, nb078AlphaDummy772] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb078_distinct_1122 (h : Var) :
    (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy772 h) := by
  simpa only [nb078AlphaDummy771, nb078AlphaDummy772] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb078_fresh_1123 (h : Var) :
    (nb078AlphaDummy1007 h) ∉ (((Class.cv h)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy1007] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((synCvv)).fv) 0

theorem nb078_fresh_1124 (h : Var) :
    (nb078AlphaDummy1008 h) ∉ (((Class.cv h)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb078AlphaDummy1008] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((synCvv)).fv) 1

theorem nb078_distinct_1125 (h : Var) :
    (nb078AlphaDummy1007 h) ≠ (nb078AlphaDummy1008 h) := by
  simpa only [nb078AlphaDummy1007, nb078AlphaDummy1008] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((synCvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1126 :
    (nb078AlphaDummy029) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy025)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy025)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy025))).fv) :=
  by
  simpa only [nb078AlphaDummy029] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy025)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy025)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy025))).fv)
      0

theorem nb078_fresh_1127 (f : Var) :
    (nb078AlphaDummy030 f) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy027 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy027 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy027 f))).fv) :=
  by
  simpa only [nb078AlphaDummy030] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy027 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy027 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy027 f))).fv)
      0

theorem nb078_fresh_1128 :
    (nb078AlphaDummy065) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy061)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy061)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy061))).fv) :=
  by
  simpa only [nb078AlphaDummy065] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy061)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy061)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy061))).fv)
      0

theorem nb078_fresh_1129 (f : Var) :
    (nb078AlphaDummy066 f) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy063 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy063 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy063 f))).fv) :=
  by
  simpa only [nb078AlphaDummy066] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy063 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy063 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy063 f))).fv)
      0

theorem nb078_fresh_1130 :
    (nb078AlphaDummy1021) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1017)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1017)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1017))).fv) :=
  by
  simpa only [nb078AlphaDummy1021] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1017)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1017)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1017))).fv)
      0

theorem nb078_fresh_1131 (h : Var) :
    (nb078AlphaDummy1022 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1019 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1019 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1019 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1022] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1019 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1019 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1019 h))).fv)
      0

theorem nb078_fresh_1132 :
    (nb078AlphaDummy107) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy103)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy103)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy103))).fv) :=
  by
  simpa only [nb078AlphaDummy107] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy103)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy103)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy103))).fv)
      0

theorem nb078_fresh_1133 (f : Var) :
    (nb078AlphaDummy108 f) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy105 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy105 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy105 f))).fv) :=
  by
  simpa only [nb078AlphaDummy108] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy105 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy105 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy105 f))).fv)
      0

theorem nb078_fresh_1134 :
    (nb078AlphaDummy1069) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1065)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1065)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1065))).fv) :=
  by
  simpa only [nb078AlphaDummy1069] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1065)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1065)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1065))).fv)
      0

theorem nb078_fresh_1135 (h : Var) :
    (nb078AlphaDummy1070 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1067 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1067 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1067 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1070] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1067 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1067 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1067 h))).fv)
      0

theorem nb078_fresh_1136 :
    (nb078AlphaDummy1105) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1101)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1101)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1101))).fv) :=
  by
  simpa only [nb078AlphaDummy1105] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1101)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1101)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1101))).fv)
      0

theorem nb078_fresh_1137 (h : Var) :
    (nb078AlphaDummy1106 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1103 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1103 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1103 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1106] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1103 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1103 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1103 h))).fv)
      0

theorem nb078_fresh_1138 :
    (nb078AlphaDummy1147) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1143)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1143)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1143))).fv) :=
  by
  simpa only [nb078AlphaDummy1147] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1143)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1143)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1143))).fv)
      0

theorem nb078_fresh_1139 (h : Var) :
    (nb078AlphaDummy1148 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1145 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1145 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1145 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1148] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1145 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1145 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1145 h))).fv)
      0

theorem nb078_fresh_1140 :
    (nb078AlphaDummy1183) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1179)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1179)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1179))).fv) :=
  by
  simpa only [nb078AlphaDummy1183] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1179)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1179)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1179))).fv)
      0

theorem nb078_fresh_1141 (h : Var) :
    (nb078AlphaDummy1184 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1181 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1181 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1181 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1184] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1181 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1181 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1181 h))).fv)
      0

theorem nb078_fresh_1142 :
    (nb078AlphaDummy1219) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1215)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1215)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1215))).fv) :=
  by
  simpa only [nb078AlphaDummy1219] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1215)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1215)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1215))).fv)
      0

theorem nb078_fresh_1143 (h : Var) :
    (nb078AlphaDummy1220 h) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy1217 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1217 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1217 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1220] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy1217 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1217 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1217 h))).fv)
      0

theorem nb078_fresh_1144 :
    (nb078AlphaDummy143) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy139)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy139)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy139))).fv) :=
  by
  simpa only [nb078AlphaDummy143] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy139)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy139)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy139))).fv)
      0

theorem nb078_fresh_1145 (f : Var) :
    (nb078AlphaDummy144 f) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy141 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy141 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy141 f))).fv) :=
  by
  simpa only [nb078AlphaDummy144] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy141 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy141 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy141 f))).fv)
      0

theorem nb078_fresh_1146 :
    (nb078AlphaDummy179) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy175)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy175)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy175))).fv) :=
  by
  simpa only [nb078AlphaDummy179] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy175)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy175)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy175))).fv)
      0

theorem nb078_fresh_1147 (f : Var) :
    (nb078AlphaDummy180 f) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy177 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy177 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy177 f))).fv) :=
  by
  simpa only [nb078AlphaDummy180] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy177 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy177 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy177 f))).fv)
      0

theorem nb078_fresh_1148 :
    (nb078AlphaDummy219) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy215)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy215)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy215))).fv) :=
  by
  simpa only [nb078AlphaDummy219] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy215)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy215)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy215))).fv)
      0

theorem nb078_fresh_1149 (f : Var) :
    (nb078AlphaDummy220 f) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy217 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy217 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy217 f))).fv) :=
  by
  simpa only [nb078AlphaDummy220] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy217 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy217 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy217 f))).fv)
      0

theorem nb078_fresh_1150 :
    (nb078AlphaDummy259) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy255)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy255)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy255))).fv) :=
  by
  simpa only [nb078AlphaDummy259] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy255)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy255)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy255))).fv)
      0

theorem nb078_fresh_1151 (f : Var) :
    (nb078AlphaDummy260 f) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy257 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy257 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy257 f))).fv) :=
  by
  simpa only [nb078AlphaDummy260] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy257 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy257 f)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy257 f))).fv)
      0

theorem nb078_fresh_1152 :
    (nb078AlphaDummy307) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy303)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy303)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy303))).fv) :=
  by
  simpa only [nb078AlphaDummy307] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy303)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy303)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy303))).fv)
      0

theorem nb078_fresh_1153 (g : Var) :
    (nb078AlphaDummy308 g) ∉
      (((Wff.classMem (Class.cv (nb078AlphaDummy305 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy305 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy305 g))).fv) :=
  by
  simpa only [nb078AlphaDummy308] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb078AlphaDummy305 g)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy305 g)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy305 g))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
