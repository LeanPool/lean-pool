/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part014`. -/


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

theorem nb090_fresh_922 (A : Class) :
    (nb090_alpha_dummy_271 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_262 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_263 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_271] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_262 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_263 A)))).fv)
      0

theorem nb090_fresh_923 (h : Var) :
    (nb090_alpha_dummy_272 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_265 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_266 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_272] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_265 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_266 h)))).fv)
      0

theorem nb090_fresh_924 (A : Class) :
    (nb090_alpha_dummy_315 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_306 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_307 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_315] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_306 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_307 A)))).fv)
      0

theorem nb090_fresh_925 (u : Var) :
    (nb090_alpha_dummy_316 u) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_309 u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_310 u)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_316] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_309 u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_310 u)))).fv)
      0

theorem nb090_fresh_926 (A : Class) :
    (nb090_alpha_dummy_361 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_352 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_353 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_361] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_352 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_353 A)))).fv)
      0

theorem nb090_fresh_927 (h : Var) :
    (nb090_alpha_dummy_362 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_355 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_356 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_362] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_355 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_356 h)))).fv)
      0

theorem nb090_fresh_928 (A : Class) :
    (nb090_alpha_dummy_405 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_396 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_397 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_405] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_396 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_397 A)))).fv)
      0

theorem nb090_fresh_929 (v : Var) :
    (nb090_alpha_dummy_406 v) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_399 v)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_400 v)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_406] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_399 v)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_400 v)))).fv)
      0

theorem nb090_fresh_930 (A : Class) :
    (nb090_alpha_dummy_455 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_446 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_447 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_455] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_446 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_447 A)))).fv)
      0

theorem nb090_fresh_931 (h : Var) :
    (nb090_alpha_dummy_456 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_449 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_450 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_456] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_449 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_450 h)))).fv)
      0

theorem nb090_fresh_932 (A : Class) :
    (nb090_alpha_dummy_491 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_482 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_483 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_491] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_482 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_483 A)))).fv)
      0

theorem nb090_fresh_933 (h : Var) :
    (nb090_alpha_dummy_492 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_485 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_486 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_492] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_485 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_486 h)))).fv)
      0

theorem nb090_fresh_934 (A : Class) :
    (nb090_alpha_dummy_533 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_524 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_525 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_533] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_524 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_525 A)))).fv)
      0

theorem nb090_fresh_935 (h : Var) :
    (nb090_alpha_dummy_534 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_527 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_528 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_534] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_527 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_528 h)))).fv)
      0

theorem nb090_fresh_936 (A : Class) :
    (nb090_alpha_dummy_569 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_560 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_561 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_569] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_560 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_561 A)))).fv)
      0

theorem nb090_fresh_937 (h : Var) :
    (nb090_alpha_dummy_570 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_563 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_564 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_570] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_563 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_564 h)))).fv)
      0

theorem nb090_fresh_938 (A : Class) :
    (nb090_alpha_dummy_605 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_596 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_597 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_605] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_596 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_597 A)))).fv)
      0

theorem nb090_fresh_939 (h : Var) :
    (nb090_alpha_dummy_606 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_599 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_600 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_606] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_599 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_600 h)))).fv)
      0

theorem nb090_fresh_940 (A : Class) :
    (nb090_alpha_dummy_641 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_632 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_633 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_641] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_632 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_633 A)))).fv)
      0

theorem nb090_fresh_941 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_642 v u h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_635 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_642] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_635 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_636 v u h)))).fv)
      0

theorem nb090_fresh_942 (A : Class) :
    (nb090_alpha_dummy_685 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_676 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_677 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_685] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_676 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_677 A)))).fv)
      0

theorem nb090_fresh_943 (u : Var) :
    (nb090_alpha_dummy_686 u) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_679 u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_680 u)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_686] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_679 u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_680 u)))).fv)
      0

theorem nb090_fresh_944 (A : Class) :
    (nb090_alpha_dummy_739 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_730 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_731 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_739] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_730 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_731 A)))).fv)
      0

theorem nb090_fresh_945 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_740 v u h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_733 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_740] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_733 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_734 v u h)))).fv)
      0

theorem nb090_fresh_946 (A : Class) :
    (nb090_alpha_dummy_769 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_760 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_761 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_769] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_760 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_761 A)))).fv)
      0

theorem nb090_fresh_947 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_770 v u h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_763 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_770] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_763 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_764 v u h)))).fv)
      0

theorem nb090_fresh_948 (A : Class) :
    (nb090_alpha_dummy_809 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_800 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_801 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_809] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_800 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_801 A)))).fv)
      0

theorem nb090_fresh_949 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_810 v u h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_803 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_810] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_803 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_804 v u h)))).fv)
      0

theorem nb090_fresh_950 (A : Class) :
    (nb090_alpha_dummy_859 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_850 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_851 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_859] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_850 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_851 A)))).fv)
      0

theorem nb090_fresh_951 (v : Var) :
    (nb090_alpha_dummy_860 v) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_853 v)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_854 v)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_860] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_853 v)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_854 v)))).fv)
      0

theorem nb090_fresh_952 (A : Class) :
    (nb090_alpha_dummy_037 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_953 (v : Var) (u : Var) :
    (nb090_alpha_dummy_038 v u) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_954 (A : Class) :
    (nb090_alpha_dummy_089 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_089] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_955 (h : Var) :
    (nb090_alpha_dummy_090 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_090] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_956 (A : Class) :
    (nb090_alpha_dummy_125 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_125] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_957 (h : Var) :
    (nb090_alpha_dummy_126 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_126] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_958 (A : Class) :
    (nb090_alpha_dummy_167 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_167] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_959 (h : Var) :
    (nb090_alpha_dummy_168 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_168] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_960 (A : Class) :
    (nb090_alpha_dummy_203 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_203] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_961 (h : Var) :
    (nb090_alpha_dummy_204 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_204] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_962 (A : Class) :
    (nb090_alpha_dummy_239 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_239] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_963 (h : Var) :
    (nb090_alpha_dummy_240 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_240] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_964 (A : Class) :
    (nb090_alpha_dummy_279 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_279] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_965 (h : Var) :
    (nb090_alpha_dummy_280 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_280] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_966 (A : Class) :
    (nb090_alpha_dummy_323 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_323] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_967 (u : Var) :
    (nb090_alpha_dummy_324 u) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_324] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_968 (A : Class) :
    (nb090_alpha_dummy_369 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_369] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_969 (h : Var) :
    (nb090_alpha_dummy_370 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_370] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_970 (A : Class) :
    (nb090_alpha_dummy_413 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_413] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_971 (v : Var) :
    (nb090_alpha_dummy_414 v) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_414] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_972 (A : Class) :
    (nb090_alpha_dummy_463 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_463] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_973 (h : Var) :
    (nb090_alpha_dummy_464 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_464] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_974 (A : Class) :
    (nb090_alpha_dummy_499 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_499] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_975 (h : Var) :
    (nb090_alpha_dummy_500 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_500] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_976 (A : Class) :
    (nb090_alpha_dummy_541 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_541] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_977 (h : Var) :
    (nb090_alpha_dummy_542 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_542] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_978 (A : Class) :
    (nb090_alpha_dummy_577 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_577] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_979 (h : Var) :
    (nb090_alpha_dummy_578 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_578] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_980 (A : Class) :
    (nb090_alpha_dummy_613 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_613] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_981 (h : Var) :
    (nb090_alpha_dummy_614 h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_614] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_982 (A : Class) :
    (nb090_alpha_dummy_649 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_649] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_983 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_650 v u h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_650] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_984 (A : Class) :
    (nb090_alpha_dummy_693 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_693] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_985 (u : Var) :
    (nb090_alpha_dummy_694 u) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_694] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_986 (A : Class) :
    (nb090_alpha_dummy_823 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_823] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_987 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_824 v u h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_824] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_988 (A : Class) :
    (nb090_alpha_dummy_747 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_747] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_989 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_748 v u h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_748] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_990 (A : Class) :
    (nb090_alpha_dummy_817 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_817] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_991 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_818 v u h) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_818] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_992 (A : Class) :
    (nb090_alpha_dummy_867 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_867] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_993 (v : Var) :
    (nb090_alpha_dummy_868 v) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_868] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb090_fresh_994 (A : Class) :
    (nb090_alpha_dummy_699 A) ∉
      (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪
        ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_042 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_699] using
    freshVar_not_mem
      (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪
        ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_042 A)))).fv)
      0

theorem nb090_fresh_995 (A : Class) :
    (nb090_alpha_dummy_700 A) ∉
      (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪
        ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_042 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_700] using
    freshVar_not_mem
      (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪
        ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_042 A)))).fv)
      1

theorem nb090_distinct_996 (A : Class) :
    (nb090_alpha_dummy_699 A) ≠ (nb090_alpha_dummy_700 A) := by
  simpa only [nb090_alpha_dummy_699, nb090_alpha_dummy_700] using
    (freshVar_injective (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪
        ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_042 A)))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_997 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_701 v u h) ∉
      (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪
        ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_701] using
    freshVar_not_mem
      (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪
        ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv)
      0

theorem nb090_fresh_998 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_702 v u h) ∉
      (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪
        ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_702] using
    freshVar_not_mem
      (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪
        ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv)
      1

theorem nb090_distinct_999 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_701 v u h) ≠ (nb090_alpha_dummy_702 v u h) := by
  simpa only [nb090_alpha_dummy_701, nb090_alpha_dummy_702] using
    (freshVar_injective (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪
        ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_1000 (A : Class) :
    (nb090_alpha_dummy_025 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_020 A))
            (Class.cv (nb090_alpha_dummy_021 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_020 A))
            (Class.cv (nb090_alpha_dummy_021 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_020 A))
            (Class.cv (nb090_alpha_dummy_021 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_020 A))
            (Class.cv (nb090_alpha_dummy_021 A)))).fv)
      0

theorem nb090_fresh_1001 (v : Var) (u : Var) :
    (nb090_alpha_dummy_026 v u) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u))
            (Class.cv (nb090_alpha_dummy_024 v u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u))
            (Class.cv (nb090_alpha_dummy_024 v u)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u))
            (Class.cv (nb090_alpha_dummy_024 v u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u))
            (Class.cv (nb090_alpha_dummy_024 v u)))).fv)
      0

theorem nb090_fresh_1002 (A : Class) :
    (nb090_alpha_dummy_077 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_072 A))
            (Class.cv (nb090_alpha_dummy_073 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_072 A))
            (Class.cv (nb090_alpha_dummy_073 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_072 A))
            (Class.cv (nb090_alpha_dummy_073 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_072 A))
            (Class.cv (nb090_alpha_dummy_073 A)))).fv)
      0

theorem nb090_fresh_1003 (h : Var) :
    (nb090_alpha_dummy_078 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_075 h))
            (Class.cv (nb090_alpha_dummy_076 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_075 h))
            (Class.cv (nb090_alpha_dummy_076 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_078] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_075 h))
            (Class.cv (nb090_alpha_dummy_076 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_075 h))
            (Class.cv (nb090_alpha_dummy_076 h)))).fv)
      0

theorem nb090_fresh_1004 (A : Class) :
    (nb090_alpha_dummy_113 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_108 A))
            (Class.cv (nb090_alpha_dummy_109 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_108 A))
            (Class.cv (nb090_alpha_dummy_109 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_113] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_108 A))
            (Class.cv (nb090_alpha_dummy_109 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_108 A))
            (Class.cv (nb090_alpha_dummy_109 A)))).fv)
      0

theorem nb090_fresh_1005 (h : Var) :
    (nb090_alpha_dummy_114 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_111 h))
            (Class.cv (nb090_alpha_dummy_112 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_111 h))
            (Class.cv (nb090_alpha_dummy_112 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_114] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_111 h))
            (Class.cv (nb090_alpha_dummy_112 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_111 h))
            (Class.cv (nb090_alpha_dummy_112 h)))).fv)
      0

theorem nb090_fresh_1006 (A : Class) :
    (nb090_alpha_dummy_155 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_150 A))
            (Class.cv (nb090_alpha_dummy_151 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_150 A))
            (Class.cv (nb090_alpha_dummy_151 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_155] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_150 A))
            (Class.cv (nb090_alpha_dummy_151 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_150 A))
            (Class.cv (nb090_alpha_dummy_151 A)))).fv)
      0

theorem nb090_fresh_1007 (h : Var) :
    (nb090_alpha_dummy_156 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_153 h))
            (Class.cv (nb090_alpha_dummy_154 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_153 h))
            (Class.cv (nb090_alpha_dummy_154 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_156] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_153 h))
            (Class.cv (nb090_alpha_dummy_154 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_153 h))
            (Class.cv (nb090_alpha_dummy_154 h)))).fv)
      0

theorem nb090_fresh_1008 (A : Class) :
    (nb090_alpha_dummy_191 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_186 A))
            (Class.cv (nb090_alpha_dummy_187 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_186 A))
            (Class.cv (nb090_alpha_dummy_187 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_191] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_186 A))
            (Class.cv (nb090_alpha_dummy_187 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_186 A))
            (Class.cv (nb090_alpha_dummy_187 A)))).fv)
      0

theorem nb090_fresh_1009 (h : Var) :
    (nb090_alpha_dummy_192 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_189 h))
            (Class.cv (nb090_alpha_dummy_190 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_189 h))
            (Class.cv (nb090_alpha_dummy_190 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_192] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_189 h))
            (Class.cv (nb090_alpha_dummy_190 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_189 h))
            (Class.cv (nb090_alpha_dummy_190 h)))).fv)
      0

theorem nb090_fresh_1010 (A : Class) :
    (nb090_alpha_dummy_227 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_222 A))
            (Class.cv (nb090_alpha_dummy_223 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_222 A))
            (Class.cv (nb090_alpha_dummy_223 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_227] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_222 A))
            (Class.cv (nb090_alpha_dummy_223 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_222 A))
            (Class.cv (nb090_alpha_dummy_223 A)))).fv)
      0

theorem nb090_fresh_1011 (h : Var) :
    (nb090_alpha_dummy_228 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_225 h))
            (Class.cv (nb090_alpha_dummy_226 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_225 h))
            (Class.cv (nb090_alpha_dummy_226 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_228] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_225 h))
            (Class.cv (nb090_alpha_dummy_226 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_225 h))
            (Class.cv (nb090_alpha_dummy_226 h)))).fv)
      0

theorem nb090_fresh_1012 (A : Class) :
    (nb090_alpha_dummy_267 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_262 A))
            (Class.cv (nb090_alpha_dummy_263 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_262 A))
            (Class.cv (nb090_alpha_dummy_263 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_267] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_262 A))
            (Class.cv (nb090_alpha_dummy_263 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_262 A))
            (Class.cv (nb090_alpha_dummy_263 A)))).fv)
      0

theorem nb090_fresh_1013 (h : Var) :
    (nb090_alpha_dummy_268 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_265 h))
            (Class.cv (nb090_alpha_dummy_266 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_265 h))
            (Class.cv (nb090_alpha_dummy_266 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_268] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_265 h))
            (Class.cv (nb090_alpha_dummy_266 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_265 h))
            (Class.cv (nb090_alpha_dummy_266 h)))).fv)
      0

theorem nb090_fresh_1014 (A : Class) :
    (nb090_alpha_dummy_311 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_306 A))
            (Class.cv (nb090_alpha_dummy_307 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_306 A))
            (Class.cv (nb090_alpha_dummy_307 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_311] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_306 A))
            (Class.cv (nb090_alpha_dummy_307 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_306 A))
            (Class.cv (nb090_alpha_dummy_307 A)))).fv)
      0

theorem nb090_fresh_1015 (u : Var) :
    (nb090_alpha_dummy_312 u) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_309 u))
            (Class.cv (nb090_alpha_dummy_310 u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_309 u))
            (Class.cv (nb090_alpha_dummy_310 u)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_312] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_309 u))
            (Class.cv (nb090_alpha_dummy_310 u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_309 u))
            (Class.cv (nb090_alpha_dummy_310 u)))).fv)
      0

theorem nb090_fresh_1016 (A : Class) :
    (nb090_alpha_dummy_357 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_352 A))
            (Class.cv (nb090_alpha_dummy_353 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_352 A))
            (Class.cv (nb090_alpha_dummy_353 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_357] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_352 A))
            (Class.cv (nb090_alpha_dummy_353 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_352 A))
            (Class.cv (nb090_alpha_dummy_353 A)))).fv)
      0

theorem nb090_fresh_1017 (h : Var) :
    (nb090_alpha_dummy_358 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_355 h))
            (Class.cv (nb090_alpha_dummy_356 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_355 h))
            (Class.cv (nb090_alpha_dummy_356 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_358] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_355 h))
            (Class.cv (nb090_alpha_dummy_356 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_355 h))
            (Class.cv (nb090_alpha_dummy_356 h)))).fv)
      0

theorem nb090_fresh_1018 (A : Class) :
    (nb090_alpha_dummy_401 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_396 A))
            (Class.cv (nb090_alpha_dummy_397 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_396 A))
            (Class.cv (nb090_alpha_dummy_397 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_401] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_396 A))
            (Class.cv (nb090_alpha_dummy_397 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_396 A))
            (Class.cv (nb090_alpha_dummy_397 A)))).fv)
      0

theorem nb090_fresh_1019 (v : Var) :
    (nb090_alpha_dummy_402 v) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_399 v))
            (Class.cv (nb090_alpha_dummy_400 v)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_399 v))
            (Class.cv (nb090_alpha_dummy_400 v)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_402] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_399 v))
            (Class.cv (nb090_alpha_dummy_400 v)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_399 v))
            (Class.cv (nb090_alpha_dummy_400 v)))).fv)
      0

theorem nb090_fresh_1020 (A : Class) :
    (nb090_alpha_dummy_451 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_446 A))
            (Class.cv (nb090_alpha_dummy_447 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_446 A))
            (Class.cv (nb090_alpha_dummy_447 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_451] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_446 A))
            (Class.cv (nb090_alpha_dummy_447 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_446 A))
            (Class.cv (nb090_alpha_dummy_447 A)))).fv)
      0

theorem nb090_fresh_1021 (h : Var) :
    (nb090_alpha_dummy_452 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_449 h))
            (Class.cv (nb090_alpha_dummy_450 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_449 h))
            (Class.cv (nb090_alpha_dummy_450 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_452] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_449 h))
            (Class.cv (nb090_alpha_dummy_450 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_449 h))
            (Class.cv (nb090_alpha_dummy_450 h)))).fv)
      0

theorem nb090_fresh_1022 (A : Class) :
    (nb090_alpha_dummy_487 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_482 A))
            (Class.cv (nb090_alpha_dummy_483 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_482 A))
            (Class.cv (nb090_alpha_dummy_483 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_487] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_482 A))
            (Class.cv (nb090_alpha_dummy_483 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_482 A))
            (Class.cv (nb090_alpha_dummy_483 A)))).fv)
      0

theorem nb090_fresh_1023 (h : Var) :
    (nb090_alpha_dummy_488 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_485 h))
            (Class.cv (nb090_alpha_dummy_486 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_485 h))
            (Class.cv (nb090_alpha_dummy_486 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_488] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_485 h))
            (Class.cv (nb090_alpha_dummy_486 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_485 h))
            (Class.cv (nb090_alpha_dummy_486 h)))).fv)
      0

theorem nb090_fresh_1024 (A : Class) :
    (nb090_alpha_dummy_529 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_524 A))
            (Class.cv (nb090_alpha_dummy_525 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_524 A))
            (Class.cv (nb090_alpha_dummy_525 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_529] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_524 A))
            (Class.cv (nb090_alpha_dummy_525 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_524 A))
            (Class.cv (nb090_alpha_dummy_525 A)))).fv)
      0

theorem nb090_fresh_1025 (h : Var) :
    (nb090_alpha_dummy_530 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_527 h))
            (Class.cv (nb090_alpha_dummy_528 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_527 h))
            (Class.cv (nb090_alpha_dummy_528 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_530] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_527 h))
            (Class.cv (nb090_alpha_dummy_528 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_527 h))
            (Class.cv (nb090_alpha_dummy_528 h)))).fv)
      0

theorem nb090_fresh_1026 (A : Class) :
    (nb090_alpha_dummy_565 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_560 A))
            (Class.cv (nb090_alpha_dummy_561 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_560 A))
            (Class.cv (nb090_alpha_dummy_561 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_565] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_560 A))
            (Class.cv (nb090_alpha_dummy_561 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_560 A))
            (Class.cv (nb090_alpha_dummy_561 A)))).fv)
      0

theorem nb090_fresh_1027 (h : Var) :
    (nb090_alpha_dummy_566 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_563 h))
            (Class.cv (nb090_alpha_dummy_564 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_563 h))
            (Class.cv (nb090_alpha_dummy_564 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_566] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_563 h))
            (Class.cv (nb090_alpha_dummy_564 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_563 h))
            (Class.cv (nb090_alpha_dummy_564 h)))).fv)
      0

theorem nb090_fresh_1028 (A : Class) :
    (nb090_alpha_dummy_601 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_596 A))
            (Class.cv (nb090_alpha_dummy_597 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_596 A))
            (Class.cv (nb090_alpha_dummy_597 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_601] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_596 A))
            (Class.cv (nb090_alpha_dummy_597 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_596 A))
            (Class.cv (nb090_alpha_dummy_597 A)))).fv)
      0

theorem nb090_fresh_1029 (h : Var) :
    (nb090_alpha_dummy_602 h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_599 h))
            (Class.cv (nb090_alpha_dummy_600 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_599 h))
            (Class.cv (nb090_alpha_dummy_600 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_602] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_599 h))
            (Class.cv (nb090_alpha_dummy_600 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_599 h))
            (Class.cv (nb090_alpha_dummy_600 h)))).fv)
      0

theorem nb090_fresh_1030 (A : Class) :
    (nb090_alpha_dummy_637 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_632 A))
            (Class.cv (nb090_alpha_dummy_633 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_632 A))
            (Class.cv (nb090_alpha_dummy_633 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_637] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_632 A))
            (Class.cv (nb090_alpha_dummy_633 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_632 A))
            (Class.cv (nb090_alpha_dummy_633 A)))).fv)
      0

theorem nb090_fresh_1031 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_638 v u h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h))
            (Class.cv (nb090_alpha_dummy_636 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h))
            (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_638] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h))
            (Class.cv (nb090_alpha_dummy_636 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h))
            (Class.cv (nb090_alpha_dummy_636 v u h)))).fv)
      0

theorem nb090_fresh_1032 (A : Class) :
    (nb090_alpha_dummy_681 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_676 A))
            (Class.cv (nb090_alpha_dummy_677 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_676 A))
            (Class.cv (nb090_alpha_dummy_677 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_681] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_676 A))
            (Class.cv (nb090_alpha_dummy_677 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_676 A))
            (Class.cv (nb090_alpha_dummy_677 A)))).fv)
      0

theorem nb090_fresh_1033 (u : Var) :
    (nb090_alpha_dummy_682 u) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_679 u))
            (Class.cv (nb090_alpha_dummy_680 u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_679 u))
            (Class.cv (nb090_alpha_dummy_680 u)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_682] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_679 u))
            (Class.cv (nb090_alpha_dummy_680 u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_679 u))
            (Class.cv (nb090_alpha_dummy_680 u)))).fv)
      0

theorem nb090_fresh_1034 (A : Class) :
    (nb090_alpha_dummy_735 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_730 A))
            (Class.cv (nb090_alpha_dummy_731 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_730 A))
            (Class.cv (nb090_alpha_dummy_731 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_735] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_730 A))
            (Class.cv (nb090_alpha_dummy_731 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_730 A))
            (Class.cv (nb090_alpha_dummy_731 A)))).fv)
      0

theorem nb090_fresh_1035 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_736 v u h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h))
            (Class.cv (nb090_alpha_dummy_734 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h))
            (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_736] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h))
            (Class.cv (nb090_alpha_dummy_734 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h))
            (Class.cv (nb090_alpha_dummy_734 v u h)))).fv)
      0

theorem nb090_fresh_1036 (A : Class) :
    (nb090_alpha_dummy_765 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_760 A))
            (Class.cv (nb090_alpha_dummy_761 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_760 A))
            (Class.cv (nb090_alpha_dummy_761 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_765] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_760 A))
            (Class.cv (nb090_alpha_dummy_761 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_760 A))
            (Class.cv (nb090_alpha_dummy_761 A)))).fv)
      0

theorem nb090_fresh_1037 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_766 v u h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h))
            (Class.cv (nb090_alpha_dummy_764 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h))
            (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_766] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h))
            (Class.cv (nb090_alpha_dummy_764 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h))
            (Class.cv (nb090_alpha_dummy_764 v u h)))).fv)
      0

theorem nb090_fresh_1038 (A : Class) :
    (nb090_alpha_dummy_805 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_800 A))
            (Class.cv (nb090_alpha_dummy_801 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_800 A))
            (Class.cv (nb090_alpha_dummy_801 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_805] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_800 A))
            (Class.cv (nb090_alpha_dummy_801 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_800 A))
            (Class.cv (nb090_alpha_dummy_801 A)))).fv)
      0

theorem nb090_fresh_1039 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_806 v u h) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h))
            (Class.cv (nb090_alpha_dummy_804 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h))
            (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_806] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h))
            (Class.cv (nb090_alpha_dummy_804 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h))
            (Class.cv (nb090_alpha_dummy_804 v u h)))).fv)
      0

theorem nb090_fresh_1040 (A : Class) :
    (nb090_alpha_dummy_855 A) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_850 A))
            (Class.cv (nb090_alpha_dummy_851 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_850 A))
            (Class.cv (nb090_alpha_dummy_851 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_855] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_850 A))
            (Class.cv (nb090_alpha_dummy_851 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_850 A))
            (Class.cv (nb090_alpha_dummy_851 A)))).fv)
      0

theorem nb090_fresh_1041 (v : Var) :
    (nb090_alpha_dummy_856 v) ∉
      (((syn_cnin (Class.cv (nb090_alpha_dummy_853 v))
            (Class.cv (nb090_alpha_dummy_854 v)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_853 v))
            (Class.cv (nb090_alpha_dummy_854 v)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_856] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb090_alpha_dummy_853 v))
            (Class.cv (nb090_alpha_dummy_854 v)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_853 v))
            (Class.cv (nb090_alpha_dummy_854 v)))).fv)
      0

theorem nb090_fresh_1042 (A : Class) :
    (nb090_alpha_dummy_045 A) ∉
      (((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
              (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
              (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv) :=
  by
  simpa only [nb090_alpha_dummy_045] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
              (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
              (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv)
      0

theorem nb090_fresh_1043 (h : Var) :
    (nb090_alpha_dummy_046 h) ∉
      (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) :=
  by
  simpa only [nb090_alpha_dummy_046] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv)
      0

theorem nb090_fresh_1044 (A : Class) :
    (nb090_alpha_dummy_419 A) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
              (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
              (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv) :=
  by
  simpa only [nb090_alpha_dummy_419] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
              (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
              (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv)
      0

theorem nb090_fresh_1045 (h : Var) :
    (nb090_alpha_dummy_420 h) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv) :=
  by
  simpa only [nb090_alpha_dummy_420] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv)
      0

theorem nb090_fresh_1046 (A : Class) :
    (nb090_alpha_dummy_329 A) ∉
      (((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_329] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv)
      0

theorem nb090_fresh_1047 (v : Var) (h : Var) :
    (nb090_alpha_dummy_330 v h) ∉
      (((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_330] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv)
      0

theorem nb090_fresh_1048 (A : Class) :
    (nb090_alpha_dummy_039 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv)
      0

theorem nb090_fresh_1049 (v : Var) (u : Var) :
    (nb090_alpha_dummy_040 v u) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv)
      0

theorem nb090_fresh_1050 (A : Class) :
    (nb090_alpha_dummy_091 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_091] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv)
      0

theorem nb090_fresh_1051 (h : Var) :
    (nb090_alpha_dummy_092 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_092] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv)
      0

theorem nb090_fresh_1052 (A : Class) :
    (nb090_alpha_dummy_127 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_127] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv)
      0

theorem nb090_fresh_1053 (h : Var) :
    (nb090_alpha_dummy_128 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_128] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv)
      0

theorem nb090_fresh_1054 (A : Class) :
    (nb090_alpha_dummy_169 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_169] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv)
      0

theorem nb090_fresh_1055 (h : Var) :
    (nb090_alpha_dummy_170 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_170] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv)
      0

theorem nb090_fresh_1056 (A : Class) :
    (nb090_alpha_dummy_205 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_205] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv)
      0

theorem nb090_fresh_1057 (h : Var) :
    (nb090_alpha_dummy_206 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_206] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv)
      0

theorem nb090_fresh_1058 (A : Class) :
    (nb090_alpha_dummy_241 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_241] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv)
      0

theorem nb090_fresh_1059 (h : Var) :
    (nb090_alpha_dummy_242 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_242] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv)
      0

theorem nb090_fresh_1060 (A : Class) :
    (nb090_alpha_dummy_281 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_281] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv)
      0

theorem nb090_fresh_1061 (h : Var) :
    (nb090_alpha_dummy_282 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_282] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv)
      0

theorem nb090_fresh_1062 (A : Class) :
    (nb090_alpha_dummy_325 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_325] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv)
      0

theorem nb090_fresh_1063 (u : Var) :
    (nb090_alpha_dummy_326 u) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_326] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv)
      0

theorem nb090_fresh_1064 (A : Class) :
    (nb090_alpha_dummy_371 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_371] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part015`. -/


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

theorem nb090_fresh_1065 (h : Var) :
    (nb090_alpha_dummy_372 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_372] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv)
      0

theorem nb090_fresh_1066 (A : Class) :
    (nb090_alpha_dummy_415 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_415] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv)
      0

theorem nb090_fresh_1067 (v : Var) :
    (nb090_alpha_dummy_416 v) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_416] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv)
      0

theorem nb090_fresh_1068 (A : Class) :
    (nb090_alpha_dummy_465 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_465] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv)
      0

theorem nb090_fresh_1069 (h : Var) :
    (nb090_alpha_dummy_466 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_466] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv)
      0

theorem nb090_fresh_1070 (A : Class) :
    (nb090_alpha_dummy_501 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_501] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv)
      0

theorem nb090_fresh_1071 (h : Var) :
    (nb090_alpha_dummy_502 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_502] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv)
      0

theorem nb090_fresh_1072 (A : Class) :
    (nb090_alpha_dummy_543 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_543] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv)
      0

theorem nb090_fresh_1073 (h : Var) :
    (nb090_alpha_dummy_544 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_544] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv)
      0

theorem nb090_fresh_1074 (A : Class) :
    (nb090_alpha_dummy_579 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_579] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv)
      0

theorem nb090_fresh_1075 (h : Var) :
    (nb090_alpha_dummy_580 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_580] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv)
      0

theorem nb090_fresh_1076 (A : Class) :
    (nb090_alpha_dummy_615 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_615] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv)
      0

theorem nb090_fresh_1077 (h : Var) :
    (nb090_alpha_dummy_616 h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_616] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv)
      0

theorem nb090_fresh_1078 (A : Class) :
    (nb090_alpha_dummy_651 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_651] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv)
      0

theorem nb090_fresh_1079 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_652 v u h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_652] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv)
      0

theorem nb090_fresh_1080 (A : Class) :
    (nb090_alpha_dummy_695 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_695] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv)
      0

theorem nb090_fresh_1081 (u : Var) :
    (nb090_alpha_dummy_696 u) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_696] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv)
      0

theorem nb090_fresh_1082 (A : Class) :
    (nb090_alpha_dummy_825 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_825] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv)
      0

theorem nb090_fresh_1083 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_826 v u h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_826] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv)
      0

theorem nb090_fresh_1084 (A : Class) :
    (nb090_alpha_dummy_749 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_749] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv)
      0

theorem nb090_fresh_1085 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_750 v u h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_750] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv)
      0

theorem nb090_fresh_1086 (A : Class) :
    (nb090_alpha_dummy_819 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_819] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv)
      0

theorem nb090_fresh_1087 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_820 v u h) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_820] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv)
      0

theorem nb090_fresh_1088 (A : Class) :
    (nb090_alpha_dummy_869 A) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_869] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv)
      0

theorem nb090_fresh_1089 (v : Var) :
    (nb090_alpha_dummy_870 v) ∉
      (((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_870] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv)
      0

theorem nb090_fresh_1090 (A : Class) :
    (nb090_alpha_dummy_331 A) ∉
      (((syn_crn (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_331] using
    freshVar_not_mem
      (((syn_crn (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv)
      0

theorem nb090_fresh_1091 (v : Var) (h : Var) :
    (nb090_alpha_dummy_332 v h) ∉
      (((syn_crn (Class.cv h))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_332] using
    freshVar_not_mem
      (((syn_crn (Class.cv h))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) 0

theorem nb090_fresh_1092 (A : Class) : (nb090_alpha_dummy_000 A) ∉ ((A).fv) := by
  simpa only [nb090_alpha_dummy_000] using freshVar_not_mem ((A).fv) 0

theorem nb090_fresh_1093 (A : Class) : (nb090_alpha_dummy_001 A) ∉ ((A).fv) := by
  simpa only [nb090_alpha_dummy_001] using freshVar_not_mem ((A).fv) 1

theorem nb090_fresh_1094 (A : Class) : (nb090_alpha_dummy_002 A) ∉ ((A).fv) := by
  simpa only [nb090_alpha_dummy_002] using freshVar_not_mem ((A).fv) 2

theorem nb090_distinct_1095 (A : Class) :
    (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_001 A) := by
  simpa only [nb090_alpha_dummy_000, nb090_alpha_dummy_001] using
    (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_1096 (A : Class) :
    (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_002 A) := by
  simpa only [nb090_alpha_dummy_000, nb090_alpha_dummy_002] using
    (freshVar_injective ((A).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_1097 (A : Class) :
    (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_002 A) := by
  simpa only [nb090_alpha_dummy_001, nb090_alpha_dummy_002] using
    (freshVar_injective ((A).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_1098 (A : Class) :
    (nb090_alpha_dummy_003 A) ∉
      (({(nb090_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_002 A)} : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A))
              (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A)))
            (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A))
                (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))
                (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))
                (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))
                (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_003] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_002 A)} : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A))
              (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A)))
            (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A))
                (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))
                (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))
                (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))
                (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))).fv)
      0

theorem nb090_fresh_1099 (A : Class) :
    (nb090_alpha_dummy_055 A) ∉
      (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_049 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_051 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_050 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_055] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_049 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_051 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_050 A)))))).fv)
      0

theorem nb090_fresh_1100 (h : Var) :
    (nb090_alpha_dummy_056 h) ∉
      (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_054 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_053 h)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_056] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_054 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_053 h)))))).fv)
      0

theorem nb090_fresh_1101 (A : Class) :
    (nb090_alpha_dummy_133 A) ∉
      (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_129 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_133] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_129 A)))).fv)
      0

theorem nb090_fresh_1102 (h : Var) :
    (nb090_alpha_dummy_134 h) ∉
      (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_131 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_134] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_131 h)))).fv)
      0

theorem nb090_fresh_1103 (A : Class) :
    (nb090_alpha_dummy_285 A) ∉
      (({(nb090_alpha_dummy_283 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
            (Class.cv (nb090_alpha_dummy_283 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_285] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_283 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
            (Class.cv (nb090_alpha_dummy_283 A)))).fv)
      0

theorem nb090_fresh_1104 (u : Var) :
    (nb090_alpha_dummy_286 u) ∉
      (({(nb090_alpha_dummy_284 u)} : Finset Var) ∪
        ((syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_286] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_284 u)} : Finset Var) ∪
        ((syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u)))).fv)
      0

theorem nb090_fresh_1105 (A : Class) :
    (nb090_alpha_dummy_375 A) ∉
      (({(nb090_alpha_dummy_373 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
            (Class.cv (nb090_alpha_dummy_373 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_375] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_373 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
            (Class.cv (nb090_alpha_dummy_373 A)))).fv)
      0

theorem nb090_fresh_1106 (v : Var) :
    (nb090_alpha_dummy_376 v) ∉
      (({(nb090_alpha_dummy_374 v)} : Finset Var) ∪
        ((syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_376] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_374 v)} : Finset Var) ∪
        ((syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v)))).fv)
      0

theorem nb090_fresh_1107 (A : Class) :
    (nb090_alpha_dummy_429 A) ∉
      (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_423 A))
                (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))
                (Class.cv (nb090_alpha_dummy_425 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_425 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_424 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_429] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_423 A))
                (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))
                (Class.cv (nb090_alpha_dummy_425 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_425 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_424 A)))))).fv)
      0

theorem nb090_fresh_1108 (h : Var) :
    (nb090_alpha_dummy_430 h) ∉
      (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_426 h))
                (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_427 h)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_430] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_426 h))
                (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_427 h)))))).fv)
      0

theorem nb090_fresh_1109 (A : Class) :
    (nb090_alpha_dummy_507 A) ∉
      (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
            (Class.cv (nb090_alpha_dummy_503 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_507] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
            (Class.cv (nb090_alpha_dummy_503 A)))).fv)
      0

theorem nb090_fresh_1110 (h : Var) :
    (nb090_alpha_dummy_508 h) ∉
      (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb090_alpha_dummy_505 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_508] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb090_alpha_dummy_505 h)))).fv)
      0

theorem nb090_fresh_1111 (A : Class) :
    (nb090_alpha_dummy_655 A) ∉
      (({(nb090_alpha_dummy_653 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
            (Class.cv (nb090_alpha_dummy_653 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_655] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_653 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
            (Class.cv (nb090_alpha_dummy_653 A)))).fv)
      0

theorem nb090_fresh_1112 (u : Var) :
    (nb090_alpha_dummy_656 u) ∉
      (({(nb090_alpha_dummy_654 u)} : Finset Var) ∪
        ((syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_656] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_654 u)} : Finset Var) ∪
        ((syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u)))).fv)
      0

theorem nb090_fresh_1113 (A : Class) :
    (nb090_alpha_dummy_709 A) ∉
      (({(nb090_alpha_dummy_707 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_707 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_709] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_707 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_707 A)))).fv)
      0

theorem nb090_fresh_1114 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_710 v u h) ∉
      (({(nb090_alpha_dummy_708 v u h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_708 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_710] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_708 v u h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_708 v u h)))).fv)
      0

theorem nb090_fresh_1115 (A : Class) :
    (nb090_alpha_dummy_779 A) ∉
      (({(nb090_alpha_dummy_777 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_777 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_779] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_777 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_777 A)))).fv)
      0

theorem nb090_fresh_1116 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_780 v u h) ∉
      (({(nb090_alpha_dummy_778 v u h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_778 v u h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_780] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_778 v u h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_778 v u h)))).fv)
      0

theorem nb090_fresh_1117 (A : Class) :
    (nb090_alpha_dummy_829 A) ∉
      (({(nb090_alpha_dummy_827 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
            (Class.cv (nb090_alpha_dummy_827 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_829] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_827 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
            (Class.cv (nb090_alpha_dummy_827 A)))).fv)
      0

theorem nb090_fresh_1118 (v : Var) :
    (nb090_alpha_dummy_830 v) ∉
      (({(nb090_alpha_dummy_828 v)} : Finset Var) ∪
        ((syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_830] using
    freshVar_not_mem
      (({(nb090_alpha_dummy_828 v)} : Finset Var) ∪
        ((syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))).fv)
      0

theorem nb090_fresh_1119 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090_alpha_dummy_004 v u A h) ∉
      (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A))
              (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h
              (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u))
                (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u))
                (syn_cfv (syn_c2nd) (Class.cv v)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_004] using
    freshVar_not_mem
      (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A))
              (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h
              (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u))
                (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u))
                (syn_cfv (syn_c2nd) (Class.cv v)))))).fv)
      0

theorem nb090_support_mem_0000 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (({(nb090_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_002 A)} : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A))
              (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A)))
            (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A))
                (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))
                (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))
                (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))
                (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0001 (v : Var) (u : Var) (A : Class) (h : Var) :
    u ∈
      (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A))
              (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h
              (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u))
                (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u))
                (syn_cfv (syn_c2nd) (Class.cv v)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0002 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (({(nb090_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_002 A)} : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A))
              (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A)))
            (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A))
                (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))
                (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))
                (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))
                (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0003 (v : Var) (u : Var) (A : Class) (h : Var) :
    v ∈
      (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A))
              (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h
              (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u))
                (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u))
                (syn_cfv (syn_c2nd) (Class.cv v)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0004 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0005 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_005 A)
              (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_005 A)
              (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_005 A) from (by
          unfold nb090_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_006 A) from (by
            unfold nb090_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0006 (v : Var) (u : Var) :
    u ∈ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0007 (v : Var) (u : Var) :
    u ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_007 v u)
              (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_007 v u)
              (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090_alpha_dummy_007 v u) from (by
          unfold nb090_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090_alpha_dummy_008 v u) from (by
            unfold nb090_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0008 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_005 A) from (by
          unfold nb090_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_006 A) from (by
            unfold nb090_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0009 (v : Var) (u : Var) :
    u ∈
      (((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090_alpha_dummy_007 v u) from (by
          unfold nb090_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090_alpha_dummy_008 v u) from (by
            unfold nb090_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0010 (A : Class) :
    (nb090_alpha_dummy_006 A) ∈ (((Class.cv (nb090_alpha_dummy_006 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0011 (v : Var) (u : Var) :
    (nb090_alpha_dummy_008 v u) ∈ (((Class.cv (nb090_alpha_dummy_008 v u))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0012 (A : Class) :
    (nb090_alpha_dummy_013 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_013 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_013 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_013 A))).fv) :=
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

theorem nb090_support_mem_0013 (v : Var) (u : Var) :
    (nb090_alpha_dummy_015 v u) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_015 v u)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_015 v u)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_015 v u))).fv) :=
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

theorem nb090_support_mem_0014 (A : Class) :
    (nb090_alpha_dummy_013 A) ∈
      (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0015 (v : Var) (u : Var) :
    (nb090_alpha_dummy_015 v u) ∈
      (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0016 (A : Class) :
    (nb090_alpha_dummy_020 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_020 A))
            (Class.cv (nb090_alpha_dummy_021 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_020 A))
            (Class.cv (nb090_alpha_dummy_021 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0017 (v : Var) (u : Var) :
    (nb090_alpha_dummy_023 v u) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u))
            (Class.cv (nb090_alpha_dummy_024 v u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u))
            (Class.cv (nb090_alpha_dummy_024 v u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0018 (A : Class) :
    (nb090_alpha_dummy_020 A) ∈
      (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0019 (v : Var) (u : Var) :
    (nb090_alpha_dummy_023 v u) ∈
      (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪
        ((Class.cv (nb090_alpha_dummy_024 v u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0020 (A : Class) :
    (nb090_alpha_dummy_021 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_020 A))
            (Class.cv (nb090_alpha_dummy_021 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_020 A))
            (Class.cv (nb090_alpha_dummy_021 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0021 (v : Var) (u : Var) :
    (nb090_alpha_dummy_024 v u) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u))
            (Class.cv (nb090_alpha_dummy_024 v u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u))
            (Class.cv (nb090_alpha_dummy_024 v u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0022 (A : Class) :
    (nb090_alpha_dummy_021 A) ∈
      (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0023 (v : Var) (u : Var) :
    (nb090_alpha_dummy_024 v u) ∈
      (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪
        ((Class.cv (nb090_alpha_dummy_024 v u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0024 (A : Class) :
    (nb090_alpha_dummy_020 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_020 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_021 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0025 (v : Var) (u : Var) :
    (nb090_alpha_dummy_023 v u) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_023 v u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_024 v u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0026 (A : Class) :
    (nb090_alpha_dummy_020 A) ∈
      (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_020 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0027 (v : Var) (u : Var) :
    (nb090_alpha_dummy_023 v u) ∈
      (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪
        ((Class.cv (nb090_alpha_dummy_023 v u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0028 (A : Class) :
    (nb090_alpha_dummy_021 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_020 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_021 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0029 (v : Var) (u : Var) :
    (nb090_alpha_dummy_024 v u) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_023 v u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_024 v u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0030 (A : Class) :
    (nb090_alpha_dummy_021 A) ∈
      (((Class.cv (nb090_alpha_dummy_021 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0031 (v : Var) (u : Var) :
    (nb090_alpha_dummy_024 v u) ∈
      (((Class.cv (nb090_alpha_dummy_024 v u))).fv ∪
        ((Class.cv (nb090_alpha_dummy_024 v u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0032 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0033 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_005 A)
              (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_005 A)
              (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_005 A) from (by
          unfold nb090_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_006 A) from (by
            unfold nb090_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0034 (v : Var) (u : Var) :
    v ∈ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0035 (v : Var) (u : Var) :
    v ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_007 v u)
              (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_007 v u)
              (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090_alpha_dummy_007 v u) from (by
          unfold nb090_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090_alpha_dummy_008 v u) from (by
            unfold nb090_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0036 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_005 A) from (by
          unfold nb090_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_006 A) from (by
            unfold nb090_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0037 (v : Var) (u : Var) :
    v ∈
      (((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090_alpha_dummy_007 v u) from (by
          unfold nb090_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090_alpha_dummy_008 v u) from (by
            unfold nb090_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0038 (A : Class) :
    (nb090_alpha_dummy_006 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0039 (v : Var) (u : Var) :
    (nb090_alpha_dummy_008 v u) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0040 (A : Class) :
    (nb090_alpha_dummy_006 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0041 (v : Var) (u : Var) :
    (nb090_alpha_dummy_008 v u) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0042 (A : Class) :
    (nb090_alpha_dummy_049 A) ∈
      (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_049 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_051 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_050 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0043 (h : Var) :
    (nb090_alpha_dummy_052 h) ∈
      (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_054 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0044 (A : Class) :
    (nb090_alpha_dummy_050 A) ∈
      (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_049 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_051 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_050 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0045 (h : Var) :
    (nb090_alpha_dummy_053 h) ∈
      (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_054 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0046 (A : Class) :
    (nb090_alpha_dummy_049 A) ∈
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0047 (A : Class) :
    (nb090_alpha_dummy_049 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_057 A)
              (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_057 A)
              (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_057 A) from (by
          unfold nb090_alpha_dummy_057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_058 A) from (by
            unfold nb090_alpha_dummy_058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0048 (h : Var) :
    (nb090_alpha_dummy_052 h) ∈
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0049 (h : Var) :
    (nb090_alpha_dummy_052 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_059 h)
              (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_059 h)
              (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_059 h) from (by
          unfold nb090_alpha_dummy_059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_060 h) from (by
            unfold nb090_alpha_dummy_060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0050 (A : Class) :
    (nb090_alpha_dummy_049 A) ∈
      (((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_057 A) from (by
          unfold nb090_alpha_dummy_057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_058 A) from (by
            unfold nb090_alpha_dummy_058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0051 (h : Var) :
    (nb090_alpha_dummy_052 h) ∈
      (((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_059 h) from (by
          unfold nb090_alpha_dummy_059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_060 h) from (by
            unfold nb090_alpha_dummy_060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0052 (A : Class) :
    (nb090_alpha_dummy_058 A) ∈ (((Class.cv (nb090_alpha_dummy_058 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0053 (h : Var) :
    (nb090_alpha_dummy_060 h) ∈ (((Class.cv (nb090_alpha_dummy_060 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0054 (A : Class) :
    (nb090_alpha_dummy_065 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_065 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_065 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_065 A))).fv) :=
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

theorem nb090_support_mem_0055 (h : Var) :
    (nb090_alpha_dummy_067 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_067 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_067 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_067 h))).fv) :=
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

theorem nb090_support_mem_0056 (A : Class) :
    (nb090_alpha_dummy_065 A) ∈
      (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0057 (h : Var) :
    (nb090_alpha_dummy_067 h) ∈
      (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0058 (A : Class) :
    (nb090_alpha_dummy_072 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_072 A))
            (Class.cv (nb090_alpha_dummy_073 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_072 A))
            (Class.cv (nb090_alpha_dummy_073 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0059 (h : Var) :
    (nb090_alpha_dummy_075 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_075 h))
            (Class.cv (nb090_alpha_dummy_076 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_075 h))
            (Class.cv (nb090_alpha_dummy_076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0060 (A : Class) :
    (nb090_alpha_dummy_072 A) ∈
      (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0061 (h : Var) :
    (nb090_alpha_dummy_075 h) ∈
      (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0062 (A : Class) :
    (nb090_alpha_dummy_073 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_072 A))
            (Class.cv (nb090_alpha_dummy_073 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_072 A))
            (Class.cv (nb090_alpha_dummy_073 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0063 (h : Var) :
    (nb090_alpha_dummy_076 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_075 h))
            (Class.cv (nb090_alpha_dummy_076 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_075 h))
            (Class.cv (nb090_alpha_dummy_076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0064 (A : Class) :
    (nb090_alpha_dummy_073 A) ∈
      (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0065 (h : Var) :
    (nb090_alpha_dummy_076 h) ∈
      (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0066 (A : Class) :
    (nb090_alpha_dummy_072 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_072 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_073 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0067 (h : Var) :
    (nb090_alpha_dummy_075 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_075 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0068 (A : Class) :
    (nb090_alpha_dummy_072 A) ∈
      (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_072 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0069 (h : Var) :
    (nb090_alpha_dummy_075 h) ∈
      (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_075 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0070 (A : Class) :
    (nb090_alpha_dummy_073 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_072 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_073 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0071 (h : Var) :
    (nb090_alpha_dummy_076 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_075 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0072 (A : Class) :
    (nb090_alpha_dummy_073 A) ∈
      (((Class.cv (nb090_alpha_dummy_073 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0073 (h : Var) :
    (nb090_alpha_dummy_076 h) ∈
      (((Class.cv (nb090_alpha_dummy_076 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0074 (A : Class) :
    (nb090_alpha_dummy_050 A) ∈
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0075 (A : Class) :
    (nb090_alpha_dummy_050 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_057 A)
              (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_057 A)
              (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_057 A) from (by
          unfold nb090_alpha_dummy_057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_058 A) from (by
            unfold nb090_alpha_dummy_058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0076 (h : Var) :
    (nb090_alpha_dummy_053 h) ∈
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0077 (h : Var) :
    (nb090_alpha_dummy_053 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_059 h)
              (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_059 h)
              (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_059 h) from (by
          unfold nb090_alpha_dummy_059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_060 h) from (by
            unfold nb090_alpha_dummy_060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0078 (A : Class) :
    (nb090_alpha_dummy_050 A) ∈
      (((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_057 A) from (by
          unfold nb090_alpha_dummy_057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_058 A) from (by
            unfold nb090_alpha_dummy_058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part016`. -/


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

theorem nb090_support_mem_0079 (h : Var) :
    (nb090_alpha_dummy_053 h) ∈
      (((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_059 h) from (by
          unfold nb090_alpha_dummy_059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_060 h) from (by
            unfold nb090_alpha_dummy_060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0080 (A : Class) :
    (nb090_alpha_dummy_058 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0081 (h : Var) :
    (nb090_alpha_dummy_060 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0082 (A : Class) :
    (nb090_alpha_dummy_058 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0083 (h : Var) :
    (nb090_alpha_dummy_060 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0084 (A : Class) :
    (nb090_alpha_dummy_049 A) ∈
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0085 (A : Class) :
    (nb090_alpha_dummy_049 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_093 A)
              (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_093 A)
              (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_093 A) from (by
          unfold nb090_alpha_dummy_093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_094 A) from (by
            unfold nb090_alpha_dummy_094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0086 (h : Var) :
    (nb090_alpha_dummy_052 h) ∈
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0087 (h : Var) :
    (nb090_alpha_dummy_052 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_095 h)
              (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_095 h)
              (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_095 h) from (by
          unfold nb090_alpha_dummy_095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_096 h) from (by
            unfold nb090_alpha_dummy_096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0088 (A : Class) :
    (nb090_alpha_dummy_049 A) ∈
      (((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_093 A) from (by
          unfold nb090_alpha_dummy_093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_094 A) from (by
            unfold nb090_alpha_dummy_094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0089 (h : Var) :
    (nb090_alpha_dummy_052 h) ∈
      (((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_095 h) from (by
          unfold nb090_alpha_dummy_095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_096 h) from (by
            unfold nb090_alpha_dummy_096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0090 (A : Class) :
    (nb090_alpha_dummy_094 A) ∈ (((Class.cv (nb090_alpha_dummy_094 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0091 (h : Var) :
    (nb090_alpha_dummy_096 h) ∈ (((Class.cv (nb090_alpha_dummy_096 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0092 (A : Class) :
    (nb090_alpha_dummy_101 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_101 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_101 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_101 A))).fv) :=
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

theorem nb090_support_mem_0093 (h : Var) :
    (nb090_alpha_dummy_103 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_103 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_103 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_103 h))).fv) :=
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

theorem nb090_support_mem_0094 (A : Class) :
    (nb090_alpha_dummy_101 A) ∈
      (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0095 (h : Var) :
    (nb090_alpha_dummy_103 h) ∈
      (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0096 (A : Class) :
    (nb090_alpha_dummy_108 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_108 A))
            (Class.cv (nb090_alpha_dummy_109 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_108 A))
            (Class.cv (nb090_alpha_dummy_109 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0097 (h : Var) :
    (nb090_alpha_dummy_111 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_111 h))
            (Class.cv (nb090_alpha_dummy_112 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_111 h))
            (Class.cv (nb090_alpha_dummy_112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0098 (A : Class) :
    (nb090_alpha_dummy_108 A) ∈
      (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0099 (h : Var) :
    (nb090_alpha_dummy_111 h) ∈
      (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0100 (A : Class) :
    (nb090_alpha_dummy_109 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_108 A))
            (Class.cv (nb090_alpha_dummy_109 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_108 A))
            (Class.cv (nb090_alpha_dummy_109 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0101 (h : Var) :
    (nb090_alpha_dummy_112 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_111 h))
            (Class.cv (nb090_alpha_dummy_112 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_111 h))
            (Class.cv (nb090_alpha_dummy_112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0102 (A : Class) :
    (nb090_alpha_dummy_109 A) ∈
      (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0103 (h : Var) :
    (nb090_alpha_dummy_112 h) ∈
      (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0104 (A : Class) :
    (nb090_alpha_dummy_108 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_108 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_109 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0105 (h : Var) :
    (nb090_alpha_dummy_111 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_111 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0106 (A : Class) :
    (nb090_alpha_dummy_108 A) ∈
      (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_108 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0107 (h : Var) :
    (nb090_alpha_dummy_111 h) ∈
      (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_111 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0108 (A : Class) :
    (nb090_alpha_dummy_109 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_108 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_109 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0109 (h : Var) :
    (nb090_alpha_dummy_112 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_111 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0110 (A : Class) :
    (nb090_alpha_dummy_109 A) ∈
      (((Class.cv (nb090_alpha_dummy_109 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0111 (h : Var) :
    (nb090_alpha_dummy_112 h) ∈
      (((Class.cv (nb090_alpha_dummy_112 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0112 (A : Class) :
    (nb090_alpha_dummy_051 A) ∈
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0113 (A : Class) :
    (nb090_alpha_dummy_051 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_093 A)
              (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_093 A)
              (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_093 A) from (by
          unfold nb090_alpha_dummy_093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_094 A) from (by
            unfold nb090_alpha_dummy_094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0114 (h : Var) :
    (nb090_alpha_dummy_054 h) ∈
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0115 (h : Var) :
    (nb090_alpha_dummy_054 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_095 h)
              (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_095 h)
              (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_095 h) from (by
          unfold nb090_alpha_dummy_095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_096 h) from (by
            unfold nb090_alpha_dummy_096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0116 (A : Class) :
    (nb090_alpha_dummy_051 A) ∈
      (((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_093 A) from (by
          unfold nb090_alpha_dummy_093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_094 A) from (by
            unfold nb090_alpha_dummy_094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0117 (h : Var) :
    (nb090_alpha_dummy_054 h) ∈
      (((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_095 h) from (by
          unfold nb090_alpha_dummy_095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_096 h) from (by
            unfold nb090_alpha_dummy_096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0118 (A : Class) :
    (nb090_alpha_dummy_094 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0119 (h : Var) :
    (nb090_alpha_dummy_096 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0120 (A : Class) :
    (nb090_alpha_dummy_094 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0121 (h : Var) :
    (nb090_alpha_dummy_096 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0122 (A : Class) :
    (nb090_alpha_dummy_129 A) ∈
      (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_129 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0123 (h : Var) :
    (nb090_alpha_dummy_131 h) ∈
      (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_131 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0124 (A : Class) :
    (nb090_alpha_dummy_130 A) ∈
      (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_129 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0125 (h : Var) :
    (nb090_alpha_dummy_132 h) ∈
      (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_131 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0126 (A : Class) :
    (nb090_alpha_dummy_129 A) ∈
      (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0127 (A : Class) :
    (nb090_alpha_dummy_129 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_135 A) from (by
          unfold nb090_alpha_dummy_135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_136 A) from (by
            unfold nb090_alpha_dummy_136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0128 (h : Var) :
    (nb090_alpha_dummy_131 h) ∈
      (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0129 (h : Var) :
    (nb090_alpha_dummy_131 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold nb090_alpha_dummy_137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_138 h) from (by
            unfold nb090_alpha_dummy_138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0130 (A : Class) :
    (nb090_alpha_dummy_129 A) ∈
      (((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_135 A) from (by
          unfold nb090_alpha_dummy_135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_136 A) from (by
            unfold nb090_alpha_dummy_136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0131 (h : Var) :
    (nb090_alpha_dummy_131 h) ∈
      (((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold nb090_alpha_dummy_137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_138 h) from (by
            unfold nb090_alpha_dummy_138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0132 (A : Class) :
    (nb090_alpha_dummy_136 A) ∈ (((Class.cv (nb090_alpha_dummy_136 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0133 (h : Var) :
    (nb090_alpha_dummy_138 h) ∈ (((Class.cv (nb090_alpha_dummy_138 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0134 (A : Class) :
    (nb090_alpha_dummy_143 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_143 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_143 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_143 A))).fv) :=
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

theorem nb090_support_mem_0135 (h : Var) :
    (nb090_alpha_dummy_145 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_145 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_145 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_145 h))).fv) :=
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

theorem nb090_support_mem_0136 (A : Class) :
    (nb090_alpha_dummy_143 A) ∈
      (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0137 (h : Var) :
    (nb090_alpha_dummy_145 h) ∈
      (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0138 (A : Class) :
    (nb090_alpha_dummy_150 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_150 A))
            (Class.cv (nb090_alpha_dummy_151 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_150 A))
            (Class.cv (nb090_alpha_dummy_151 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0139 (h : Var) :
    (nb090_alpha_dummy_153 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_153 h))
            (Class.cv (nb090_alpha_dummy_154 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_153 h))
            (Class.cv (nb090_alpha_dummy_154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0140 (A : Class) :
    (nb090_alpha_dummy_150 A) ∈
      (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0141 (h : Var) :
    (nb090_alpha_dummy_153 h) ∈
      (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0142 (A : Class) :
    (nb090_alpha_dummy_151 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_150 A))
            (Class.cv (nb090_alpha_dummy_151 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_150 A))
            (Class.cv (nb090_alpha_dummy_151 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0143 (h : Var) :
    (nb090_alpha_dummy_154 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_153 h))
            (Class.cv (nb090_alpha_dummy_154 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_153 h))
            (Class.cv (nb090_alpha_dummy_154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0144 (A : Class) :
    (nb090_alpha_dummy_151 A) ∈
      (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0145 (h : Var) :
    (nb090_alpha_dummy_154 h) ∈
      (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0146 (A : Class) :
    (nb090_alpha_dummy_150 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_150 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_151 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0147 (h : Var) :
    (nb090_alpha_dummy_153 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_153 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0148 (A : Class) :
    (nb090_alpha_dummy_150 A) ∈
      (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_150 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0149 (h : Var) :
    (nb090_alpha_dummy_153 h) ∈
      (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_153 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0150 (A : Class) :
    (nb090_alpha_dummy_151 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_150 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_151 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0151 (h : Var) :
    (nb090_alpha_dummy_154 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_153 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0152 (A : Class) :
    (nb090_alpha_dummy_151 A) ∈
      (((Class.cv (nb090_alpha_dummy_151 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0153 (h : Var) :
    (nb090_alpha_dummy_154 h) ∈
      (((Class.cv (nb090_alpha_dummy_154 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0154 (A : Class) :
    (nb090_alpha_dummy_130 A) ∈
      (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0155 (A : Class) :
    (nb090_alpha_dummy_130 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_135 A) from (by
          unfold nb090_alpha_dummy_135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
            unfold nb090_alpha_dummy_136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0156 (h : Var) :
    (nb090_alpha_dummy_132 h) ∈
      (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0157 (h : Var) :
    (nb090_alpha_dummy_132 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold nb090_alpha_dummy_137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_138 h) from (by
            unfold nb090_alpha_dummy_138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0158 (A : Class) :
    (nb090_alpha_dummy_130 A) ∈
      (((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_135 A) from (by
          unfold nb090_alpha_dummy_135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
            unfold nb090_alpha_dummy_136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0159 (h : Var) :
    (nb090_alpha_dummy_132 h) ∈
      (((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold nb090_alpha_dummy_137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_138 h) from (by
            unfold nb090_alpha_dummy_138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0160 (A : Class) :
    (nb090_alpha_dummy_136 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0161 (h : Var) :
    (nb090_alpha_dummy_138 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0162 (A : Class) :
    (nb090_alpha_dummy_136 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0163 (h : Var) :
    (nb090_alpha_dummy_138 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0164 (A : Class) :
    (nb090_alpha_dummy_130 A) ∈
      (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0165 (A : Class) :
    (nb090_alpha_dummy_130 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_171 A)
              (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_171 A)
              (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_171 A) from (by
          unfold nb090_alpha_dummy_171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_172 A) from (by
            unfold nb090_alpha_dummy_172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0166 (h : Var) :
    (nb090_alpha_dummy_132 h) ∈
      (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0167 (h : Var) :
    (nb090_alpha_dummy_132 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_173 h)
              (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_173 h)
              (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold nb090_alpha_dummy_173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_174 h) from (by
            unfold nb090_alpha_dummy_174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0168 (A : Class) :
    (nb090_alpha_dummy_130 A) ∈
      (((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_171 A) from (by
          unfold nb090_alpha_dummy_171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_172 A) from (by
            unfold nb090_alpha_dummy_172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0169 (h : Var) :
    (nb090_alpha_dummy_132 h) ∈
      (((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold nb090_alpha_dummy_173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_174 h) from (by
            unfold nb090_alpha_dummy_174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0170 (A : Class) :
    (nb090_alpha_dummy_172 A) ∈ (((Class.cv (nb090_alpha_dummy_172 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0171 (h : Var) :
    (nb090_alpha_dummy_174 h) ∈ (((Class.cv (nb090_alpha_dummy_174 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0172 (A : Class) :
    (nb090_alpha_dummy_179 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_179 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_179 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_179 A))).fv) :=
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

theorem nb090_support_mem_0173 (h : Var) :
    (nb090_alpha_dummy_181 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_181 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_181 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_181 h))).fv) :=
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

theorem nb090_support_mem_0174 (A : Class) :
    (nb090_alpha_dummy_179 A) ∈
      (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0175 (h : Var) :
    (nb090_alpha_dummy_181 h) ∈
      (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0176 (A : Class) :
    (nb090_alpha_dummy_186 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_186 A))
            (Class.cv (nb090_alpha_dummy_187 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_186 A))
            (Class.cv (nb090_alpha_dummy_187 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0177 (h : Var) :
    (nb090_alpha_dummy_189 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_189 h))
            (Class.cv (nb090_alpha_dummy_190 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_189 h))
            (Class.cv (nb090_alpha_dummy_190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0178 (A : Class) :
    (nb090_alpha_dummy_186 A) ∈
      (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0179 (h : Var) :
    (nb090_alpha_dummy_189 h) ∈
      (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0180 (A : Class) :
    (nb090_alpha_dummy_187 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_186 A))
            (Class.cv (nb090_alpha_dummy_187 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_186 A))
            (Class.cv (nb090_alpha_dummy_187 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0181 (h : Var) :
    (nb090_alpha_dummy_190 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_189 h))
            (Class.cv (nb090_alpha_dummy_190 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_189 h))
            (Class.cv (nb090_alpha_dummy_190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0182 (A : Class) :
    (nb090_alpha_dummy_187 A) ∈
      (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0183 (h : Var) :
    (nb090_alpha_dummy_190 h) ∈
      (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0184 (A : Class) :
    (nb090_alpha_dummy_186 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_186 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_187 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0185 (h : Var) :
    (nb090_alpha_dummy_189 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_189 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0186 (A : Class) :
    (nb090_alpha_dummy_186 A) ∈
      (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_186 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0187 (h : Var) :
    (nb090_alpha_dummy_189 h) ∈
      (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_189 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0188 (A : Class) :
    (nb090_alpha_dummy_187 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_186 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_187 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0189 (h : Var) :
    (nb090_alpha_dummy_190 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_189 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0190 (A : Class) :
    (nb090_alpha_dummy_187 A) ∈
      (((Class.cv (nb090_alpha_dummy_187 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0191 (h : Var) :
    (nb090_alpha_dummy_190 h) ∈
      (((Class.cv (nb090_alpha_dummy_190 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0192 (A : Class) :
    (nb090_alpha_dummy_129 A) ∈
      (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0193 (A : Class) :
    (nb090_alpha_dummy_129 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_171 A)
              (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_171 A)
              (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_171 A) from (by
          unfold nb090_alpha_dummy_171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
            unfold nb090_alpha_dummy_172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0194 (h : Var) :
    (nb090_alpha_dummy_131 h) ∈
      (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0195 (h : Var) :
    (nb090_alpha_dummy_131 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_173 h)
              (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_173 h)
              (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold nb090_alpha_dummy_173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_174 h) from (by
            unfold nb090_alpha_dummy_174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0196 (A : Class) :
    (nb090_alpha_dummy_129 A) ∈
      (((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_171 A) from (by
          unfold nb090_alpha_dummy_171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
            unfold nb090_alpha_dummy_172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0197 (h : Var) :
    (nb090_alpha_dummy_131 h) ∈
      (((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold nb090_alpha_dummy_173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_174 h) from (by
            unfold nb090_alpha_dummy_174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0198 (A : Class) :
    (nb090_alpha_dummy_172 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0199 (h : Var) :
    (nb090_alpha_dummy_174 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0200 (A : Class) :
    (nb090_alpha_dummy_172 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0201 (h : Var) :
    (nb090_alpha_dummy_174 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0202 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
              (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
              (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv) :=
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

theorem nb090_support_mem_0203 (h : Var) :
    h ∈
      (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) :=
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

theorem nb090_support_mem_0204 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0205 (h : Var) :
    h ∈ (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0206 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
        ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0207 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_049 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_051 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_050 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_051 A) from (by
          unfold nb090_alpha_dummy_051;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0206 A) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0208 (h : Var) :
    h ∈ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0209 (h : Var) :
    h ∈
      (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_054 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090_alpha_dummy_054 h) from (by
          unfold nb090_alpha_dummy_054;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0208 h) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0210 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_129 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0211 (h : Var) :
    h ∈
      (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_131 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0212 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈ (((Class.cv (nb090_alpha_dummy_000 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0213 (h : Var) : h ∈ (((Class.cv h)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0214 (A : Class) :
    (nb090_alpha_dummy_051 A) ∈
      (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0215 (A : Class) :
    (nb090_alpha_dummy_051 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_207 A)
              (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_207 A)
              (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_207 A) from (by
          unfold nb090_alpha_dummy_207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_208 A) from (by
            unfold nb090_alpha_dummy_208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0216 (h : Var) :
    (nb090_alpha_dummy_054 h) ∈
      (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
