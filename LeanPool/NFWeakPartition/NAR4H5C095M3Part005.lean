/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part004

/-! NF weak partition development: NAR4H5C095M3Part005. -/


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

theorem nb095_fresh_789 (f : Var) :
    (nb095_alpha_dummy_207 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb095_alpha_dummy_207] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0

theorem nb095_fresh_790 (f : Var) :
    (nb095_alpha_dummy_208 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb095_alpha_dummy_208] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1

theorem nb095_distinct_791 (f : Var) :
    (nb095_alpha_dummy_207 f) ≠ (nb095_alpha_dummy_208 f) := by
  simpa only [nb095_alpha_dummy_207, nb095_alpha_dummy_208] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_792 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_249 D R S_cls E) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_249] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
      0

theorem nb095_fresh_793 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_250 D R S_cls E) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_250] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
      1

theorem nb095_distinct_794 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_250 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_249, nb095_alpha_dummy_250] using
    (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_795 (x : Var) (R : Class) :
    (nb095_alpha_dummy_251 x R) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (Class.cv x))).fv) :=
  by
  simpa only [nb095_alpha_dummy_251] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (Class.cv x))).fv) 0

theorem nb095_fresh_796 (x : Var) (R : Class) :
    (nb095_alpha_dummy_252 x R) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (Class.cv x))).fv) :=
  by
  simpa only [nb095_alpha_dummy_252] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (Class.cv x))).fv) 1

theorem nb095_distinct_797 (x : Var) (R : Class) :
    (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_252 x R) := by
  simpa only [nb095_alpha_dummy_251, nb095_alpha_dummy_252] using
    (freshVar_injective
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (Class.cv x))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_798 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_339 D R S_cls E) ∉
      (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_339] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv)
      0

theorem nb095_fresh_799 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_340 D R S_cls E) ∉
      (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_340] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv)
      1

theorem nb095_distinct_800 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_340 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_339, nb095_alpha_dummy_340] using
    (freshVar_injective (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪
        ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_801 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_341 u S_cls) ∉
      (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn (Class.cv u))).fv) :=
  by
  simpa only [nb095_alpha_dummy_341] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn (Class.cv u))).fv) 0

theorem nb095_fresh_802 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_342 u S_cls) ∉
      (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn (Class.cv u))).fv) :=
  by
  simpa only [nb095_alpha_dummy_342] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn (Class.cv u))).fv) 1

theorem nb095_distinct_803 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_342 u S_cls) := by
  simpa only [nb095_alpha_dummy_341, nb095_alpha_dummy_342] using
    (freshVar_injective
      (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn (Class.cv u))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_804 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_009 D R S_cls E) ∉
      (((syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb095_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb095_fresh_805 (f : Var) :
    (nb095_alpha_dummy_010 f) ∉
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb095_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0

theorem nb095_fresh_806 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_383 D R S_cls E) ∉
      (((syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
            (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))).fv ∪
        ((syn_cid)).fv) :=
  by
  simpa only [nb095_alpha_dummy_383] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
            (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))).fv ∪
        ((syn_cid)).fv)
      0

theorem nb095_fresh_807 (f : Var) :
    (nb095_alpha_dummy_384 f) ∉
      (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪
        ((syn_cid)).fv) :=
  by
  simpa only [nb095_alpha_dummy_384] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪
        ((syn_cid)).fv)
      0

theorem nb095_fresh_808 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_023 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_023] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_809 (f : Var) :
    (nb095_alpha_dummy_024 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_021 f)
              (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_021 f)
              (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_024] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_021 f)
              (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_021 f)
              (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_810 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_059 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_055 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_055 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_059] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_055 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_055 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_811 (f : Var) :
    (nb095_alpha_dummy_060 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_057 f)
              (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_057 f)
              (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_060] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_057 f)
              (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_057 f)
              (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_812 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_101 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_101] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_813 (f : Var) :
    (nb095_alpha_dummy_102 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_099 f)
              (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_099 f)
              (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_102] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_099 f)
              (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_099 f)
              (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_814 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_137 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_137] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_815 (f : Var) :
    (nb095_alpha_dummy_138 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_135 f)
              (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_135 f)
              (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_138] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_135 f)
              (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_135 f)
              (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_816 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_173 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_173] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_817 (f : Var) :
    (nb095_alpha_dummy_174 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_171 f)
              (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_171 f)
              (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_174] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_171 f)
              (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_171 f)
              (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_818 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_213 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_213] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_819 (f : Var) :
    (nb095_alpha_dummy_214 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_211 f)
              (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_211 f)
              (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_214] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_211 f)
              (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_211 f)
              (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_820 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_259 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_259] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_821 (x : Var) (R : Class) :
    (nb095_alpha_dummy_260 x R) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_257 x R)
              (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_257 x R)
              (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_260] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_257 x R)
              (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_257 x R)
              (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_822 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_303 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_303] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_823 (f : Var) :
    (nb095_alpha_dummy_304 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_301 f)
              (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_301 f)
              (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_304] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_301 f)
              (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_301 f)
              (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_824 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_349 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_349] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_825 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_350 u S_cls) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_347 u S_cls)
              (syn_wrex (nb095_alpha_dummy_348 u S_cls)
                (Class.cv (nb095_alpha_dummy_342 u S_cls))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
                (Class.cv (nb095_alpha_dummy_341 u S_cls))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_350] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_347 u S_cls)
              (syn_wrex (nb095_alpha_dummy_348 u S_cls)
                (Class.cv (nb095_alpha_dummy_342 u S_cls))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
                (Class.cv (nb095_alpha_dummy_341 u S_cls))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_826 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_397 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_397] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_827 (f : Var) :
    (nb095_alpha_dummy_398 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_395 f)
              (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_395 f)
              (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_398] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_395 f)
              (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_395 f)
              (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_828 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_433 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_433] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_829 (f : Var) :
    (nb095_alpha_dummy_434 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_431 f)
              (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_431 f)
              (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_434] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_431 f)
              (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_431 f)
              (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_830 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_475 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_475] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_831 (f : Var) :
    (nb095_alpha_dummy_476 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_473 f)
              (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_473 f)
              (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_476] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_473 f)
              (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_473 f)
              (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_832 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_511 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_511] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_833 (f : Var) :
    (nb095_alpha_dummy_512 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_509 f)
              (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_509 f)
              (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_512] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_509 f)
              (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_509 f)
              (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_834 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_547 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_547] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_835 (f : Var) :
    (nb095_alpha_dummy_548 f) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_545 f)
              (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_545 f)
              (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_548] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_545 f)
              (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_545 f)
              (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_836 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_583 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_583] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_837 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_584 x u D R S_cls f E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_584] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_838 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_629 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_629] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_839 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_630 x D R) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_627 x D R)
              (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_621 x D R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
                (Class.cv (nb095_alpha_dummy_622 x D R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_630] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_627 x D R)
              (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_621 x D R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
                (Class.cv (nb095_alpha_dummy_622 x D R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_840 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_665 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
                (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                  (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
                (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                  (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_665] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
                (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                  (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
                (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                  (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_841 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_666 x u D R S_cls f E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E) (syn_cfv (Class.cv f)
                  (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E) (syn_cfv (Class.cv f)
                  (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_666] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E) (syn_cfv (Class.cv f)
                  (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E) (syn_cfv (Class.cv f)
                  (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_842 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_681 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_681] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_843 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_682 x u D R S_cls f E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_682] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_844 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_751 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_751] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_845 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_752 x u D R S_cls f E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_752] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_846 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_803 D R S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_803] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_847 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_804 u S_cls E) ∉
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_801 u S_cls E)
              (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
                (Class.cv (nb095_alpha_dummy_795 u S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_801 u S_cls E)
              (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
                (Class.cv (nb095_alpha_dummy_796 u S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_804] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_801 u S_cls E)
              (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
                (Class.cv (nb095_alpha_dummy_795 u S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_801 u S_cls E)
              (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
                (Class.cv (nb095_alpha_dummy_796 u S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb095_fresh_848 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_043 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_034 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_034 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv)
      0

theorem nb095_fresh_849 (f : Var) :
    (nb095_alpha_dummy_044 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_037 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_038 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_044] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_037 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_038 f)))).fv)
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

theorem nb095_fresh_850 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_079 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_070 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_079] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_070 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv)
      0

theorem nb095_fresh_851 (f : Var) :
    (nb095_alpha_dummy_080 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_073 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_074 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_080] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_073 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_074 f)))).fv)
      0

theorem nb095_fresh_852 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_121 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_112 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_121] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_112 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv)
      0

theorem nb095_fresh_853 (f : Var) :
    (nb095_alpha_dummy_122 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_115 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_116 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_122] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_115 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_116 f)))).fv)
      0

theorem nb095_fresh_854 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_157 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_148 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_157] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_148 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv)
      0

theorem nb095_fresh_855 (f : Var) :
    (nb095_alpha_dummy_158 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_151 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_152 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_158] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_151 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_152 f)))).fv)
      0

theorem nb095_fresh_856 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_193 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_184 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_193] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_184 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv)
      0

theorem nb095_fresh_857 (f : Var) :
    (nb095_alpha_dummy_194 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_187 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_188 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_194] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_187 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_188 f)))).fv)
      0

theorem nb095_fresh_858 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_233 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_224 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_233] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_224 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv)
      0

theorem nb095_fresh_859 (f : Var) :
    (nb095_alpha_dummy_234 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_227 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_228 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_234] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_227 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_228 f)))).fv)
      0

theorem nb095_fresh_860 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_279 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_270 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_279] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_270 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv)
      0

theorem nb095_fresh_861 (x : Var) (R : Class) :
    (nb095_alpha_dummy_280 x R) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_273 x R)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_274 x R)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_280] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_273 x R)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_274 x R)))).fv)
      0

theorem nb095_fresh_862 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_323 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_314 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_323] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_314 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv)
      0

theorem nb095_fresh_863 (f : Var) :
    (nb095_alpha_dummy_324 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_317 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_318 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_324] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_317 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_318 f)))).fv)
      0

theorem nb095_fresh_864 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_369 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_360 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_369] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_360 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv)
      0

theorem nb095_fresh_865 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_370 u S_cls) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_363 u S_cls)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_370] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_363 u S_cls)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv)
      0

theorem nb095_fresh_866 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_417 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_408 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_417] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_408 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv)
      0

theorem nb095_fresh_867 (f : Var) :
    (nb095_alpha_dummy_418 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_411 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_412 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_418] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_411 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_412 f)))).fv)
      0

theorem nb095_fresh_868 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_453 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_444 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_453] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_444 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv)
      0

theorem nb095_fresh_869 (f : Var) :
    (nb095_alpha_dummy_454 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_447 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_448 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_454] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_447 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_448 f)))).fv)
      0

theorem nb095_fresh_870 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_495 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_486 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_495] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_486 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv)
      0

theorem nb095_fresh_871 (f : Var) :
    (nb095_alpha_dummy_496 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_489 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_490 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_496] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_489 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_490 f)))).fv)
      0

theorem nb095_fresh_872 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_531 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_522 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_531] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_522 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv)
      0

theorem nb095_fresh_873 (f : Var) :
    (nb095_alpha_dummy_532 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_525 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_526 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_532] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_525 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_526 f)))).fv)
      0

theorem nb095_fresh_874 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_567 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_558 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_567] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_558 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv)
      0

theorem nb095_fresh_875 (f : Var) :
    (nb095_alpha_dummy_568 f) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_561 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_562 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_568] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_561 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_562 f)))).fv)
      0

theorem nb095_fresh_876 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_603 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_594 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_603] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_594 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv)
      0

theorem nb095_fresh_877 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_604 x u D R S_cls f E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_604] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_878 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_649 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_640 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_649] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_640 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv)
      0

theorem nb095_fresh_879 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_650 x D R) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_643 x D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_644 x D R)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_650] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_643 x D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_644 x D R)))).fv)
      0

theorem nb095_fresh_880 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_701 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_692 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_701] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_692 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv)
      0

theorem nb095_fresh_881 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_702 x u D R S_cls f E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_702] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_882 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_731 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_722 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_731] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_722 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv)
      0

theorem nb095_fresh_883 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_732 x u D R S_cls f E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_732] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_884 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_771 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_762 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_771] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_762 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv)
      0

theorem nb095_fresh_885 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_772 x u D R S_cls f E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_772] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_886 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_823 D R S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_814 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_823] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_814 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv)
      0

theorem nb095_fresh_887 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_824 u S_cls E) ∉
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_817 u S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_824] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_817 u S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv)
      0

theorem nb095_fresh_888 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_051 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_051] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_889 (f : Var) :
    (nb095_alpha_dummy_052 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_052] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_890 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_087 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_087] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_891 (f : Var) :
    (nb095_alpha_dummy_088 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_088] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_892 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_129 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_129] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_893 (f : Var) :
    (nb095_alpha_dummy_130 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_130] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_894 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_165 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_165] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_895 (f : Var) :
    (nb095_alpha_dummy_166 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_166] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_896 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_201 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_201] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_897 (f : Var) :
    (nb095_alpha_dummy_202 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_202] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_898 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_241 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_241] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_899 (f : Var) :
    (nb095_alpha_dummy_242 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_242] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_900 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_287 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_287] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_901 (x : Var) (R : Class) :
    (nb095_alpha_dummy_288 x R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_288] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_902 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_331 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_331] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_903 (f : Var) :
    (nb095_alpha_dummy_332 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_332] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_904 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_377 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_377] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_905 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_378 u S_cls) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_378] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_906 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_425 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_425] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_907 (f : Var) :
    (nb095_alpha_dummy_426 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_426] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_908 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_461 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_461] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_909 (f : Var) :
    (nb095_alpha_dummy_462 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_462] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_910 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_503 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_503] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_911 (f : Var) :
    (nb095_alpha_dummy_504 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_504] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_912 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_539 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_539] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_913 (f : Var) :
    (nb095_alpha_dummy_540 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_540] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_914 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_575 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_575] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_915 (f : Var) :
    (nb095_alpha_dummy_576 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_576] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_916 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_611 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_611] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_917 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_612 x u D R S_cls f E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_612] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_918 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_657 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_657] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_919 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_658 x D R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_658] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_920 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_785 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_785] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_921 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_786 x u D R S_cls f E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_786] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_922 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_709 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_709] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_923 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_710 x u D R S_cls f E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_710] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_924 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_779 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_779] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_925 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_780 x u D R S_cls f E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_780] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_926 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_831 D R S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_831] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_927 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_832 u S_cls E) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_832] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb095_fresh_928 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_661 D R S_cls E) ∉
      (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
        ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_661] using
    freshVar_not_mem
      (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
        ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv)
      0

theorem nb095_fresh_929 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_662 D R S_cls E) ∉
      (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
        ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_662] using
    freshVar_not_mem
      (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
        ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv)
      1

theorem nb095_distinct_930 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_661 D R S_cls E) ≠ (nb095_alpha_dummy_662 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_661, nb095_alpha_dummy_662] using
    (freshVar_injective (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
        ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_931 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_663 x u D R S_cls f E) ∉
      (((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
        ((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_663] using
    freshVar_not_mem
      (((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
        ((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_932 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_664 x u D R S_cls f E) ∉
      (((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
        ((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_664] using
    freshVar_not_mem
      (((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
        ((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv)
      1

theorem nb095_distinct_933 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_663 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_664 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_663, nb095_alpha_dummy_664] using
    (freshVar_injective
      (((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
        ((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_934 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_619 D R S_cls E) ∉
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_619] using
    freshVar_not_mem
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_935 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_620 D R S_cls E) ∉
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_620] using
    freshVar_not_mem
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv)
      1

theorem nb095_distinct_936 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_619 D R S_cls E) ≠ (nb095_alpha_dummy_620 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_619, nb095_alpha_dummy_620] using
    (freshVar_injective (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_937 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_621 x D R) ∉
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_621] using
    freshVar_not_mem
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv)
      0

theorem nb095_fresh_938 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_622 x D R) ∉
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_622] using
    freshVar_not_mem
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv)
      1

theorem nb095_distinct_939 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_622 x D R) := by
  simpa only [nb095_alpha_dummy_621, nb095_alpha_dummy_622] using
    (freshVar_injective (((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_940 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_793 D R S_cls E) ∉
      (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_793] using
    freshVar_not_mem
      (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_941 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_794 D R S_cls E) ∉
      (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_794] using
    freshVar_not_mem
      (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
      1

theorem nb095_distinct_942 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_793 D R S_cls E) ≠ (nb095_alpha_dummy_794 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_793, nb095_alpha_dummy_794] using
    (freshVar_injective (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_943 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_795 u S_cls E) ∉
      (((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
        ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_795] using
    freshVar_not_mem
      (((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
        ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
      0

theorem nb095_fresh_944 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_796 u S_cls E) ∉
      (((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
        ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_796] using
    freshVar_not_mem
      (((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
        ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
      1

theorem nb095_distinct_945 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_795 u S_cls E) ≠ (nb095_alpha_dummy_796 u S_cls E) := by
  simpa only [nb095_alpha_dummy_795, nb095_alpha_dummy_796] using
    (freshVar_injective (((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
        ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_946 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_039 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_034 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_034 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_034 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_034 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv)
      0

theorem nb095_fresh_947 (f : Var) :
    (nb095_alpha_dummy_040 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_037 f))
            (Class.cv (nb095_alpha_dummy_038 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_037 f))
            (Class.cv (nb095_alpha_dummy_038 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_037 f))
            (Class.cv (nb095_alpha_dummy_038 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_037 f))
            (Class.cv (nb095_alpha_dummy_038 f)))).fv)
      0

theorem nb095_fresh_948 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_075 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_070 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_070 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_075] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_070 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_070 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv)
      0

theorem nb095_fresh_949 (f : Var) :
    (nb095_alpha_dummy_076 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_073 f))
            (Class.cv (nb095_alpha_dummy_074 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_073 f))
            (Class.cv (nb095_alpha_dummy_074 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_076] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_073 f))
            (Class.cv (nb095_alpha_dummy_074 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_073 f))
            (Class.cv (nb095_alpha_dummy_074 f)))).fv)
      0

theorem nb095_fresh_950 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_117 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_112 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_112 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_117] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_112 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_112 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv)
      0

theorem nb095_fresh_951 (f : Var) :
    (nb095_alpha_dummy_118 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_115 f))
            (Class.cv (nb095_alpha_dummy_116 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_115 f))
            (Class.cv (nb095_alpha_dummy_116 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_118] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_115 f))
            (Class.cv (nb095_alpha_dummy_116 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_115 f))
            (Class.cv (nb095_alpha_dummy_116 f)))).fv)
      0

theorem nb095_fresh_952 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_153 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_148 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_148 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_153] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_148 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_148 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv)
      0

theorem nb095_fresh_953 (f : Var) :
    (nb095_alpha_dummy_154 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_151 f))
            (Class.cv (nb095_alpha_dummy_152 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_151 f))
            (Class.cv (nb095_alpha_dummy_152 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_154] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_151 f))
            (Class.cv (nb095_alpha_dummy_152 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_151 f))
            (Class.cv (nb095_alpha_dummy_152 f)))).fv)
      0

theorem nb095_fresh_954 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_189 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_184 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_184 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_189] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_184 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_184 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv)
      0

theorem nb095_fresh_955 (f : Var) :
    (nb095_alpha_dummy_190 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_187 f))
            (Class.cv (nb095_alpha_dummy_188 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_187 f))
            (Class.cv (nb095_alpha_dummy_188 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_190] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_187 f))
            (Class.cv (nb095_alpha_dummy_188 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_187 f))
            (Class.cv (nb095_alpha_dummy_188 f)))).fv)
      0

theorem nb095_fresh_956 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_229 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_224 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_224 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_229] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_224 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_224 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv)
      0

theorem nb095_fresh_957 (f : Var) :
    (nb095_alpha_dummy_230 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_227 f))
            (Class.cv (nb095_alpha_dummy_228 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_227 f))
            (Class.cv (nb095_alpha_dummy_228 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_230] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_227 f))
            (Class.cv (nb095_alpha_dummy_228 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_227 f))
            (Class.cv (nb095_alpha_dummy_228 f)))).fv)
      0

theorem nb095_fresh_958 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_275 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_270 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_270 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_275] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_270 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_270 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv)
      0

theorem nb095_fresh_959 (x : Var) (R : Class) :
    (nb095_alpha_dummy_276 x R) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_273 x R))
            (Class.cv (nb095_alpha_dummy_274 x R)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_273 x R))
            (Class.cv (nb095_alpha_dummy_274 x R)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_276] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_273 x R))
            (Class.cv (nb095_alpha_dummy_274 x R)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_273 x R))
            (Class.cv (nb095_alpha_dummy_274 x R)))).fv)
      0

theorem nb095_fresh_960 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_319 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_314 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_314 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_319] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_314 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_314 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv)
      0

theorem nb095_fresh_961 (f : Var) :
    (nb095_alpha_dummy_320 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_317 f))
            (Class.cv (nb095_alpha_dummy_318 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_317 f))
            (Class.cv (nb095_alpha_dummy_318 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_320] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_317 f))
            (Class.cv (nb095_alpha_dummy_318 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_317 f))
            (Class.cv (nb095_alpha_dummy_318 f)))).fv)
      0

theorem nb095_fresh_962 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_365 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_360 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_360 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_365] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_360 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_360 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv)
      0

theorem nb095_fresh_963 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_366 u S_cls) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_363 u S_cls))
            (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_363 u S_cls))
            (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_366] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_363 u S_cls))
            (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_363 u S_cls))
            (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv)
      0

theorem nb095_fresh_964 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_413 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_408 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_408 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_413] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_408 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_408 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv)
      0

theorem nb095_fresh_965 (f : Var) :
    (nb095_alpha_dummy_414 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_411 f))
            (Class.cv (nb095_alpha_dummy_412 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_411 f))
            (Class.cv (nb095_alpha_dummy_412 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_414] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_411 f))
            (Class.cv (nb095_alpha_dummy_412 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_411 f))
            (Class.cv (nb095_alpha_dummy_412 f)))).fv)
      0

theorem nb095_fresh_966 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_449 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_444 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_444 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_449] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_444 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_444 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv)
      0

theorem nb095_fresh_967 (f : Var) :
    (nb095_alpha_dummy_450 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_447 f))
            (Class.cv (nb095_alpha_dummy_448 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_447 f))
            (Class.cv (nb095_alpha_dummy_448 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_450] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_447 f))
            (Class.cv (nb095_alpha_dummy_448 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_447 f))
            (Class.cv (nb095_alpha_dummy_448 f)))).fv)
      0

theorem nb095_fresh_968 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_491 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_486 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_486 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_491] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_486 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_486 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_487 D R S_cls E)))).fv)
      0

theorem nb095_fresh_969 (f : Var) :
    (nb095_alpha_dummy_492 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_489 f))
            (Class.cv (nb095_alpha_dummy_490 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_489 f))
            (Class.cv (nb095_alpha_dummy_490 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_492] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_489 f))
            (Class.cv (nb095_alpha_dummy_490 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_489 f))
            (Class.cv (nb095_alpha_dummy_490 f)))).fv)
      0

theorem nb095_fresh_970 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_527 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_522 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_522 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_527] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_522 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_522 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_523 D R S_cls E)))).fv)
      0

theorem nb095_fresh_971 (f : Var) :
    (nb095_alpha_dummy_528 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_525 f))
            (Class.cv (nb095_alpha_dummy_526 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_525 f))
            (Class.cv (nb095_alpha_dummy_526 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_528] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_525 f))
            (Class.cv (nb095_alpha_dummy_526 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_525 f))
            (Class.cv (nb095_alpha_dummy_526 f)))).fv)
      0

theorem nb095_fresh_972 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_563 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_558 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_558 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_563] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_558 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_558 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_559 D R S_cls E)))).fv)
      0

theorem nb095_fresh_973 (f : Var) :
    (nb095_alpha_dummy_564 f) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_561 f))
            (Class.cv (nb095_alpha_dummy_562 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_561 f))
            (Class.cv (nb095_alpha_dummy_562 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_564] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_561 f))
            (Class.cv (nb095_alpha_dummy_562 f)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_561 f))
            (Class.cv (nb095_alpha_dummy_562 f)))).fv)
      0

theorem nb095_fresh_974 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_599 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_594 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_594 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_599] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_594 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_594 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_595 D R S_cls E)))).fv)
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

theorem nb095_fresh_975 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_600 x u D R S_cls f E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_600] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_976 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_645 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_640 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_640 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_645] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_640 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_640 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_641 D R S_cls E)))).fv)
      0

theorem nb095_fresh_977 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_646 x D R) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_643 x D R))
            (Class.cv (nb095_alpha_dummy_644 x D R)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_643 x D R))
            (Class.cv (nb095_alpha_dummy_644 x D R)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_646] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_643 x D R))
            (Class.cv (nb095_alpha_dummy_644 x D R)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_643 x D R))
            (Class.cv (nb095_alpha_dummy_644 x D R)))).fv)
      0

theorem nb095_fresh_978 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_697 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_692 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_692 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_697] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_692 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_692 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv)
      0

theorem nb095_fresh_979 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_698 x u D R S_cls f E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_698] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_980 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_727 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_722 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_722 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_727] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_722 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_722 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv)
      0

theorem nb095_fresh_981 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_728 x u D R S_cls f E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_728] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_982 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_767 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_762 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_762 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_767] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_762 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_762 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv)
      0

theorem nb095_fresh_983 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_768 x u D R S_cls f E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_768] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_984 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_819 D R S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_814 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_814 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_819] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_814 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_814 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv)
      0

theorem nb095_fresh_985 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_820 u S_cls E) ∉
      (((syn_cnin (Class.cv (nb095_alpha_dummy_817 u S_cls E))
            (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_817 u S_cls E))
            (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_820] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb095_alpha_dummy_817 u S_cls E))
            (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_817 u S_cls E))
            (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv)
      0

theorem nb095_fresh_986 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_007 D R S_cls E) ∉
      (((syn_cnin (syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))) (syn_cid))).fv) :=
  by
  simpa only [nb095_alpha_dummy_007] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))) (syn_cid))).fv)
      0

theorem nb095_fresh_987 (f : Var) :
    (nb095_alpha_dummy_008 f) ∉
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) :=
  by
  simpa only [nb095_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv)
      0

theorem nb095_fresh_988 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_381 D R S_cls E) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
              (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))
            (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
              (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))
            (syn_cid))).fv) :=
  by
  simpa only [nb095_alpha_dummy_381] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
              (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))
            (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
              (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))
            (syn_cid))).fv)
      0

theorem nb095_fresh_989 (f : Var) :
    (nb095_alpha_dummy_382 f) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv) :=
  by
  simpa only [nb095_alpha_dummy_382] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv)
      0

theorem nb095_fresh_990 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_291 D R S_cls E) ∉
      (((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_291] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_991 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_292 u S_cls f E) ∉
      (((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_292] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv)
      0

theorem nb095_fresh_992 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_245 D R S_cls E) ∉
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cnin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_245] using
    freshVar_not_mem
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cnin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_993 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_246 x D R) ∉
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cnin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_246] using
    freshVar_not_mem
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv)
      0

theorem nb095_fresh_994 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_335 D R S_cls E) ∉
      (((syn_cnin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cnin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_335] using
    freshVar_not_mem
      (((syn_cnin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cnin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_995 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_336 u S_cls E) ∉
      (((syn_cnin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
        ((syn_cnin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_336] using
    freshVar_not_mem
      (((syn_cnin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
        ((syn_cnin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
      0

theorem nb095_fresh_996 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_615 D R S_cls E) ∉
      (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
        ((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_615] using
    freshVar_not_mem
      (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
        ((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv)
      0

theorem nb095_fresh_997 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_616 x D R) ∉
      (((syn_cnin R (syn_cxp (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv ∪
        ((syn_cnin R (syn_cxp (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_616] using
    freshVar_not_mem
      (((syn_cnin R (syn_cxp (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv ∪
        ((syn_cnin R (syn_cxp (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv)
      0

theorem nb095_fresh_998 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_789 D R S_cls E) ∉
      (((syn_cnin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
        ((syn_cnin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_789] using
    freshVar_not_mem
      (((syn_cnin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
        ((syn_cnin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv)
      0

theorem nb095_fresh_999 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_790 u S_cls E) ∉
      (((syn_cnin S_cls (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u))))))).fv ∪ ((syn_cnin S_cls (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_790] using
    freshVar_not_mem
      (((syn_cnin S_cls (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u))))))).fv ∪ ((syn_cnin S_cls (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u))))))).fv)
      0

theorem nb095_fresh_1000 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_053 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_053] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1001 (f : Var) :
    (nb095_alpha_dummy_054 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_054] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))).fv)
      0

theorem nb095_fresh_1002 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_089 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_089] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1003 (f : Var) :
    (nb095_alpha_dummy_090 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_090] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))).fv)
      0

theorem nb095_fresh_1004 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_131 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_131] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1005 (f : Var) :
    (nb095_alpha_dummy_132 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_132] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))).fv)
      0

theorem nb095_fresh_1006 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_167 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_167] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1007 (f : Var) :
    (nb095_alpha_dummy_168 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_168] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))).fv)
      0

theorem nb095_fresh_1008 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_203 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_203] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1009 (f : Var) :
    (nb095_alpha_dummy_204 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_204] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))).fv)
      0

theorem nb095_fresh_1010 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_243 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_243] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1011 (f : Var) :
    (nb095_alpha_dummy_244 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_244] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))).fv)
      0

theorem nb095_fresh_1012 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_289 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_289] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1013 (x : Var) (R : Class) :
    (nb095_alpha_dummy_290 x R) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_290] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))).fv)
      0

theorem nb095_fresh_1014 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_333 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_333] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1015 (f : Var) :
    (nb095_alpha_dummy_334 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_334] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))).fv)
      0

theorem nb095_fresh_1016 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_379 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_379] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1017 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_380 u S_cls) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_380] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))).fv)
      0

theorem nb095_fresh_1018 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_427 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_427] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1019 (f : Var) :
    (nb095_alpha_dummy_428 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_428] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))).fv)
      0

theorem nb095_fresh_1020 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_463 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_463] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1021 (f : Var) :
    (nb095_alpha_dummy_464 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_464] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))).fv)
      0

theorem nb095_fresh_1022 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_505 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_505] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1023 (f : Var) :
    (nb095_alpha_dummy_506 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_506] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))).fv)
      0

theorem nb095_fresh_1024 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_541 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_541] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1025 (f : Var) :
    (nb095_alpha_dummy_542 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_542] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))).fv)
      0

theorem nb095_fresh_1026 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_577 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_577] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1027 (f : Var) :
    (nb095_alpha_dummy_578 f) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_578] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))).fv)
      0

theorem nb095_fresh_1028 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_613 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_613] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1029 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_614 x u D R S_cls f E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_614] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1030 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_659 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_659] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1031 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_660 x D R) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_660] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))).fv)
      0

theorem nb095_fresh_1032 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_787 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_787] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1033 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_788 x u D R S_cls f E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_788] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1034 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_711 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_711] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1035 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_712 x u D R S_cls f E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_712] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1036 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_781 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_781] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1037 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_782 x u D R S_cls f E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_782] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1038 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_833 D R S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_833] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1039 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_834 u S_cls E) ∉
      (((syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_834] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))).fv)
      0

theorem nb095_fresh_1040 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_293 D R S_cls E) ∉
      (((syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_293] using
    freshVar_not_mem
      (((syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_1041 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_294 u S_cls f E) ∉
      (((syn_crn (Class.cv f))).fv ∪ ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_294] using
    freshVar_not_mem
      (((syn_crn (Class.cv f))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
      0

theorem nb095_fresh_1042 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_247 D R S_cls E) ∉
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_247] using
    freshVar_not_mem
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))).fv)
      0

theorem nb095_fresh_1043 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_248 x D R) ∉
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_248] using
    freshVar_not_mem
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))).fv)
      0

theorem nb095_fresh_1044 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_337 D R S_cls E) ∉
      ((E).fv ∪ ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_337] using
    freshVar_not_mem
      ((E).fv ∪ ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))).fv)
      0

theorem nb095_fresh_1045 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_338 u S_cls E) ∉
      ((E).fv ∪ ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_338] using
    freshVar_not_mem
      ((E).fv ∪ ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))).fv)
      0

theorem nb095_fresh_1046 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_617 D R S_cls E) ∉
      ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_617] using
    freshVar_not_mem
      ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_1047 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_618 x D R) ∉
      ((R).fv ∪ ((syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_618] using
    freshVar_not_mem
      ((R).fv ∪ ((syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))).fv)
      0

theorem nb095_fresh_1048 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∉ ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) := by
  simpa only [nb095_alpha_dummy_000] using
    freshVar_not_mem ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 0

theorem nb095_fresh_1049 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∉ ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) := by
  simpa only [nb095_alpha_dummy_001] using
    freshVar_not_mem ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 1

theorem nb095_fresh_1050 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∉ ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) := by
  simpa only [nb095_alpha_dummy_002] using
    freshVar_not_mem ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 2

theorem nb095_distinct_1051 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_001 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_000, nb095_alpha_dummy_001] using
    (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (i := 0) (j := 1) (by decide))

theorem nb095_distinct_1052 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_002 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_000, nb095_alpha_dummy_002] using
    (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (i := 0) (j := 2) (by decide))

theorem nb095_distinct_1053 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ≠ (nb095_alpha_dummy_002 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_001, nb095_alpha_dummy_002] using
    (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (i := 1) (j := 2) (by decide))

theorem nb095_fresh_1054 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_791 D R S_cls E) ∉
      ((S_cls).fv ∪ ((syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_791] using
    freshVar_not_mem
      ((S_cls).fv ∪ ((syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_1055 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_792 u S_cls E) ∉
      ((S_cls).fv ∪ ((syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_792] using
    freshVar_not_mem
      ((S_cls).fv ∪ ((syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u)))))).fv)
      0

theorem nb095_fresh_1056 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_017 D R S_cls E) ∉
      (({(nb095_alpha_dummy_011 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_012 D R S_cls E)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_013 D R S_cls E) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_017] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_011 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_012 D R S_cls E)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_013 D R S_cls E) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_1057 (f : Var) :
    (nb095_alpha_dummy_018 f) ∉
      (({(nb095_alpha_dummy_014 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_015 f)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_016 f) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_014 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb095_alpha_dummy_016 f)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_016 f)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_015 f)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_018] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_014 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_015 f)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_016 f) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_014 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb095_alpha_dummy_016 f)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_016 f)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_015 f)))))).fv)
      0

theorem nb095_fresh_1058 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_095 D R S_cls E) ∉
      (({(nb095_alpha_dummy_091 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_092 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_091 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_095] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_091 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_092 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_091 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1059 (f : Var) :
    (nb095_alpha_dummy_096 f) ∉
      (({(nb095_alpha_dummy_093 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_094 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_094 f)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_093 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_096] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_093 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_094 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_094 f)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_093 f)))).fv)
      0

theorem nb095_fresh_1060 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_391 D R S_cls E) ∉
      (({(nb095_alpha_dummy_385 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_386 D R S_cls E)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_387 D R S_cls E) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_391] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_385 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_386 D R S_cls E)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_387 D R S_cls E) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
                (Class.cv (nb095_alpha_dummy_386 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_1061 (f : Var) :
    (nb095_alpha_dummy_392 f) ∉
      (({(nb095_alpha_dummy_388 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_389 f)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_390 f) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_388 f))
                (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb095_alpha_dummy_390 f)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_390 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb095_alpha_dummy_389 f)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_392] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_388 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_389 f)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_390 f) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_388 f))
                (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb095_alpha_dummy_390 f)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_390 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb095_alpha_dummy_389 f)))))).fv)
      0

theorem nb095_fresh_1062 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_469 D R S_cls E) ∉
      (({(nb095_alpha_dummy_465 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_466 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
            (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
            (Class.cv (nb095_alpha_dummy_465 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_469] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_465 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_466 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
            (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
            (Class.cv (nb095_alpha_dummy_465 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1063 (f : Var) :
    (nb095_alpha_dummy_470 f) ∉
      (({(nb095_alpha_dummy_467 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_468 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_468 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb095_alpha_dummy_467 f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_470] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_467 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_468 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_468 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb095_alpha_dummy_467 f)))).fv)
      0

theorem nb095_fresh_1064 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_623 D R S_cls E) ∉
      (({(nb095_alpha_dummy_619 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_620 D R S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_619 D R S_cls E)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_620 D R S_cls E)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_623] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_619 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_620 D R S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_619 D R S_cls E)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_620 D R S_cls E)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv)
      0

theorem nb095_fresh_1065 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_624 x D R) ∉
      (({(nb095_alpha_dummy_621 x D R)} : Finset Var) ∪
          ({(nb095_alpha_dummy_622 x D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_621 x D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_622 x D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_624] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_621 x D R)} : Finset Var) ∪
          ({(nb095_alpha_dummy_622 x D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_621 x D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_622 x D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv)
      0

theorem nb095_fresh_1066 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_671 D R S_cls E) ∉
      (({(nb095_alpha_dummy_669 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_669 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_671] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_669 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_669 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1067 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_672 x u D R S_cls f E) ∉
      (({(nb095_alpha_dummy_670 x u D R S_cls f E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_672] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_670 x u D R S_cls f E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1068 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_741 D R S_cls E) ∉
      (({(nb095_alpha_dummy_739 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_739 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_741] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_739 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_739 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1069 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_742 x u D R S_cls f E) ∉
      (({(nb095_alpha_dummy_740 x u D R S_cls f E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_742] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_740 x u D R S_cls f E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1070 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_797 D R S_cls E) ∉
      (({(nb095_alpha_dummy_793 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_794 D R S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_794 D R S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_797] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_793 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_794 D R S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_794 D R S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv)
      0

theorem nb095_fresh_1071 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_798 u S_cls E) ∉
      (({(nb095_alpha_dummy_795 u S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_796 u S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_796 u S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_798] using
    freshVar_not_mem
      (({(nb095_alpha_dummy_795 u S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_796 u S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_796 u S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))))).fv)
      0

theorem nb095_support_mem_0000 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_011 D R S_cls E) ∈
      (({(nb095_alpha_dummy_011 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_012 D R S_cls E)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_013 D R S_cls E) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0001 (f : Var) :
    (nb095_alpha_dummy_014 f) ∈
      (({(nb095_alpha_dummy_014 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_015 f)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_016 f) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_014 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb095_alpha_dummy_016 f)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_016 f)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_015 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0002 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_012 D R S_cls E) ∈
      (({(nb095_alpha_dummy_011 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_012 D R S_cls E)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_013 D R S_cls E) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0003 (f : Var) :
    (nb095_alpha_dummy_015 f) ∈
      (({(nb095_alpha_dummy_014 f)} : Finset Var) ∪ ({(nb095_alpha_dummy_015 f)} : Finset Var) ∪
        ((syn_wex (nb095_alpha_dummy_016 f) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_014 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb095_alpha_dummy_016 f)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_016 f)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_015 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0004 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_011 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0005 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_011 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_011 D R S_cls E) ≠ (nb095_alpha_dummy_019 D R S_cls E) from (by
          unfold nb095_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_011 D R S_cls E) ≠ (nb095_alpha_dummy_020 D R S_cls E) from (by
            unfold nb095_alpha_dummy_020;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0006 (f : Var) :
    (nb095_alpha_dummy_014 f) ∈
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
