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
    (nb095AlphaDummy207 f) ∉ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb095AlphaDummy207] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 0

theorem nb095_fresh_790 (f : Var) :
    (nb095AlphaDummy208 f) ∉ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb095AlphaDummy208] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 1

theorem nb095_distinct_791 (f : Var) :
    (nb095AlphaDummy207 f) ≠ (nb095AlphaDummy208 f) := by
  simpa only [nb095AlphaDummy207, nb095AlphaDummy208] using
    (freshVar_injective (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_792 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy249 D R S_cls E) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy249] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
      0

theorem nb095_fresh_793 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy250 D R S_cls E) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy250] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
      1

theorem nb095_distinct_794 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy250 D R S_cls E) := by
  simpa only [nb095AlphaDummy249, nb095AlphaDummy250] using
    (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_795 (x : Var) (R : Class) :
    (nb095AlphaDummy251 x R) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn (Class.cv x))).fv) :=
  by
  simpa only [nb095AlphaDummy251] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn (Class.cv x))).fv) 0

theorem nb095_fresh_796 (x : Var) (R : Class) :
    (nb095AlphaDummy252 x R) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn (Class.cv x))).fv) :=
  by
  simpa only [nb095AlphaDummy252] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn (Class.cv x))).fv) 1

theorem nb095_distinct_797 (x : Var) (R : Class) :
    (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy252 x R) := by
  simpa only [nb095AlphaDummy251, nb095AlphaDummy252] using
    (freshVar_injective
      (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn (Class.cv x))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_798 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy339 D R S_cls E) ∉
      (((synCcnv (synCdif S_cls (synCid)))).fv ∪
        ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy339] using
    freshVar_not_mem
      (((synCcnv (synCdif S_cls (synCid)))).fv ∪
        ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
      0

theorem nb095_fresh_799 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy340 D R S_cls E) ∉
      (((synCcnv (synCdif S_cls (synCid)))).fv ∪
        ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy340] using
    freshVar_not_mem
      (((synCcnv (synCdif S_cls (synCid)))).fv ∪
        ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
      1

theorem nb095_distinct_800 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy339 D R S_cls E) ≠ (nb095AlphaDummy340 D R S_cls E) := by
  simpa only [nb095AlphaDummy339, nb095AlphaDummy340] using
    (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪
        ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_801 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy341 u S_cls) ∉
      (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn (Class.cv u))).fv) :=
  by
  simpa only [nb095AlphaDummy341] using
    freshVar_not_mem
      (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn (Class.cv u))).fv) 0

theorem nb095_fresh_802 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy342 u S_cls) ∉
      (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn (Class.cv u))).fv) :=
  by
  simpa only [nb095AlphaDummy342] using
    freshVar_not_mem
      (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn (Class.cv u))).fv) 1

theorem nb095_distinct_803 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy342 u S_cls) := by
  simpa only [nb095AlphaDummy341, nb095AlphaDummy342] using
    (freshVar_injective
      (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn (Class.cv u))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_804 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy009 D R S_cls E) ∉
      (((synCcom (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb095AlphaDummy009] using
    freshVar_not_mem
      (((synCcom (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv ∪ ((synCid)).fv)
      0

theorem nb095_fresh_805 (f : Var) :
    (nb095AlphaDummy010 f) ∉
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb095AlphaDummy010] using
    freshVar_not_mem
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0

theorem nb095_fresh_806 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy383 D R S_cls E) ∉
      (((synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
            (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))).fv ∪
        ((synCid)).fv) :=
  by
  simpa only [nb095AlphaDummy383] using
    freshVar_not_mem
      (((synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
            (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))).fv ∪
        ((synCid)).fv)
      0

theorem nb095_fresh_807 (f : Var) :
    (nb095AlphaDummy384 f) ∉
      (((synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))).fv ∪
        ((synCid)).fv) :=
  by
  simpa only [nb095AlphaDummy384] using
    freshVar_not_mem
      (((synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))).fv ∪
        ((synCid)).fv)
      0

theorem nb095_fresh_808 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy023 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy019 D R S_cls E)
              (synWrex (nb095AlphaDummy020 D R S_cls E)
                (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy019 D R S_cls E)
              (synWrex (nb095AlphaDummy020 D R S_cls E)
                (Class.cv (nb095AlphaDummy012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy023] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy019 D R S_cls E)
              (synWrex (nb095AlphaDummy020 D R S_cls E)
                (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy019 D R S_cls E)
              (synWrex (nb095AlphaDummy020 D R S_cls E)
                (Class.cv (nb095AlphaDummy012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_809 (f : Var) :
    (nb095AlphaDummy024 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy021 f)
              (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                  (synCphi (Class.cv (nb095AlphaDummy022 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy021 f)
              (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy015 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy022 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy024] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy021 f)
              (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                  (synCphi (Class.cv (nb095AlphaDummy022 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy021 f)
              (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy015 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy022 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_810 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy059 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy055 D R S_cls E)
              (synWrex (nb095AlphaDummy056 D R S_cls E)
                (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy055 D R S_cls E)
              (synWrex (nb095AlphaDummy056 D R S_cls E)
                (Class.cv (nb095AlphaDummy013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy059] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy055 D R S_cls E)
              (synWrex (nb095AlphaDummy056 D R S_cls E)
                (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy055 D R S_cls E)
              (synWrex (nb095AlphaDummy056 D R S_cls E)
                (Class.cv (nb095AlphaDummy013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_811 (f : Var) :
    (nb095AlphaDummy060 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy057 f)
              (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                  (synCphi (Class.cv (nb095AlphaDummy058 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy057 f)
              (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy016 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy058 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy060] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy057 f)
              (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                  (synCphi (Class.cv (nb095AlphaDummy058 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy057 f)
              (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy016 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy058 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_812 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy101 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy097 D R S_cls E)
              (synWrex (nb095AlphaDummy098 D R S_cls E)
                (Class.cv (nb095AlphaDummy091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy097 D R S_cls E)
              (synWrex (nb095AlphaDummy098 D R S_cls E)
                (Class.cv (nb095AlphaDummy092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy101] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy097 D R S_cls E)
              (synWrex (nb095AlphaDummy098 D R S_cls E)
                (Class.cv (nb095AlphaDummy091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy097 D R S_cls E)
              (synWrex (nb095AlphaDummy098 D R S_cls E)
                (Class.cv (nb095AlphaDummy092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_813 (f : Var) :
    (nb095AlphaDummy102 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy099 f)
              (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                  (synCphi (Class.cv (nb095AlphaDummy100 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy099 f)
              (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy094 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy100 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy102] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy099 f)
              (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                  (synCphi (Class.cv (nb095AlphaDummy100 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy099 f)
              (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy094 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy100 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_814 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy137 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy133 D R S_cls E)
              (synWrex (nb095AlphaDummy134 D R S_cls E)
                (Class.cv (nb095AlphaDummy092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy133 D R S_cls E)
              (synWrex (nb095AlphaDummy134 D R S_cls E)
                (Class.cv (nb095AlphaDummy091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy137] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy133 D R S_cls E)
              (synWrex (nb095AlphaDummy134 D R S_cls E)
                (Class.cv (nb095AlphaDummy092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy133 D R S_cls E)
              (synWrex (nb095AlphaDummy134 D R S_cls E)
                (Class.cv (nb095AlphaDummy091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_815 (f : Var) :
    (nb095AlphaDummy138 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy135 f)
              (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy094 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                  (synCphi (Class.cv (nb095AlphaDummy136 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy135 f)
              (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy093 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy136 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy138] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy135 f)
              (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy094 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                  (synCphi (Class.cv (nb095AlphaDummy136 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy135 f)
              (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy093 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy136 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_816 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy173 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy169 D R S_cls E)
              (synWrex (nb095AlphaDummy170 D R S_cls E)
                (Class.cv (nb095AlphaDummy013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy169 D R S_cls E)
              (synWrex (nb095AlphaDummy170 D R S_cls E)
                (Class.cv (nb095AlphaDummy012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy173] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy169 D R S_cls E)
              (synWrex (nb095AlphaDummy170 D R S_cls E)
                (Class.cv (nb095AlphaDummy013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy169 D R S_cls E)
              (synWrex (nb095AlphaDummy170 D R S_cls E)
                (Class.cv (nb095AlphaDummy012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_817 (f : Var) :
    (nb095AlphaDummy174 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy171 f)
              (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                  (synCphi (Class.cv (nb095AlphaDummy172 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy171 f)
              (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy015 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy172 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy174] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy171 f)
              (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                  (synCphi (Class.cv (nb095AlphaDummy172 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy171 f)
              (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy015 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy172 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_818 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy213 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy209 D R S_cls E)
              (synWrex (nb095AlphaDummy210 D R S_cls E)
                (Class.cv (nb095AlphaDummy206 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy209 D R S_cls E)
              (synWrex (nb095AlphaDummy210 D R S_cls E)
                (Class.cv (nb095AlphaDummy205 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy213] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy209 D R S_cls E)
              (synWrex (nb095AlphaDummy210 D R S_cls E)
                (Class.cv (nb095AlphaDummy206 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy209 D R S_cls E)
              (synWrex (nb095AlphaDummy210 D R S_cls E)
                (Class.cv (nb095AlphaDummy205 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_819 (f : Var) :
    (nb095AlphaDummy214 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy211 f)
              (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy208 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                  (synCphi (Class.cv (nb095AlphaDummy212 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy211 f)
              (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy207 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy212 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy214] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy211 f)
              (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy208 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                  (synCphi (Class.cv (nb095AlphaDummy212 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy211 f)
              (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy207 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy212 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_820 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy259 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy255 D R S_cls E)
              (synWrex (nb095AlphaDummy256 D R S_cls E)
                (Class.cv (nb095AlphaDummy250 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy255 D R S_cls E)
              (synWrex (nb095AlphaDummy256 D R S_cls E)
                (Class.cv (nb095AlphaDummy249 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy259] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy255 D R S_cls E)
              (synWrex (nb095AlphaDummy256 D R S_cls E)
                (Class.cv (nb095AlphaDummy250 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy255 D R S_cls E)
              (synWrex (nb095AlphaDummy256 D R S_cls E)
                (Class.cv (nb095AlphaDummy249 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_821 (x : Var) (R : Class) :
    (nb095AlphaDummy260 x R) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy257 x R)
              (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy252 x R))
                (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                  (synCphi (Class.cv (nb095AlphaDummy258 x R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy257 x R)
              (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy251 x R))
                (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy258 x R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy260] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy257 x R)
              (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy252 x R))
                (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                  (synCphi (Class.cv (nb095AlphaDummy258 x R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy257 x R)
              (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy251 x R))
                (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy258 x R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_822 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy303 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy299 D R S_cls E)
              (synWrex (nb095AlphaDummy300 D R S_cls E)
                (Class.cv (nb095AlphaDummy296 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy299 D R S_cls E)
              (synWrex (nb095AlphaDummy300 D R S_cls E)
                (Class.cv (nb095AlphaDummy295 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy303] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy299 D R S_cls E)
              (synWrex (nb095AlphaDummy300 D R S_cls E)
                (Class.cv (nb095AlphaDummy296 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy299 D R S_cls E)
              (synWrex (nb095AlphaDummy300 D R S_cls E)
                (Class.cv (nb095AlphaDummy295 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_823 (f : Var) :
    (nb095AlphaDummy304 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy301 f)
              (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                  (synCphi (Class.cv (nb095AlphaDummy302 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy301 f)
              (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy297 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy302 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy304] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy301 f)
              (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                  (synCphi (Class.cv (nb095AlphaDummy302 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy301 f)
              (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy297 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy302 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_824 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy349 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy345 D R S_cls E)
              (synWrex (nb095AlphaDummy346 D R S_cls E)
                (Class.cv (nb095AlphaDummy340 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy345 D R S_cls E)
              (synWrex (nb095AlphaDummy346 D R S_cls E)
                (Class.cv (nb095AlphaDummy339 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy349] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy345 D R S_cls E)
              (synWrex (nb095AlphaDummy346 D R S_cls E)
                (Class.cv (nb095AlphaDummy340 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy345 D R S_cls E)
              (synWrex (nb095AlphaDummy346 D R S_cls E)
                (Class.cv (nb095AlphaDummy339 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_825 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy350 u S_cls) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy347 u S_cls)
              (synWrex (nb095AlphaDummy348 u S_cls)
                (Class.cv (nb095AlphaDummy342 u S_cls))
                (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                  (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
                (Class.cv (nb095AlphaDummy341 u S_cls))
                (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy350] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy347 u S_cls)
              (synWrex (nb095AlphaDummy348 u S_cls)
                (Class.cv (nb095AlphaDummy342 u S_cls))
                (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                  (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
                (Class.cv (nb095AlphaDummy341 u S_cls))
                (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_826 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy397 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy393 D R S_cls E)
              (synWrex (nb095AlphaDummy394 D R S_cls E)
                (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy393 D R S_cls E)
              (synWrex (nb095AlphaDummy394 D R S_cls E)
                (Class.cv (nb095AlphaDummy386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy397] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy393 D R S_cls E)
              (synWrex (nb095AlphaDummy394 D R S_cls E)
                (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy393 D R S_cls E)
              (synWrex (nb095AlphaDummy394 D R S_cls E)
                (Class.cv (nb095AlphaDummy386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_827 (f : Var) :
    (nb095AlphaDummy398 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy395 f)
              (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                  (synCphi (Class.cv (nb095AlphaDummy396 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy395 f)
              (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy398] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy395 f)
              (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                  (synCphi (Class.cv (nb095AlphaDummy396 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy395 f)
              (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_828 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy433 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy429 D R S_cls E)
              (synWrex (nb095AlphaDummy430 D R S_cls E)
                (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy429 D R S_cls E)
              (synWrex (nb095AlphaDummy430 D R S_cls E)
                (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy433] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy429 D R S_cls E)
              (synWrex (nb095AlphaDummy430 D R S_cls E)
                (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy429 D R S_cls E)
              (synWrex (nb095AlphaDummy430 D R S_cls E)
                (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_829 (f : Var) :
    (nb095AlphaDummy434 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy431 f)
              (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                  (synCphi (Class.cv (nb095AlphaDummy432 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy431 f)
              (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy434] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy431 f)
              (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                  (synCphi (Class.cv (nb095AlphaDummy432 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy431 f)
              (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_830 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy475 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy471 D R S_cls E)
              (synWrex (nb095AlphaDummy472 D R S_cls E)
                (Class.cv (nb095AlphaDummy465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy471 D R S_cls E)
              (synWrex (nb095AlphaDummy472 D R S_cls E)
                (Class.cv (nb095AlphaDummy466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy475] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy471 D R S_cls E)
              (synWrex (nb095AlphaDummy472 D R S_cls E)
                (Class.cv (nb095AlphaDummy465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy471 D R S_cls E)
              (synWrex (nb095AlphaDummy472 D R S_cls E)
                (Class.cv (nb095AlphaDummy466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_831 (f : Var) :
    (nb095AlphaDummy476 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy473 f)
              (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                  (synCphi (Class.cv (nb095AlphaDummy474 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy473 f)
              (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy476] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy473 f)
              (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                  (synCphi (Class.cv (nb095AlphaDummy474 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy473 f)
              (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_832 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy511 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy507 D R S_cls E)
              (synWrex (nb095AlphaDummy508 D R S_cls E)
                (Class.cv (nb095AlphaDummy466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy507 D R S_cls E)
              (synWrex (nb095AlphaDummy508 D R S_cls E)
                (Class.cv (nb095AlphaDummy465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy511] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy507 D R S_cls E)
              (synWrex (nb095AlphaDummy508 D R S_cls E)
                (Class.cv (nb095AlphaDummy466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy507 D R S_cls E)
              (synWrex (nb095AlphaDummy508 D R S_cls E)
                (Class.cv (nb095AlphaDummy465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_833 (f : Var) :
    (nb095AlphaDummy512 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy509 f)
              (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                  (synCphi (Class.cv (nb095AlphaDummy510 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy509 f)
              (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy512] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy509 f)
              (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                  (synCphi (Class.cv (nb095AlphaDummy510 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy509 f)
              (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_834 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy547 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy543 D R S_cls E)
              (synWrex (nb095AlphaDummy544 D R S_cls E)
                (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy543 D R S_cls E)
              (synWrex (nb095AlphaDummy544 D R S_cls E)
                (Class.cv (nb095AlphaDummy386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy547] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy543 D R S_cls E)
              (synWrex (nb095AlphaDummy544 D R S_cls E)
                (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy543 D R S_cls E)
              (synWrex (nb095AlphaDummy544 D R S_cls E)
                (Class.cv (nb095AlphaDummy386 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_835 (f : Var) :
    (nb095AlphaDummy548 f) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy545 f)
              (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                  (synCphi (Class.cv (nb095AlphaDummy546 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy545 f)
              (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy548] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy545 f)
              (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                  (synCphi (Class.cv (nb095AlphaDummy546 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy545 f)
              (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_836 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy583 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy579 D R S_cls E)
              (synWrex (nb095AlphaDummy580 D R S_cls E)
                (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy579 D R S_cls E)
              (synWrex (nb095AlphaDummy580 D R S_cls E)
                (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy583] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy579 D R S_cls E)
              (synWrex (nb095AlphaDummy580 D R S_cls E)
                (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy579 D R S_cls E)
              (synWrex (nb095AlphaDummy580 D R S_cls E)
                (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_837 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy584 x u D R S_cls f E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy584] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_838 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy629 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy625 D R S_cls E)
              (synWrex (nb095AlphaDummy626 D R S_cls E)
                (Class.cv (nb095AlphaDummy619 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy625 D R S_cls E)
              (synWrex (nb095AlphaDummy626 D R S_cls E)
                (Class.cv (nb095AlphaDummy620 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy629] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy625 D R S_cls E)
              (synWrex (nb095AlphaDummy626 D R S_cls E)
                (Class.cv (nb095AlphaDummy619 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy625 D R S_cls E)
              (synWrex (nb095AlphaDummy626 D R S_cls E)
                (Class.cv (nb095AlphaDummy620 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_839 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy630 x D R) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy627 x D R)
              (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy621 x D R))
                (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                  (synCphi (Class.cv (nb095AlphaDummy628 x D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
                (Class.cv (nb095AlphaDummy622 x D R))
                (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy630] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy627 x D R)
              (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy621 x D R))
                (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                  (synCphi (Class.cv (nb095AlphaDummy628 x D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
                (Class.cv (nb095AlphaDummy622 x D R))
                (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_840 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy665 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy661 D R S_cls E)
              (synWrex (nb095AlphaDummy662 D R S_cls E)
                (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                  (Class.cv (nb095AlphaDummy003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy661 D R S_cls E)
              (synWrex (nb095AlphaDummy662 D R S_cls E)
                (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                  (Class.cv (nb095AlphaDummy004 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy665] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy661 D R S_cls E)
              (synWrex (nb095AlphaDummy662 D R S_cls E)
                (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                  (Class.cv (nb095AlphaDummy003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy661 D R S_cls E)
              (synWrex (nb095AlphaDummy662 D R S_cls E)
                (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                  (Class.cv (nb095AlphaDummy004 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_841 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy666 x u D R S_cls f E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy664 x u D R S_cls f E) (synCfv (Class.cv f)
                  (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy664 x u D R S_cls f E) (synCfv (Class.cv f)
                  (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy666] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy664 x u D R S_cls f E) (synCfv (Class.cv f)
                  (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy664 x u D R S_cls f E) (synCfv (Class.cv f)
                  (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_842 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy681 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy677 D R S_cls E)
              (synWrex (nb095AlphaDummy678 D R S_cls E)
                (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy677 D R S_cls E)
              (synWrex (nb095AlphaDummy678 D R S_cls E)
                (Class.cv (nb095AlphaDummy669 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy681] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy677 D R S_cls E)
              (synWrex (nb095AlphaDummy678 D R S_cls E)
                (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy677 D R S_cls E)
              (synWrex (nb095AlphaDummy678 D R S_cls E)
                (Class.cv (nb095AlphaDummy669 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_843 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy682 x u D R S_cls f E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy682] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_844 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy751 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy747 D R S_cls E)
              (synWrex (nb095AlphaDummy748 D R S_cls E)
                (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy747 D R S_cls E)
              (synWrex (nb095AlphaDummy748 D R S_cls E)
                (Class.cv (nb095AlphaDummy739 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy751] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy747 D R S_cls E)
              (synWrex (nb095AlphaDummy748 D R S_cls E)
                (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy747 D R S_cls E)
              (synWrex (nb095AlphaDummy748 D R S_cls E)
                (Class.cv (nb095AlphaDummy739 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_845 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy752 x u D R S_cls f E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy752] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_846 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy803 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy794 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy803] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy794 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_847 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy804 u S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy801 u S_cls E)
              (synWrex (nb095AlphaDummy802 u S_cls E)
                (Class.cv (nb095AlphaDummy795 u S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy801 u S_cls E)
              (synWrex (nb095AlphaDummy802 u S_cls E)
                (Class.cv (nb095AlphaDummy796 u S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy804] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy801 u S_cls E)
              (synWrex (nb095AlphaDummy802 u S_cls E)
                (Class.cv (nb095AlphaDummy795 u S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy801 u S_cls E)
              (synWrex (nb095AlphaDummy802 u S_cls E)
                (Class.cv (nb095AlphaDummy796 u S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb095_fresh_848 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy043 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy034 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy035 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy043] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy034 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy035 D R S_cls E)))).fv)
      0

theorem nb095_fresh_849 (f : Var) :
    (nb095AlphaDummy044 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy037 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy038 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy044] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy037 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy038 f)))).fv)
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
    (nb095AlphaDummy079 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy070 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy071 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy079] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy070 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy071 D R S_cls E)))).fv)
      0

theorem nb095_fresh_851 (f : Var) :
    (nb095AlphaDummy080 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy073 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy074 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy080] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy073 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy074 f)))).fv)
      0

theorem nb095_fresh_852 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy121 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy112 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy113 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy121] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy112 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy113 D R S_cls E)))).fv)
      0

theorem nb095_fresh_853 (f : Var) :
    (nb095AlphaDummy122 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy115 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy116 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy122] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy115 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy116 f)))).fv)
      0

theorem nb095_fresh_854 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy157 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy148 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy149 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy157] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy148 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy149 D R S_cls E)))).fv)
      0

theorem nb095_fresh_855 (f : Var) :
    (nb095AlphaDummy158 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy151 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy152 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy158] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy151 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy152 f)))).fv)
      0

theorem nb095_fresh_856 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy193 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy184 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy185 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy193] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy184 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy185 D R S_cls E)))).fv)
      0

theorem nb095_fresh_857 (f : Var) :
    (nb095AlphaDummy194 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy187 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy188 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy194] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy187 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy188 f)))).fv)
      0

theorem nb095_fresh_858 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy233 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy224 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy225 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy233] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy224 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy225 D R S_cls E)))).fv)
      0

theorem nb095_fresh_859 (f : Var) :
    (nb095AlphaDummy234 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy227 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy228 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy234] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy227 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy228 f)))).fv)
      0

theorem nb095_fresh_860 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy279 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy270 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy271 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy279] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy270 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy271 D R S_cls E)))).fv)
      0

theorem nb095_fresh_861 (x : Var) (R : Class) :
    (nb095AlphaDummy280 x R) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy273 x R)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy274 x R)))).fv) :=
  by
  simpa only [nb095AlphaDummy280] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy273 x R)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy274 x R)))).fv)
      0

theorem nb095_fresh_862 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy323 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy314 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy315 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy323] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy314 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy315 D R S_cls E)))).fv)
      0

theorem nb095_fresh_863 (f : Var) :
    (nb095AlphaDummy324 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy317 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy318 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy324] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy317 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy318 f)))).fv)
      0

theorem nb095_fresh_864 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy369 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy360 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy361 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy369] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy360 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy361 D R S_cls E)))).fv)
      0

theorem nb095_fresh_865 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy370 u S_cls) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy363 u S_cls)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy364 u S_cls)))).fv) :=
  by
  simpa only [nb095AlphaDummy370] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy363 u S_cls)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy364 u S_cls)))).fv)
      0

theorem nb095_fresh_866 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy417 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy408 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy417] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy408 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv)
      0

theorem nb095_fresh_867 (f : Var) :
    (nb095AlphaDummy418 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy411 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy412 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy418] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy411 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy412 f)))).fv)
      0

theorem nb095_fresh_868 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy453 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy444 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy453] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy444 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv)
      0

theorem nb095_fresh_869 (f : Var) :
    (nb095AlphaDummy454 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy447 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy448 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy454] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy447 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy448 f)))).fv)
      0

theorem nb095_fresh_870 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy495 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy486 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy495] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy486 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv)
      0

theorem nb095_fresh_871 (f : Var) :
    (nb095AlphaDummy496 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy489 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy490 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy496] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy489 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy490 f)))).fv)
      0

theorem nb095_fresh_872 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy531 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy522 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy531] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy522 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv)
      0

theorem nb095_fresh_873 (f : Var) :
    (nb095AlphaDummy532 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy525 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy526 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy532] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy525 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy526 f)))).fv)
      0

theorem nb095_fresh_874 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy567 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy558 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy567] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy558 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv)
      0

theorem nb095_fresh_875 (f : Var) :
    (nb095AlphaDummy568 f) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy561 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy562 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy568] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy561 f)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy562 f)))).fv)
      0

theorem nb095_fresh_876 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy603 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy594 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy603] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy594 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv)
      0

theorem nb095_fresh_877 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy604 x u D R S_cls f E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy597 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy604] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy597 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_878 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy649 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy640 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy649] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy640 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv)
      0

theorem nb095_fresh_879 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy650 x D R) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy643 x D R)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy644 x D R)))).fv) :=
  by
  simpa only [nb095AlphaDummy650] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy643 x D R)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy644 x D R)))).fv)
      0

theorem nb095_fresh_880 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy701 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy692 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy701] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy692 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv)
      0

theorem nb095_fresh_881 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy702 x u D R S_cls f E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy695 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy702] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy695 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_882 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy731 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy722 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy731] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy722 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv)
      0

theorem nb095_fresh_883 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy732 x u D R S_cls f E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy725 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy732] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy725 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_884 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy771 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy762 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy771] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy762 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv)
      0

theorem nb095_fresh_885 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy772 x u D R S_cls f E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy765 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy772] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy765 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_886 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy823 D R S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy814 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy823] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy814 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv)
      0

theorem nb095_fresh_887 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy824 u S_cls E) ∉
      (((synCcompl (Class.cv (nb095AlphaDummy817 u S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy824] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb095AlphaDummy817 u S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv)
      0

theorem nb095_fresh_888 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy051 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy051] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_889 (f : Var) :
    (nb095AlphaDummy052 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy022 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy052] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy022 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_890 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy087 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy087] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_891 (f : Var) :
    (nb095AlphaDummy088 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy058 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy088] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy058 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_892 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy129 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy129] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_893 (f : Var) :
    (nb095AlphaDummy130 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy100 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy130] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy100 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_894 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy165 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy165] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_895 (f : Var) :
    (nb095AlphaDummy166 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy136 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy166] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy136 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_896 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy201 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy201] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_897 (f : Var) :
    (nb095AlphaDummy202 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy172 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy202] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy172 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_898 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy241 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy241] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_899 (f : Var) :
    (nb095AlphaDummy242 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy212 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy242] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy212 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_900 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy287 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy287] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_901 (x : Var) (R : Class) :
    (nb095AlphaDummy288 x R) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy258 x R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy288] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy258 x R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_902 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy331 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy331] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_903 (f : Var) :
    (nb095AlphaDummy332 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy302 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy332] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy302 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_904 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy377 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy377] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_905 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy378 u S_cls) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy378] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_906 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy425 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy425] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_907 (f : Var) :
    (nb095AlphaDummy426 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy396 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy426] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy396 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_908 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy461 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy461] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_909 (f : Var) :
    (nb095AlphaDummy462 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy432 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy462] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy432 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_910 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy503 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy503] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_911 (f : Var) :
    (nb095AlphaDummy504 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy474 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy504] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy474 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_912 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy539 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy539] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_913 (f : Var) :
    (nb095AlphaDummy540 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy510 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy540] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy510 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_914 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy575 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy575] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_915 (f : Var) :
    (nb095AlphaDummy576 f) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy546 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy576] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy546 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_916 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy611 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy611] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_917 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy612 x u D R S_cls f E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy612] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_918 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy657 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy657] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_919 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy658 x D R) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy628 x D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy658] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy628 x D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_920 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy785 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy785] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_921 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy786 x u D R S_cls f E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy786] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_922 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy709 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy709] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_923 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy710 x u D R S_cls f E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy710] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_924 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy779 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy779] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_925 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy780 x u D R S_cls f E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy780] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_926 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy831 D R S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy831] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_927 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy832 u S_cls E) ∉
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb095AlphaDummy832] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb095_fresh_928 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy661 D R S_cls E) ∉
      (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
        ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy661] using
    freshVar_not_mem
      (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
        ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv)
      0

theorem nb095_fresh_929 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy662 D R S_cls E) ∉
      (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
        ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy662] using
    freshVar_not_mem
      (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
        ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv)
      1

theorem nb095_distinct_930 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy661 D R S_cls E) ≠ (nb095AlphaDummy662 D R S_cls E) := by
  simpa only [nb095AlphaDummy661, nb095AlphaDummy662] using
    (freshVar_injective (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
        ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_931 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy663 x u D R S_cls f E) ∉
      (((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
        ((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy663] using
    freshVar_not_mem
      (((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
        ((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_932 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy664 x u D R S_cls f E) ∉
      (((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
        ((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy664] using
    freshVar_not_mem
      (((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
        ((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv)
      1

theorem nb095_distinct_933 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy663 x u D R S_cls f E) ≠
      (nb095AlphaDummy664 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy663, nb095AlphaDummy664] using
    (freshVar_injective
      (((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
        ((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_934 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy619 D R S_cls E) ∉
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy619] using
    freshVar_not_mem
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_935 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy620 D R S_cls E) ∉
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy620] using
    freshVar_not_mem
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv)
      1

theorem nb095_distinct_936 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy619 D R S_cls E) ≠ (nb095AlphaDummy620 D R S_cls E) := by
  simpa only [nb095AlphaDummy619, nb095AlphaDummy620] using
    (freshVar_injective (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_937 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy621 x D R) ∉
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv) :=
  by
  simpa only [nb095AlphaDummy621] using
    freshVar_not_mem
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv)
      0

theorem nb095_fresh_938 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy622 x D R) ∉
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv) :=
  by
  simpa only [nb095AlphaDummy622] using
    freshVar_not_mem
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv)
      1

theorem nb095_distinct_939 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy622 x D R) := by
  simpa only [nb095AlphaDummy621, nb095AlphaDummy622] using
    (freshVar_injective (((synCin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_940 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy793 D R S_cls E) ∉
      (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy793] using
    freshVar_not_mem
      (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_941 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy794 D R S_cls E) ∉
      (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy794] using
    freshVar_not_mem
      (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
      1

theorem nb095_distinct_942 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy793 D R S_cls E) ≠ (nb095AlphaDummy794 D R S_cls E) := by
  simpa only [nb095AlphaDummy793, nb095AlphaDummy794] using
    (freshVar_injective (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_943 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy795 u S_cls E) ∉
      (((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv ∪
        ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv u))))).fv) :=
  by
  simpa only [nb095AlphaDummy795] using
    freshVar_not_mem
      (((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv ∪
        ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
      0

theorem nb095_fresh_944 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy796 u S_cls E) ∉
      (((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv ∪
        ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv u))))).fv) :=
  by
  simpa only [nb095AlphaDummy796] using
    freshVar_not_mem
      (((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv ∪
        ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
      1

theorem nb095_distinct_945 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy795 u S_cls E) ≠ (nb095AlphaDummy796 u S_cls E) := by
  simpa only [nb095AlphaDummy795, nb095AlphaDummy796] using
    (freshVar_injective (((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv ∪
        ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_946 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy039 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy034 D R S_cls E))
            (Class.cv (nb095AlphaDummy035 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy034 D R S_cls E))
            (Class.cv (nb095AlphaDummy035 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy039] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy034 D R S_cls E))
            (Class.cv (nb095AlphaDummy035 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy034 D R S_cls E))
            (Class.cv (nb095AlphaDummy035 D R S_cls E)))).fv)
      0

theorem nb095_fresh_947 (f : Var) :
    (nb095AlphaDummy040 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy037 f))
            (Class.cv (nb095AlphaDummy038 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy037 f))
            (Class.cv (nb095AlphaDummy038 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy040] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy037 f))
            (Class.cv (nb095AlphaDummy038 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy037 f))
            (Class.cv (nb095AlphaDummy038 f)))).fv)
      0

theorem nb095_fresh_948 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy075 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy070 D R S_cls E))
            (Class.cv (nb095AlphaDummy071 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy070 D R S_cls E))
            (Class.cv (nb095AlphaDummy071 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy075] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy070 D R S_cls E))
            (Class.cv (nb095AlphaDummy071 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy070 D R S_cls E))
            (Class.cv (nb095AlphaDummy071 D R S_cls E)))).fv)
      0

theorem nb095_fresh_949 (f : Var) :
    (nb095AlphaDummy076 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy073 f))
            (Class.cv (nb095AlphaDummy074 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy073 f))
            (Class.cv (nb095AlphaDummy074 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy076] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy073 f))
            (Class.cv (nb095AlphaDummy074 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy073 f))
            (Class.cv (nb095AlphaDummy074 f)))).fv)
      0

theorem nb095_fresh_950 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy117 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy112 D R S_cls E))
            (Class.cv (nb095AlphaDummy113 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy112 D R S_cls E))
            (Class.cv (nb095AlphaDummy113 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy117] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy112 D R S_cls E))
            (Class.cv (nb095AlphaDummy113 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy112 D R S_cls E))
            (Class.cv (nb095AlphaDummy113 D R S_cls E)))).fv)
      0

theorem nb095_fresh_951 (f : Var) :
    (nb095AlphaDummy118 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy115 f))
            (Class.cv (nb095AlphaDummy116 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy115 f))
            (Class.cv (nb095AlphaDummy116 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy118] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy115 f))
            (Class.cv (nb095AlphaDummy116 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy115 f))
            (Class.cv (nb095AlphaDummy116 f)))).fv)
      0

theorem nb095_fresh_952 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy153 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy148 D R S_cls E))
            (Class.cv (nb095AlphaDummy149 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy148 D R S_cls E))
            (Class.cv (nb095AlphaDummy149 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy153] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy148 D R S_cls E))
            (Class.cv (nb095AlphaDummy149 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy148 D R S_cls E))
            (Class.cv (nb095AlphaDummy149 D R S_cls E)))).fv)
      0

theorem nb095_fresh_953 (f : Var) :
    (nb095AlphaDummy154 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy151 f))
            (Class.cv (nb095AlphaDummy152 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy151 f))
            (Class.cv (nb095AlphaDummy152 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy154] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy151 f))
            (Class.cv (nb095AlphaDummy152 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy151 f))
            (Class.cv (nb095AlphaDummy152 f)))).fv)
      0

theorem nb095_fresh_954 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy189 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy184 D R S_cls E))
            (Class.cv (nb095AlphaDummy185 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy184 D R S_cls E))
            (Class.cv (nb095AlphaDummy185 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy189] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy184 D R S_cls E))
            (Class.cv (nb095AlphaDummy185 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy184 D R S_cls E))
            (Class.cv (nb095AlphaDummy185 D R S_cls E)))).fv)
      0

theorem nb095_fresh_955 (f : Var) :
    (nb095AlphaDummy190 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy187 f))
            (Class.cv (nb095AlphaDummy188 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy187 f))
            (Class.cv (nb095AlphaDummy188 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy190] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy187 f))
            (Class.cv (nb095AlphaDummy188 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy187 f))
            (Class.cv (nb095AlphaDummy188 f)))).fv)
      0

theorem nb095_fresh_956 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy229 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy224 D R S_cls E))
            (Class.cv (nb095AlphaDummy225 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy224 D R S_cls E))
            (Class.cv (nb095AlphaDummy225 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy229] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy224 D R S_cls E))
            (Class.cv (nb095AlphaDummy225 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy224 D R S_cls E))
            (Class.cv (nb095AlphaDummy225 D R S_cls E)))).fv)
      0

theorem nb095_fresh_957 (f : Var) :
    (nb095AlphaDummy230 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy227 f))
            (Class.cv (nb095AlphaDummy228 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy227 f))
            (Class.cv (nb095AlphaDummy228 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy230] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy227 f))
            (Class.cv (nb095AlphaDummy228 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy227 f))
            (Class.cv (nb095AlphaDummy228 f)))).fv)
      0

theorem nb095_fresh_958 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy275 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy270 D R S_cls E))
            (Class.cv (nb095AlphaDummy271 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy270 D R S_cls E))
            (Class.cv (nb095AlphaDummy271 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy275] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy270 D R S_cls E))
            (Class.cv (nb095AlphaDummy271 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy270 D R S_cls E))
            (Class.cv (nb095AlphaDummy271 D R S_cls E)))).fv)
      0

theorem nb095_fresh_959 (x : Var) (R : Class) :
    (nb095AlphaDummy276 x R) ∉
      (((synCnin (Class.cv (nb095AlphaDummy273 x R))
            (Class.cv (nb095AlphaDummy274 x R)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy273 x R))
            (Class.cv (nb095AlphaDummy274 x R)))).fv) :=
  by
  simpa only [nb095AlphaDummy276] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy273 x R))
            (Class.cv (nb095AlphaDummy274 x R)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy273 x R))
            (Class.cv (nb095AlphaDummy274 x R)))).fv)
      0

theorem nb095_fresh_960 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy319 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy314 D R S_cls E))
            (Class.cv (nb095AlphaDummy315 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy314 D R S_cls E))
            (Class.cv (nb095AlphaDummy315 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy319] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy314 D R S_cls E))
            (Class.cv (nb095AlphaDummy315 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy314 D R S_cls E))
            (Class.cv (nb095AlphaDummy315 D R S_cls E)))).fv)
      0

theorem nb095_fresh_961 (f : Var) :
    (nb095AlphaDummy320 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy317 f))
            (Class.cv (nb095AlphaDummy318 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy317 f))
            (Class.cv (nb095AlphaDummy318 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy320] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy317 f))
            (Class.cv (nb095AlphaDummy318 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy317 f))
            (Class.cv (nb095AlphaDummy318 f)))).fv)
      0

theorem nb095_fresh_962 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy365 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy360 D R S_cls E))
            (Class.cv (nb095AlphaDummy361 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy360 D R S_cls E))
            (Class.cv (nb095AlphaDummy361 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy365] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy360 D R S_cls E))
            (Class.cv (nb095AlphaDummy361 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy360 D R S_cls E))
            (Class.cv (nb095AlphaDummy361 D R S_cls E)))).fv)
      0

theorem nb095_fresh_963 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy366 u S_cls) ∉
      (((synCnin (Class.cv (nb095AlphaDummy363 u S_cls))
            (Class.cv (nb095AlphaDummy364 u S_cls)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy363 u S_cls))
            (Class.cv (nb095AlphaDummy364 u S_cls)))).fv) :=
  by
  simpa only [nb095AlphaDummy366] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy363 u S_cls))
            (Class.cv (nb095AlphaDummy364 u S_cls)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy363 u S_cls))
            (Class.cv (nb095AlphaDummy364 u S_cls)))).fv)
      0

theorem nb095_fresh_964 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy413 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy408 D R S_cls E))
            (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy408 D R S_cls E))
            (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy413] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy408 D R S_cls E))
            (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy408 D R S_cls E))
            (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv)
      0

theorem nb095_fresh_965 (f : Var) :
    (nb095AlphaDummy414 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy411 f))
            (Class.cv (nb095AlphaDummy412 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy411 f))
            (Class.cv (nb095AlphaDummy412 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy414] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy411 f))
            (Class.cv (nb095AlphaDummy412 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy411 f))
            (Class.cv (nb095AlphaDummy412 f)))).fv)
      0

theorem nb095_fresh_966 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy449 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy444 D R S_cls E))
            (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy444 D R S_cls E))
            (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy449] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy444 D R S_cls E))
            (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy444 D R S_cls E))
            (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv)
      0

theorem nb095_fresh_967 (f : Var) :
    (nb095AlphaDummy450 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy447 f))
            (Class.cv (nb095AlphaDummy448 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy447 f))
            (Class.cv (nb095AlphaDummy448 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy450] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy447 f))
            (Class.cv (nb095AlphaDummy448 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy447 f))
            (Class.cv (nb095AlphaDummy448 f)))).fv)
      0

theorem nb095_fresh_968 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy491 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy486 D R S_cls E))
            (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy486 D R S_cls E))
            (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy491] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy486 D R S_cls E))
            (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy486 D R S_cls E))
            (Class.cv (nb095AlphaDummy487 D R S_cls E)))).fv)
      0

theorem nb095_fresh_969 (f : Var) :
    (nb095AlphaDummy492 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy489 f))
            (Class.cv (nb095AlphaDummy490 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy489 f))
            (Class.cv (nb095AlphaDummy490 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy492] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy489 f))
            (Class.cv (nb095AlphaDummy490 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy489 f))
            (Class.cv (nb095AlphaDummy490 f)))).fv)
      0

theorem nb095_fresh_970 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy527 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy522 D R S_cls E))
            (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy522 D R S_cls E))
            (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy527] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy522 D R S_cls E))
            (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy522 D R S_cls E))
            (Class.cv (nb095AlphaDummy523 D R S_cls E)))).fv)
      0

theorem nb095_fresh_971 (f : Var) :
    (nb095AlphaDummy528 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy525 f))
            (Class.cv (nb095AlphaDummy526 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy525 f))
            (Class.cv (nb095AlphaDummy526 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy528] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy525 f))
            (Class.cv (nb095AlphaDummy526 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy525 f))
            (Class.cv (nb095AlphaDummy526 f)))).fv)
      0

theorem nb095_fresh_972 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy563 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy558 D R S_cls E))
            (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy558 D R S_cls E))
            (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy563] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy558 D R S_cls E))
            (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy558 D R S_cls E))
            (Class.cv (nb095AlphaDummy559 D R S_cls E)))).fv)
      0

theorem nb095_fresh_973 (f : Var) :
    (nb095AlphaDummy564 f) ∉
      (((synCnin (Class.cv (nb095AlphaDummy561 f))
            (Class.cv (nb095AlphaDummy562 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy561 f))
            (Class.cv (nb095AlphaDummy562 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy564] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy561 f))
            (Class.cv (nb095AlphaDummy562 f)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy561 f))
            (Class.cv (nb095AlphaDummy562 f)))).fv)
      0

theorem nb095_fresh_974 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy599 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy594 D R S_cls E))
            (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy594 D R S_cls E))
            (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy599] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy594 D R S_cls E))
            (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy594 D R S_cls E))
            (Class.cv (nb095AlphaDummy595 D R S_cls E)))).fv)
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
    (nb095AlphaDummy600 x u D R S_cls f E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy597 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy597 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy600] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy597 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy597 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy598 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_976 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy645 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy640 D R S_cls E))
            (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy640 D R S_cls E))
            (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy645] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy640 D R S_cls E))
            (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy640 D R S_cls E))
            (Class.cv (nb095AlphaDummy641 D R S_cls E)))).fv)
      0

theorem nb095_fresh_977 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy646 x D R) ∉
      (((synCnin (Class.cv (nb095AlphaDummy643 x D R))
            (Class.cv (nb095AlphaDummy644 x D R)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy643 x D R))
            (Class.cv (nb095AlphaDummy644 x D R)))).fv) :=
  by
  simpa only [nb095AlphaDummy646] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy643 x D R))
            (Class.cv (nb095AlphaDummy644 x D R)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy643 x D R))
            (Class.cv (nb095AlphaDummy644 x D R)))).fv)
      0

theorem nb095_fresh_978 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy697 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy692 D R S_cls E))
            (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy692 D R S_cls E))
            (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy697] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy692 D R S_cls E))
            (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy692 D R S_cls E))
            (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv)
      0

theorem nb095_fresh_979 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy698 x u D R S_cls f E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy695 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy695 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy698] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy695 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy695 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_980 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy727 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy722 D R S_cls E))
            (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy722 D R S_cls E))
            (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy727] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy722 D R S_cls E))
            (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy722 D R S_cls E))
            (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv)
      0

theorem nb095_fresh_981 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy728 x u D R S_cls f E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy725 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy725 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy728] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy725 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy725 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_982 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy767 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy762 D R S_cls E))
            (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy762 D R S_cls E))
            (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy767] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy762 D R S_cls E))
            (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy762 D R S_cls E))
            (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv)
      0

theorem nb095_fresh_983 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy768 x u D R S_cls f E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy765 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy765 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy768] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy765 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy765 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_984 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy819 D R S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy814 D R S_cls E))
            (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy814 D R S_cls E))
            (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy819] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy814 D R S_cls E))
            (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy814 D R S_cls E))
            (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv)
      0

theorem nb095_fresh_985 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy820 u S_cls E) ∉
      (((synCnin (Class.cv (nb095AlphaDummy817 u S_cls E))
            (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy817 u S_cls E))
            (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy820] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb095AlphaDummy817 u S_cls E))
            (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy817 u S_cls E))
            (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv)
      0

theorem nb095_fresh_986 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy007 D R S_cls E) ∉
      (((synCnin (synCcom (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))) (synCid))).fv) :=
  by
  simpa only [nb095AlphaDummy007] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))) (synCid))).fv)
      0

theorem nb095_fresh_987 (f : Var) :
    (nb095AlphaDummy008 f) ∉
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) :=
  by
  simpa only [nb095AlphaDummy008] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv)
      0

theorem nb095_fresh_988 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy381 D R S_cls E) ∉
      (((synCnin (synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
              (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))
            (synCid))).fv ∪ ((synCnin
            (synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
              (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))
            (synCid))).fv) :=
  by
  simpa only [nb095AlphaDummy381] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
              (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))
            (synCid))).fv ∪ ((synCnin
            (synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
              (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))
            (synCid))).fv)
      0

theorem nb095_fresh_989 (f : Var) :
    (nb095AlphaDummy382 f) ∉
      (((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv) :=
  by
  simpa only [nb095AlphaDummy382] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv)
      0

theorem nb095_fresh_990 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy291 D R S_cls E) ∉
      (((synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv ∪
        ((synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy291] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv ∪
        ((synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_991 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy292 u S_cls f E) ∉
      (((synCnin (synCrn (Class.cv f)) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))).fv ∪
        ((synCnin (synCrn (Class.cv f)) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))).fv) :=
  by
  simpa only [nb095AlphaDummy292] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv f)) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))).fv ∪
        ((synCnin (synCrn (Class.cv f)) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))).fv)
      0

theorem nb095_fresh_992 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy245 D R S_cls E) ∉
      (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCnin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy245] using
    freshVar_not_mem
      (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCnin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_993 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy246 x D R) ∉
      (((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCnin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv) :=
  by
  simpa only [nb095AlphaDummy246] using
    freshVar_not_mem
      (((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv)
      0

theorem nb095_fresh_994 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy335 D R S_cls E) ∉
      (((synCnin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCnin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy335] using
    freshVar_not_mem
      (((synCnin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCnin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_995 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy336 u S_cls E) ∉
      (((synCnin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv ∪
        ((synCnin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv u))))).fv) :=
  by
  simpa only [nb095AlphaDummy336] using
    freshVar_not_mem
      (((synCnin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv ∪
        ((synCnin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
      0

theorem nb095_fresh_996 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy615 D R S_cls E) ∉
      (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
        ((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy615] using
    freshVar_not_mem
      (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
        ((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv)
      0

theorem nb095_fresh_997 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy616 x D R) ∉
      (((synCnin R (synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv ∪
        ((synCnin R (synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv) :=
  by
  simpa only [nb095AlphaDummy616] using
    freshVar_not_mem
      (((synCnin R (synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv ∪
        ((synCnin R (synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv)
      0

theorem nb095_fresh_998 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy789 D R S_cls E) ∉
      (((synCnin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
        ((synCnin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy789] using
    freshVar_not_mem
      (((synCnin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
        ((synCnin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv)
      0

theorem nb095_fresh_999 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy790 u S_cls E) ∉
      (((synCnin S_cls (synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
              (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u))))))).fv ∪ ((synCnin S_cls (synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
              (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u))))))).fv) :=
  by
  simpa only [nb095AlphaDummy790] using
    freshVar_not_mem
      (((synCnin S_cls (synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
              (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u))))))).fv ∪ ((synCnin S_cls (synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
              (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u))))))).fv)
      0

theorem nb095_fresh_1000 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy053 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy053] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1001 (f : Var) :
    (nb095AlphaDummy054 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy022 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy022 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy054] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy022 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy022 f)))).fv)
      0

theorem nb095_fresh_1002 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy089 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy089] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1003 (f : Var) :
    (nb095AlphaDummy090 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy058 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy058 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy090] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy058 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy058 f)))).fv)
      0

theorem nb095_fresh_1004 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy131 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy131] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1005 (f : Var) :
    (nb095AlphaDummy132 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy100 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy100 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy132] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy100 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy100 f)))).fv)
      0

theorem nb095_fresh_1006 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy167 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy167] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1007 (f : Var) :
    (nb095AlphaDummy168 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy136 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy136 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy168] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy136 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy136 f)))).fv)
      0

theorem nb095_fresh_1008 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy203 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy203] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1009 (f : Var) :
    (nb095AlphaDummy204 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy172 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy172 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy204] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy172 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy172 f)))).fv)
      0

theorem nb095_fresh_1010 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy243 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy243] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1011 (f : Var) :
    (nb095AlphaDummy244 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy212 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy212 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy244] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy212 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy212 f)))).fv)
      0

theorem nb095_fresh_1012 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy289 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy289] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1013 (x : Var) (R : Class) :
    (nb095AlphaDummy290 x R) ∉
      (((synCphi (Class.cv (nb095AlphaDummy258 x R)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy258 x R)))).fv) :=
  by
  simpa only [nb095AlphaDummy290] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy258 x R)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy258 x R)))).fv)
      0

theorem nb095_fresh_1014 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy333 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy333] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1015 (f : Var) :
    (nb095AlphaDummy334 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy302 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy302 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy334] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy302 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy302 f)))).fv)
      0

theorem nb095_fresh_1016 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy379 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy379] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1017 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy380 u S_cls) ∉
      (((synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))).fv) :=
  by
  simpa only [nb095AlphaDummy380] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))).fv)
      0

theorem nb095_fresh_1018 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy427 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy427] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1019 (f : Var) :
    (nb095AlphaDummy428 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy396 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy396 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy428] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy396 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy396 f)))).fv)
      0

theorem nb095_fresh_1020 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy463 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy463] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1021 (f : Var) :
    (nb095AlphaDummy464 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy432 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy432 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy464] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy432 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy432 f)))).fv)
      0

theorem nb095_fresh_1022 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy505 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy505] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1023 (f : Var) :
    (nb095AlphaDummy506 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy474 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy474 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy506] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy474 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy474 f)))).fv)
      0

theorem nb095_fresh_1024 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy541 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy541] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1025 (f : Var) :
    (nb095AlphaDummy542 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy510 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy510 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy542] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy510 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy510 f)))).fv)
      0

theorem nb095_fresh_1026 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy577 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy577] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1027 (f : Var) :
    (nb095AlphaDummy578 f) ∉
      (((synCphi (Class.cv (nb095AlphaDummy546 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy546 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy578] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy546 f)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy546 f)))).fv)
      0

theorem nb095_fresh_1028 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy613 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy613] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1029 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy614 x u D R S_cls f E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy614] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1030 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy659 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy659] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1031 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy660 x D R) ∉
      (((synCphi (Class.cv (nb095AlphaDummy628 x D R)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy628 x D R)))).fv) :=
  by
  simpa only [nb095AlphaDummy660] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy628 x D R)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy628 x D R)))).fv)
      0

theorem nb095_fresh_1032 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy787 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy787] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1033 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy788 x u D R S_cls f E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy788] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1034 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy711 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy711] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1035 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy712 x u D R S_cls f E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy712] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1036 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy781 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy781] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1037 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy782 x u D R S_cls f E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy782] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1038 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy833 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy833] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1039 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy834 u S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy834] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))).fv)
      0

theorem nb095_fresh_1040 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy293 D R S_cls E) ∉
      (((synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy293] using
    freshVar_not_mem
      (((synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_1041 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy294 u S_cls f E) ∉
      (((synCrn (Class.cv f))).fv ∪ ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv u))))).fv) :=
  by
  simpa only [nb095AlphaDummy294] using
    freshVar_not_mem
      (((synCrn (Class.cv f))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
      0

theorem nb095_fresh_1042 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy247 D R S_cls E) ∉
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))).fv) :=
  by
  simpa only [nb095AlphaDummy247] using
    freshVar_not_mem
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))).fv)
      0

theorem nb095_fresh_1043 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy248 x D R) ∉
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))).fv) :=
  by
  simpa only [nb095AlphaDummy248] using
    freshVar_not_mem
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))).fv)
      0

theorem nb095_fresh_1044 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy337 D R S_cls E) ∉
      ((E).fv ∪ ((synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))).fv) :=
  by
  simpa only [nb095AlphaDummy337] using
    freshVar_not_mem
      ((E).fv ∪ ((synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))).fv)
      0

theorem nb095_fresh_1045 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy338 u S_cls E) ∉
      ((E).fv ∪ ((synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))).fv) :=
  by
  simpa only [nb095AlphaDummy338] using
    freshVar_not_mem
      ((E).fv ∪ ((synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))).fv)
      0

theorem nb095_fresh_1046 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy617 D R S_cls E) ∉
      ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy617] using
    freshVar_not_mem
      ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_1047 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy618 x D R) ∉
      ((R).fv ∪ ((synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))).fv) :=
  by
  simpa only [nb095AlphaDummy618] using
    freshVar_not_mem
      ((R).fv ∪ ((synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))).fv)
      0

theorem nb095_fresh_1048 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∉ ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) := by
  simpa only [nb095AlphaDummy000] using
    freshVar_not_mem ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 0

theorem nb095_fresh_1049 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy001 D R S_cls E) ∉ ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) := by
  simpa only [nb095AlphaDummy001] using
    freshVar_not_mem ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 1

theorem nb095_fresh_1050 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy002 D R S_cls E) ∉ ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) := by
  simpa only [nb095AlphaDummy002] using
    freshVar_not_mem ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 2

theorem nb095_distinct_1051 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy001 D R S_cls E) := by
  simpa only [nb095AlphaDummy000, nb095AlphaDummy001] using
    (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (i := 0) (j := 1) (by decide))

theorem nb095_distinct_1052 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy002 D R S_cls E) := by
  simpa only [nb095AlphaDummy000, nb095AlphaDummy002] using
    (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (i := 0) (j := 2) (by decide))

theorem nb095_distinct_1053 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy002 D R S_cls E) := by
  simpa only [nb095AlphaDummy001, nb095AlphaDummy002] using
    (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (i := 1) (j := 2) (by decide))

theorem nb095_fresh_1054 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy791 D R S_cls E) ∉
      ((S_cls).fv ∪ ((synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy791] using
    freshVar_not_mem
      ((S_cls).fv ∪ ((synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_1055 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy792 u S_cls E) ∉
      ((S_cls).fv ∪ ((synCxp (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
            (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u)))))).fv) :=
  by
  simpa only [nb095AlphaDummy792] using
    freshVar_not_mem
      ((S_cls).fv ∪ ((synCxp (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
            (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u)))))).fv)
      0

theorem nb095_fresh_1056 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy017 D R S_cls E) ∉
      (({(nb095AlphaDummy011 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy012 D R S_cls E)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy013 D R S_cls E) (synWa
              (synWbr (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
                (Class.cv (nb095AlphaDummy013 D R S_cls E)))
              (synWbr (Class.cv (nb095AlphaDummy013 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy012 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy017] using
    freshVar_not_mem
      (({(nb095AlphaDummy011 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy012 D R S_cls E)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy013 D R S_cls E) (synWa
              (synWbr (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
                (Class.cv (nb095AlphaDummy013 D R S_cls E)))
              (synWbr (Class.cv (nb095AlphaDummy013 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy012 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_1057 (f : Var) :
    (nb095AlphaDummy018 f) ∉
      (({(nb095AlphaDummy014 f)} : Finset Var) ∪ ({(nb095AlphaDummy015 f)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy016 f) (synWa
              (synWbr (Class.cv (nb095AlphaDummy014 f)) (synCcnv (Class.cv f))
                (Class.cv (nb095AlphaDummy016 f)))
              (synWbr (Class.cv (nb095AlphaDummy016 f)) (Class.cv f)
                (Class.cv (nb095AlphaDummy015 f)))))).fv) :=
  by
  simpa only [nb095AlphaDummy018] using
    freshVar_not_mem
      (({(nb095AlphaDummy014 f)} : Finset Var) ∪ ({(nb095AlphaDummy015 f)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy016 f) (synWa
              (synWbr (Class.cv (nb095AlphaDummy014 f)) (synCcnv (Class.cv f))
                (Class.cv (nb095AlphaDummy016 f)))
              (synWbr (Class.cv (nb095AlphaDummy016 f)) (Class.cv f)
                (Class.cv (nb095AlphaDummy015 f)))))).fv)
      0

theorem nb095_fresh_1058 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy095 D R S_cls E) ∉
      (({(nb095AlphaDummy091 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy092 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy092 D R S_cls E))
            (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy091 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy095] using
    freshVar_not_mem
      (({(nb095AlphaDummy091 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy092 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy092 D R S_cls E))
            (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy091 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1059 (f : Var) :
    (nb095AlphaDummy096 f) ∉
      (({(nb095AlphaDummy093 f)} : Finset Var) ∪ ({(nb095AlphaDummy094 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy094 f)) (Class.cv f)
            (Class.cv (nb095AlphaDummy093 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy096] using
    freshVar_not_mem
      (({(nb095AlphaDummy093 f)} : Finset Var) ∪ ({(nb095AlphaDummy094 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy094 f)) (Class.cv f)
            (Class.cv (nb095AlphaDummy093 f)))).fv)
      0

theorem nb095_fresh_1060 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy391 D R S_cls E) ∉
      (({(nb095AlphaDummy385 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy386 D R S_cls E)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy387 D R S_cls E) (synWa
              (synWbr (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))
                (Class.cv (nb095AlphaDummy387 D R S_cls E)))
              (synWbr (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
                (Class.cv (nb095AlphaDummy386 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy391] using
    freshVar_not_mem
      (({(nb095AlphaDummy385 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy386 D R S_cls E)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy387 D R S_cls E) (synWa
              (synWbr (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))
                (Class.cv (nb095AlphaDummy387 D R S_cls E)))
              (synWbr (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
                (Class.cv (nb095AlphaDummy386 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_1061 (f : Var) :
    (nb095AlphaDummy392 f) ∉
      (({(nb095AlphaDummy388 f)} : Finset Var) ∪ ({(nb095AlphaDummy389 f)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy390 f) (synWa
              (synWbr (Class.cv (nb095AlphaDummy388 f))
                (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb095AlphaDummy390 f)))
              (synWbr (Class.cv (nb095AlphaDummy390 f)) (synCcnv (Class.cv f))
                (Class.cv (nb095AlphaDummy389 f)))))).fv) :=
  by
  simpa only [nb095AlphaDummy392] using
    freshVar_not_mem
      (({(nb095AlphaDummy388 f)} : Finset Var) ∪ ({(nb095AlphaDummy389 f)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy390 f) (synWa
              (synWbr (Class.cv (nb095AlphaDummy388 f))
                (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb095AlphaDummy390 f)))
              (synWbr (Class.cv (nb095AlphaDummy390 f)) (synCcnv (Class.cv f))
                (Class.cv (nb095AlphaDummy389 f)))))).fv)
      0

theorem nb095_fresh_1062 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy469 D R S_cls E) ∉
      (({(nb095AlphaDummy465 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy466 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy466 D R S_cls E))
            (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
            (Class.cv (nb095AlphaDummy465 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy469] using
    freshVar_not_mem
      (({(nb095AlphaDummy465 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy466 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy466 D R S_cls E))
            (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
            (Class.cv (nb095AlphaDummy465 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1063 (f : Var) :
    (nb095AlphaDummy470 f) ∉
      (({(nb095AlphaDummy467 f)} : Finset Var) ∪ ({(nb095AlphaDummy468 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy468 f)) (synCcnv (Class.cv f))
            (Class.cv (nb095AlphaDummy467 f)))).fv) :=
  by
  simpa only [nb095AlphaDummy470] using
    freshVar_not_mem
      (({(nb095AlphaDummy467 f)} : Finset Var) ∪ ({(nb095AlphaDummy468 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy468 f)) (synCcnv (Class.cv f))
            (Class.cv (nb095AlphaDummy467 f)))).fv)
      0

theorem nb095_fresh_1064 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy623 D R S_cls E) ∉
      (({(nb095AlphaDummy619 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy620 D R S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy619 D R S_cls E)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095AlphaDummy620 D R S_cls E)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy623] using
    freshVar_not_mem
      (({(nb095AlphaDummy619 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy620 D R S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy619 D R S_cls E)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095AlphaDummy620 D R S_cls E)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv)
      0

theorem nb095_fresh_1065 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy624 x D R) ∉
      (({(nb095AlphaDummy621 x D R)} : Finset Var) ∪
          ({(nb095AlphaDummy622 x D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy621 x D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))
            (Wff.classMem (Class.cv (nb095AlphaDummy622 x D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv) :=
  by
  simpa only [nb095AlphaDummy624] using
    freshVar_not_mem
      (({(nb095AlphaDummy621 x D R)} : Finset Var) ∪
          ({(nb095AlphaDummy622 x D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy621 x D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))
            (Wff.classMem (Class.cv (nb095AlphaDummy622 x D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv)
      0

theorem nb095_fresh_1066 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy671 D R S_cls E) ∉
      (({(nb095AlphaDummy669 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
            (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy669 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy671] using
    freshVar_not_mem
      (({(nb095AlphaDummy669 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
            (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy669 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1067 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy672 x u D R S_cls f E) ∉
      (({(nb095AlphaDummy670 x u D R S_cls f E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095AlphaDummy670 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy672] using
    freshVar_not_mem
      (({(nb095AlphaDummy670 x u D R S_cls f E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095AlphaDummy670 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1068 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy741 D R S_cls E) ∉
      (({(nb095AlphaDummy739 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
            (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy739 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy741] using
    freshVar_not_mem
      (({(nb095AlphaDummy739 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
            (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy739 D R S_cls E)))).fv)
      0

theorem nb095_fresh_1069 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy742 x u D R S_cls f E) ∉
      (({(nb095AlphaDummy740 x u D R S_cls f E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095AlphaDummy740 x u D R S_cls f E)))).fv) :=
  by
  simpa only [nb095AlphaDummy742] using
    freshVar_not_mem
      (({(nb095AlphaDummy740 x u D R S_cls f E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095AlphaDummy740 x u D R S_cls f E)))).fv)
      0

theorem nb095_fresh_1070 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy797 D R S_cls E) ∉
      (({(nb095AlphaDummy793 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy794 D R S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy793 D R S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095AlphaDummy794 D R S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy797] using
    freshVar_not_mem
      (({(nb095AlphaDummy793 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy794 D R S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy793 D R S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095AlphaDummy794 D R S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv)
      0

theorem nb095_fresh_1071 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy798 u S_cls E) ∉
      (({(nb095AlphaDummy795 u S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy796 u S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy795 u S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))
            (Wff.classMem (Class.cv (nb095AlphaDummy796 u S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u))))))).fv) :=
  by
  simpa only [nb095AlphaDummy798] using
    freshVar_not_mem
      (({(nb095AlphaDummy795 u S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy796 u S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy795 u S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))
            (Wff.classMem (Class.cv (nb095AlphaDummy796 u S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))))).fv)
      0

theorem nb095_support_mem_0000 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy011 D R S_cls E) ∈
      (({(nb095AlphaDummy011 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy012 D R S_cls E)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy013 D R S_cls E) (synWa
              (synWbr (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
                (Class.cv (nb095AlphaDummy013 D R S_cls E)))
              (synWbr (Class.cv (nb095AlphaDummy013 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy012 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0001 (f : Var) :
    (nb095AlphaDummy014 f) ∈
      (({(nb095AlphaDummy014 f)} : Finset Var) ∪ ({(nb095AlphaDummy015 f)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy016 f) (synWa
              (synWbr (Class.cv (nb095AlphaDummy014 f)) (synCcnv (Class.cv f))
                (Class.cv (nb095AlphaDummy016 f)))
              (synWbr (Class.cv (nb095AlphaDummy016 f)) (Class.cv f)
                (Class.cv (nb095AlphaDummy015 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0002 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy012 D R S_cls E) ∈
      (({(nb095AlphaDummy011 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy012 D R S_cls E)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy013 D R S_cls E) (synWa
              (synWbr (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
                (Class.cv (nb095AlphaDummy013 D R S_cls E)))
              (synWbr (Class.cv (nb095AlphaDummy013 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy012 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0003 (f : Var) :
    (nb095AlphaDummy015 f) ∈
      (({(nb095AlphaDummy014 f)} : Finset Var) ∪ ({(nb095AlphaDummy015 f)} : Finset Var) ∪
        ((synWex (nb095AlphaDummy016 f) (synWa
              (synWbr (Class.cv (nb095AlphaDummy014 f)) (synCcnv (Class.cv f))
                (Class.cv (nb095AlphaDummy016 f)))
              (synWbr (Class.cv (nb095AlphaDummy016 f)) (Class.cv f)
                (Class.cv (nb095AlphaDummy015 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0004 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy011 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0005 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy011 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy019 D R S_cls E)
              (synWrex (nb095AlphaDummy020 D R S_cls E)
                (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy019 D R S_cls E)
              (synWrex (nb095AlphaDummy020 D R S_cls E)
                (Class.cv (nb095AlphaDummy012 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy011 D R S_cls E) ≠ (nb095AlphaDummy019 D R S_cls E) from (by
          unfold nb095AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy011 D R S_cls E) ≠ (nb095AlphaDummy020 D R S_cls E) from (by
            unfold nb095AlphaDummy020;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0006 (f : Var) :
    (nb095AlphaDummy014 f) ∈
      (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv (nb095AlphaDummy015 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
