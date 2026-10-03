/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C053C001Part001. -/


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

@[expose]
noncomputable def nb053_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb053_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb053_alpha_dummy_002 : Var :=
  (freshVar
    (({(nb053_alpha_dummy_000)} : Finset Var) ∪ ({(nb053_alpha_dummy_001)} : Finset Var) ∪
      ((Wff.classEq
          (syn_cin (Class.cv (nb053_alpha_dummy_000)) (Class.cv (nb053_alpha_dummy_001)))
          (syn_c0))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_003 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ((Wff.classEq (syn_cin (Class.cv x) (Class.cv y)) (syn_c0))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_004 : Var :=
  (freshVar
    (((Class.cv (nb053_alpha_dummy_000))).fv ∪ ((Class.cv (nb053_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_005 : Var :=
  (freshVar
    (((Class.cv (nb053_alpha_dummy_000))).fv ∪ ((Class.cv (nb053_alpha_dummy_001))).fv) 1)

@[expose]
noncomputable def nb053_alpha_dummy_006 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_007 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb053_alpha_dummy_008 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cphi (Class.cv (nb053_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_009 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_010 : Var :=
  (freshVar (((Class.cab (nb053_alpha_dummy_004)
          (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
              (syn_cphi (Class.cv (nb053_alpha_dummy_005))))))).fv ∪
      ((Class.cab (nb053_alpha_dummy_004)
          (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
              (syn_cphi (Class.cv (nb053_alpha_dummy_005))))))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_011 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb053_alpha_dummy_006 x y)
          (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
              (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))))).fv ∪
      ((Class.cab (nb053_alpha_dummy_006 x y) (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
              (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_012 : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_005))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_013 : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_005))).fv) 1)

@[expose]
noncomputable def nb053_alpha_dummy_014 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_007 x y))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_015 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_007 x y))).fv) 1)

@[expose]
noncomputable def nb053_alpha_dummy_016 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb053_alpha_dummy_012)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb053_alpha_dummy_012)) (syn_c1c))).fv ∪
      ((Class.cv (nb053_alpha_dummy_012))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_017 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb053_alpha_dummy_014 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb053_alpha_dummy_014 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb053_alpha_dummy_014 x y))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_018 : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_019 : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb053_alpha_dummy_020 : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb053_alpha_dummy_021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_022 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb053_alpha_dummy_023 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb053_alpha_dummy_024 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb053_alpha_dummy_019))
          (Class.cv (nb053_alpha_dummy_020)))).fv ∪
      ((syn_cnin (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020)))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_025 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb053_alpha_dummy_022 x y))
          (Class.cv (nb053_alpha_dummy_023 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb053_alpha_dummy_022 x y))
          (Class.cv (nb053_alpha_dummy_023 x y)))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_026 : Var :=
  (freshVar
    (((Class.cv (nb053_alpha_dummy_019))).fv ∪ ((Class.cv (nb053_alpha_dummy_020))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_027 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_022 x y))).fv ∪
      ((Class.cv (nb053_alpha_dummy_023 x y))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_028 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb053_alpha_dummy_019)))).fv ∪
      ((syn_ccompl (Class.cv (nb053_alpha_dummy_020)))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_029 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb053_alpha_dummy_022 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb053_alpha_dummy_023 x y)))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_030 : Var :=
  (freshVar
    (((Class.cv (nb053_alpha_dummy_019))).fv ∪ ((Class.cv (nb053_alpha_dummy_019))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_022 x y))).fv ∪
      ((Class.cv (nb053_alpha_dummy_022 x y))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_032 : Var :=
  (freshVar
    (((Class.cv (nb053_alpha_dummy_020))).fv ∪ ((Class.cv (nb053_alpha_dummy_020))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053_alpha_dummy_023 x y))).fv ∪
      ((Class.cv (nb053_alpha_dummy_023 x y))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_034 : Var :=
  (freshVar (((Class.cab (nb053_alpha_dummy_004)
          (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
              (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb053_alpha_dummy_004)
          (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
              (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_035 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb053_alpha_dummy_006 x y)
          (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
              (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb053_alpha_dummy_006 x y)
          (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
              (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_036 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb053_alpha_dummy_005))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_037 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_038 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb053_alpha_dummy_005)))).fv ∪
      ((syn_cphi (Class.cv (nb053_alpha_dummy_005)))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_039 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_040 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb053_alpha_dummy_000))
          (Class.cv (nb053_alpha_dummy_001)))).fv ∪
      ((syn_cnin (Class.cv (nb053_alpha_dummy_000)) (Class.cv (nb053_alpha_dummy_001)))).fv) 0)

@[expose]
noncomputable def nb053_alpha_dummy_041 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪
      ((syn_cnin (Class.cv x) (Class.cv y))).fv) 0)

theorem nb053_fresh_000 :
    (nb053_alpha_dummy_010) ∉
      (((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cphi (Class.cv (nb053_alpha_dummy_005))))))).fv ∪
        ((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cphi (Class.cv (nb053_alpha_dummy_005))))))).fv) :=
  by
  simpa only [nb053_alpha_dummy_010] using
    freshVar_not_mem
      (((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cphi (Class.cv (nb053_alpha_dummy_005))))))).fv ∪
        ((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cphi (Class.cv (nb053_alpha_dummy_005))))))).fv)
      0

theorem nb053_fresh_001 :
    (nb053_alpha_dummy_034) ∉
      (((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb053_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb053_fresh_002 (x : Var) (y : Var) :
    (nb053_alpha_dummy_011 x y) ∉
      (((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))))).fv ∪
        ((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))))).fv) :=
  by
  simpa only [nb053_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))))).fv ∪
        ((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))))).fv)
      0

theorem nb053_fresh_003 (x : Var) (y : Var) :
    (nb053_alpha_dummy_035 x y) ∉
      (((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb053_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb053_fresh_004 :
    (nb053_alpha_dummy_004) ∉
      (((Class.cv (nb053_alpha_dummy_000))).fv ∪ ((Class.cv (nb053_alpha_dummy_001))).fv) :=
  by
  simpa only [nb053_alpha_dummy_004] using
    freshVar_not_mem
      (((Class.cv (nb053_alpha_dummy_000))).fv ∪ ((Class.cv (nb053_alpha_dummy_001))).fv)
      0

theorem nb053_fresh_005 :
    (nb053_alpha_dummy_005) ∉
      (((Class.cv (nb053_alpha_dummy_000))).fv ∪ ((Class.cv (nb053_alpha_dummy_001))).fv) :=
  by
  simpa only [nb053_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb053_alpha_dummy_000))).fv ∪ ((Class.cv (nb053_alpha_dummy_001))).fv)
      1

theorem nb053_distinct_006 : (nb053_alpha_dummy_004) ≠ (nb053_alpha_dummy_005) := by
  simpa only [nb053_alpha_dummy_004, nb053_alpha_dummy_005] using
    (freshVar_injective
      (((Class.cv (nb053_alpha_dummy_000))).fv ∪ ((Class.cv (nb053_alpha_dummy_001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb053_fresh_007 :
    (nb053_alpha_dummy_012) ∉ (((Class.cv (nb053_alpha_dummy_005))).fv) := by
  simpa only [nb053_alpha_dummy_012] using
    freshVar_not_mem (((Class.cv (nb053_alpha_dummy_005))).fv) 0

theorem nb053_fresh_008 :
    (nb053_alpha_dummy_013) ∉ (((Class.cv (nb053_alpha_dummy_005))).fv) := by
  simpa only [nb053_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb053_alpha_dummy_005))).fv) 1

theorem nb053_distinct_009 : (nb053_alpha_dummy_012) ≠ (nb053_alpha_dummy_013) := by
  simpa only [nb053_alpha_dummy_012, nb053_alpha_dummy_013] using
    (freshVar_injective (((Class.cv (nb053_alpha_dummy_005))).fv) (i := 0) (j := 1) (by decide))

theorem nb053_fresh_010 (x : Var) (y : Var) :
    (nb053_alpha_dummy_014 x y) ∉ (((Class.cv (nb053_alpha_dummy_007 x y))).fv) := by
  simpa only [nb053_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb053_alpha_dummy_007 x y))).fv) 0

theorem nb053_fresh_011 (x : Var) (y : Var) :
    (nb053_alpha_dummy_015 x y) ∉ (((Class.cv (nb053_alpha_dummy_007 x y))).fv) := by
  simpa only [nb053_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb053_alpha_dummy_007 x y))).fv) 1

theorem nb053_distinct_012 (x : Var) (y : Var) :
    (nb053_alpha_dummy_014 x y) ≠ (nb053_alpha_dummy_015 x y) := by
  simpa only [nb053_alpha_dummy_014, nb053_alpha_dummy_015] using
    (freshVar_injective (((Class.cv (nb053_alpha_dummy_007 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb053_fresh_013 :
    (nb053_alpha_dummy_018) ∉
      (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb053_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 0

theorem nb053_fresh_014 :
    (nb053_alpha_dummy_019) ∉
      (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb053_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 1

theorem nb053_fresh_015 :
    (nb053_alpha_dummy_020) ∉
      (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb053_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 2

theorem nb053_distinct_016 : (nb053_alpha_dummy_018) ≠ (nb053_alpha_dummy_019) := by
  simpa only [nb053_alpha_dummy_018, nb053_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb053_distinct_017 : (nb053_alpha_dummy_018) ≠ (nb053_alpha_dummy_020) := by
  simpa only [nb053_alpha_dummy_018, nb053_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb053_distinct_018 : (nb053_alpha_dummy_019) ≠ (nb053_alpha_dummy_020) := by
  simpa only [nb053_alpha_dummy_019, nb053_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb053_fresh_019 (x : Var) (y : Var) :
    (nb053_alpha_dummy_021 x y) ∉
      (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb053_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb053_fresh_020 (x : Var) (y : Var) :
    (nb053_alpha_dummy_022 x y) ∉
      (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb053_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb053_fresh_021 (x : Var) (y : Var) :
    (nb053_alpha_dummy_023 x y) ∉
      (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb053_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb053_distinct_022 (x : Var) (y : Var) :
    (nb053_alpha_dummy_021 x y) ≠ (nb053_alpha_dummy_022 x y) := by
  simpa only [nb053_alpha_dummy_021, nb053_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb053_distinct_023 (x : Var) (y : Var) :
    (nb053_alpha_dummy_021 x y) ≠ (nb053_alpha_dummy_023 x y) := by
  simpa only [nb053_alpha_dummy_021, nb053_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb053_distinct_024 (x : Var) (y : Var) :
    (nb053_alpha_dummy_022 x y) ≠ (nb053_alpha_dummy_023 x y) := by
  simpa only [nb053_alpha_dummy_022, nb053_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb053_fresh_025 :
    (nb053_alpha_dummy_030) ∉
      (((Class.cv (nb053_alpha_dummy_019))).fv ∪ ((Class.cv (nb053_alpha_dummy_019))).fv) :=
  by
  simpa only [nb053_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb053_alpha_dummy_019))).fv ∪ ((Class.cv (nb053_alpha_dummy_019))).fv)
      0

theorem nb053_fresh_026 :
    (nb053_alpha_dummy_026) ∉
      (((Class.cv (nb053_alpha_dummy_019))).fv ∪ ((Class.cv (nb053_alpha_dummy_020))).fv) :=
  by
  simpa only [nb053_alpha_dummy_026] using
    freshVar_not_mem
      (((Class.cv (nb053_alpha_dummy_019))).fv ∪ ((Class.cv (nb053_alpha_dummy_020))).fv)
      0

theorem nb053_fresh_027 :
    (nb053_alpha_dummy_032) ∉
      (((Class.cv (nb053_alpha_dummy_020))).fv ∪ ((Class.cv (nb053_alpha_dummy_020))).fv) :=
  by
  simpa only [nb053_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb053_alpha_dummy_020))).fv ∪ ((Class.cv (nb053_alpha_dummy_020))).fv)
      0

theorem nb053_fresh_028 (x : Var) (y : Var) :
    (nb053_alpha_dummy_031 x y) ∉
      (((Class.cv (nb053_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb053_alpha_dummy_022 x y))).fv) :=
  by
  simpa only [nb053_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb053_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb053_alpha_dummy_022 x y))).fv)
      0

theorem nb053_fresh_029 (x : Var) (y : Var) :
    (nb053_alpha_dummy_027 x y) ∉
      (((Class.cv (nb053_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb053_alpha_dummy_023 x y))).fv) :=
  by
  simpa only [nb053_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb053_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb053_alpha_dummy_023 x y))).fv)
      0

theorem nb053_fresh_030 (x : Var) (y : Var) :
    (nb053_alpha_dummy_033 x y) ∉
      (((Class.cv (nb053_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb053_alpha_dummy_023 x y))).fv) :=
  by
  simpa only [nb053_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb053_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb053_alpha_dummy_023 x y))).fv)
      0

theorem nb053_fresh_031 (x : Var) (y : Var) :
    (nb053_alpha_dummy_006 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb053_alpha_dummy_006] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb053_fresh_032 (x : Var) (y : Var) :
    (nb053_alpha_dummy_007 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb053_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb053_distinct_033 (x : Var) (y : Var) :
    (nb053_alpha_dummy_006 x y) ≠ (nb053_alpha_dummy_007 x y) := by
  simpa only [nb053_alpha_dummy_006, nb053_alpha_dummy_007] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb053_fresh_034 :
    (nb053_alpha_dummy_016) ∉
      (((Wff.classMem (Class.cv (nb053_alpha_dummy_012)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb053_alpha_dummy_012)) (syn_c1c))).fv ∪
        ((Class.cv (nb053_alpha_dummy_012))).fv) :=
  by
  simpa only [nb053_alpha_dummy_016] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb053_alpha_dummy_012)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb053_alpha_dummy_012)) (syn_c1c))).fv ∪
        ((Class.cv (nb053_alpha_dummy_012))).fv)
      0

theorem nb053_fresh_035 (x : Var) (y : Var) :
    (nb053_alpha_dummy_017 x y) ∉
      (((Wff.classMem (Class.cv (nb053_alpha_dummy_014 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb053_alpha_dummy_014 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb053_alpha_dummy_014 x y))).fv) :=
  by
  simpa only [nb053_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb053_alpha_dummy_014 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb053_alpha_dummy_014 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb053_alpha_dummy_014 x y))).fv)
      0

theorem nb053_fresh_036 :
    (nb053_alpha_dummy_008) ∉
      (((syn_ccompl (Class.cab (nb053_alpha_dummy_004)
              (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                  (syn_cphi (Class.cv (nb053_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb053_alpha_dummy_004)
              (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                  (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb053_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb053_alpha_dummy_004)
              (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                  (syn_cphi (Class.cv (nb053_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb053_alpha_dummy_004)
              (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                  (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb053_fresh_037 (x : Var) (y : Var) :
    (nb053_alpha_dummy_009 x y) ∉
      (((syn_ccompl (Class.cab (nb053_alpha_dummy_006 x y)
              (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                  (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb053_alpha_dummy_006 x y)
              (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                  (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb053_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb053_alpha_dummy_006 x y)
              (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                  (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb053_alpha_dummy_006 x y)
              (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                  (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb053_fresh_038 :
    (nb053_alpha_dummy_028) ∉
      (((syn_ccompl (Class.cv (nb053_alpha_dummy_019)))).fv ∪
        ((syn_ccompl (Class.cv (nb053_alpha_dummy_020)))).fv) :=
  by
  simpa only [nb053_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb053_alpha_dummy_019)))).fv ∪
        ((syn_ccompl (Class.cv (nb053_alpha_dummy_020)))).fv)
      0

theorem nb053_fresh_039 (x : Var) (y : Var) :
    (nb053_alpha_dummy_029 x y) ∉
      (((syn_ccompl (Class.cv (nb053_alpha_dummy_022 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb053_alpha_dummy_023 x y)))).fv) :=
  by
  simpa only [nb053_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb053_alpha_dummy_022 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb053_alpha_dummy_023 x y)))).fv)
      0

theorem nb053_fresh_040 :
    (nb053_alpha_dummy_036) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb053_alpha_dummy_005))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb053_alpha_dummy_036] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb053_alpha_dummy_005))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb053_fresh_041 (x : Var) (y : Var) :
    (nb053_alpha_dummy_037 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb053_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb053_fresh_042 :
    (nb053_alpha_dummy_040) ∉
      (((syn_cnin (Class.cv (nb053_alpha_dummy_000)) (Class.cv (nb053_alpha_dummy_001)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_000))
            (Class.cv (nb053_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb053_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb053_alpha_dummy_000)) (Class.cv (nb053_alpha_dummy_001)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_000)) (Class.cv (nb053_alpha_dummy_001)))).fv)
      0

theorem nb053_fresh_043 :
    (nb053_alpha_dummy_024) ∉
      (((syn_cnin (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_019))
            (Class.cv (nb053_alpha_dummy_020)))).fv) :=
  by
  simpa only [nb053_alpha_dummy_024] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020)))).fv)
      0

theorem nb053_fresh_044 (x : Var) (y : Var) :
    (nb053_alpha_dummy_025 x y) ∉
      (((syn_cnin (Class.cv (nb053_alpha_dummy_022 x y))
            (Class.cv (nb053_alpha_dummy_023 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_022 x y))
            (Class.cv (nb053_alpha_dummy_023 x y)))).fv) :=
  by
  simpa only [nb053_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb053_alpha_dummy_022 x y))
            (Class.cv (nb053_alpha_dummy_023 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_022 x y))
            (Class.cv (nb053_alpha_dummy_023 x y)))).fv)
      0

theorem nb053_fresh_045 (x : Var) (y : Var) :
    (nb053_alpha_dummy_041 x y) ∉
      (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪ ((syn_cnin (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb053_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪ ((syn_cnin (Class.cv x) (Class.cv y))).fv)
      0

theorem nb053_fresh_046 :
    (nb053_alpha_dummy_038) ∉
      (((syn_cphi (Class.cv (nb053_alpha_dummy_005)))).fv ∪
        ((syn_cphi (Class.cv (nb053_alpha_dummy_005)))).fv) :=
  by
  simpa only [nb053_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb053_alpha_dummy_005)))).fv ∪
        ((syn_cphi (Class.cv (nb053_alpha_dummy_005)))).fv)
      0

theorem nb053_fresh_047 (x : Var) (y : Var) :
    (nb053_alpha_dummy_039 x y) ∉
      (((syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))).fv) :=
  by
  simpa only [nb053_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))).fv)
      0

theorem nb053_fresh_048 :
    (nb053_alpha_dummy_002) ∉
      (({(nb053_alpha_dummy_000)} : Finset Var) ∪ ({(nb053_alpha_dummy_001)} : Finset Var) ∪
        ((Wff.classEq (syn_cin (Class.cv (nb053_alpha_dummy_000))
              (Class.cv (nb053_alpha_dummy_001))) (syn_c0))).fv) :=
  by
  simpa only [nb053_alpha_dummy_002] using
    freshVar_not_mem
      (({(nb053_alpha_dummy_000)} : Finset Var) ∪ ({(nb053_alpha_dummy_001)} : Finset Var) ∪
        ((Wff.classEq (syn_cin (Class.cv (nb053_alpha_dummy_000))
              (Class.cv (nb053_alpha_dummy_001))) (syn_c0))).fv)
      0

theorem nb053_fresh_049 (x : Var) (y : Var) :
    (nb053_alpha_dummy_003 x y) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classEq (syn_cin (Class.cv x) (Class.cv y)) (syn_c0))).fv) :=
  by
  simpa only [nb053_alpha_dummy_003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classEq (syn_cin (Class.cv x) (Class.cv y)) (syn_c0))).fv)
      0

theorem nb053_fresh_050 : (nb053_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb053_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb053_fresh_051 : (nb053_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb053_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb053_distinct_052 : (nb053_alpha_dummy_000) ≠ (nb053_alpha_dummy_001) := by
  simpa only [nb053_alpha_dummy_000, nb053_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb053_support_mem_0000 :
    (nb053_alpha_dummy_000) ∈
      (({(nb053_alpha_dummy_000)} : Finset Var) ∪ ({(nb053_alpha_dummy_001)} : Finset Var) ∪
        ((Wff.classEq (syn_cin (Class.cv (nb053_alpha_dummy_000))
              (Class.cv (nb053_alpha_dummy_001))) (syn_c0))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0001 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classEq (syn_cin (Class.cv x) (Class.cv y)) (syn_c0))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0002 :
    (nb053_alpha_dummy_001) ∈
      (({(nb053_alpha_dummy_000)} : Finset Var) ∪ ({(nb053_alpha_dummy_001)} : Finset Var) ∪
        ((Wff.classEq (syn_cin (Class.cv (nb053_alpha_dummy_000))
              (Class.cv (nb053_alpha_dummy_001))) (syn_c0))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0003 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classEq (syn_cin (Class.cv x) (Class.cv y)) (syn_c0))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0004 :
    (nb053_alpha_dummy_000) ∈
      (((Class.cv (nb053_alpha_dummy_000))).fv ∪ ((Class.cv (nb053_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0005 :
    (nb053_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb053_alpha_dummy_004)
              (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                  (syn_cphi (Class.cv (nb053_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb053_alpha_dummy_004)
              (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                  (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0006 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb053_alpha_dummy_006 x y)
              (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                  (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb053_alpha_dummy_006 x y)
              (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                  (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0008 :
    (nb053_alpha_dummy_000) ∈
      (((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cphi (Class.cv (nb053_alpha_dummy_005))))))).fv ∪
        ((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cphi (Class.cv (nb053_alpha_dummy_005))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0009 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))))).fv ∪
        ((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0010 :
    (nb053_alpha_dummy_005) ∈ (((Class.cv (nb053_alpha_dummy_005))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0011 (x : Var) (y : Var) :
    (nb053_alpha_dummy_007 x y) ∈ (((Class.cv (nb053_alpha_dummy_007 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0012 :
    (nb053_alpha_dummy_012) ∈
      (((Wff.classMem (Class.cv (nb053_alpha_dummy_012)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb053_alpha_dummy_012)) (syn_c1c))).fv ∪
        ((Class.cv (nb053_alpha_dummy_012))).fv) :=
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

theorem nb053_support_mem_0013 (x : Var) (y : Var) :
    (nb053_alpha_dummy_014 x y) ∈
      (((Wff.classMem (Class.cv (nb053_alpha_dummy_014 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb053_alpha_dummy_014 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb053_alpha_dummy_014 x y))).fv) :=
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

theorem nb053_support_mem_0014 :
    (nb053_alpha_dummy_012) ∈
      (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0015 (x : Var) (y : Var) :
    (nb053_alpha_dummy_014 x y) ∈
      (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0016 :
    (nb053_alpha_dummy_019) ∈
      (((syn_cnin (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_019))
            (Class.cv (nb053_alpha_dummy_020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0017 (x : Var) (y : Var) :
    (nb053_alpha_dummy_022 x y) ∈
      (((syn_cnin (Class.cv (nb053_alpha_dummy_022 x y))
            (Class.cv (nb053_alpha_dummy_023 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_022 x y))
            (Class.cv (nb053_alpha_dummy_023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0018 :
    (nb053_alpha_dummy_019) ∈
      (((Class.cv (nb053_alpha_dummy_019))).fv ∪ ((Class.cv (nb053_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0019 (x : Var) (y : Var) :
    (nb053_alpha_dummy_022 x y) ∈
      (((Class.cv (nb053_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb053_alpha_dummy_023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0020 :
    (nb053_alpha_dummy_020) ∈
      (((syn_cnin (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_019))
            (Class.cv (nb053_alpha_dummy_020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0021 (x : Var) (y : Var) :
    (nb053_alpha_dummy_023 x y) ∈
      (((syn_cnin (Class.cv (nb053_alpha_dummy_022 x y))
            (Class.cv (nb053_alpha_dummy_023 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_022 x y))
            (Class.cv (nb053_alpha_dummy_023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0022 :
    (nb053_alpha_dummy_020) ∈
      (((Class.cv (nb053_alpha_dummy_019))).fv ∪ ((Class.cv (nb053_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0023 (x : Var) (y : Var) :
    (nb053_alpha_dummy_023 x y) ∈
      (((Class.cv (nb053_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb053_alpha_dummy_023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0024 :
    (nb053_alpha_dummy_019) ∈
      (((syn_ccompl (Class.cv (nb053_alpha_dummy_019)))).fv ∪
        ((syn_ccompl (Class.cv (nb053_alpha_dummy_020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0025 (x : Var) (y : Var) :
    (nb053_alpha_dummy_022 x y) ∈
      (((syn_ccompl (Class.cv (nb053_alpha_dummy_022 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb053_alpha_dummy_023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0026 :
    (nb053_alpha_dummy_019) ∈
      (((Class.cv (nb053_alpha_dummy_019))).fv ∪ ((Class.cv (nb053_alpha_dummy_019))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0027 (x : Var) (y : Var) :
    (nb053_alpha_dummy_022 x y) ∈
      (((Class.cv (nb053_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb053_alpha_dummy_022 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0028 :
    (nb053_alpha_dummy_020) ∈
      (((syn_ccompl (Class.cv (nb053_alpha_dummy_019)))).fv ∪
        ((syn_ccompl (Class.cv (nb053_alpha_dummy_020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0029 (x : Var) (y : Var) :
    (nb053_alpha_dummy_023 x y) ∈
      (((syn_ccompl (Class.cv (nb053_alpha_dummy_022 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb053_alpha_dummy_023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0030 :
    (nb053_alpha_dummy_020) ∈
      (((Class.cv (nb053_alpha_dummy_020))).fv ∪ ((Class.cv (nb053_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0031 (x : Var) (y : Var) :
    (nb053_alpha_dummy_023 x y) ∈
      (((Class.cv (nb053_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb053_alpha_dummy_023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0032 :
    (nb053_alpha_dummy_001) ∈
      (((Class.cv (nb053_alpha_dummy_000))).fv ∪ ((Class.cv (nb053_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0033 :
    (nb053_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb053_alpha_dummy_004)
              (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                  (syn_cphi (Class.cv (nb053_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb053_alpha_dummy_004)
              (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                  (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0034 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0035 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb053_alpha_dummy_006 x y)
              (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                  (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb053_alpha_dummy_006 x y)
              (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                  (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0034 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0034 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0036 :
    (nb053_alpha_dummy_001) ∈
      (((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb053_alpha_dummy_004)
            (syn_wrex (nb053_alpha_dummy_005) (Class.cv (nb053_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0037 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb053_alpha_dummy_006 x y)
            (syn_wrex (nb053_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0034 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0034 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0038 :
    (nb053_alpha_dummy_005) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb053_alpha_dummy_005))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0039 (x : Var) (y : Var) :
    (nb053_alpha_dummy_007 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0040 :
    (nb053_alpha_dummy_005) ∈
      (((syn_cphi (Class.cv (nb053_alpha_dummy_005)))).fv ∪
        ((syn_cphi (Class.cv (nb053_alpha_dummy_005)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0041 (x : Var) (y : Var) :
    (nb053_alpha_dummy_007 x y) ∈
      (((syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0042 :
    (nb053_alpha_dummy_000) ∈
      (((syn_cnin (Class.cv (nb053_alpha_dummy_000)) (Class.cv (nb053_alpha_dummy_001)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_000))
            (Class.cv (nb053_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0043 (x : Var) (y : Var) :
    x ∈
      (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪ ((syn_cnin (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0044 :
    (nb053_alpha_dummy_001) ∈
      (((syn_cnin (Class.cv (nb053_alpha_dummy_000)) (Class.cv (nb053_alpha_dummy_001)))).fv ∪
        ((syn_cnin (Class.cv (nb053_alpha_dummy_000))
            (Class.cv (nb053_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0045 (x : Var) (y : Var) :
    y ∈
      (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪ ((syn_cnin (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
