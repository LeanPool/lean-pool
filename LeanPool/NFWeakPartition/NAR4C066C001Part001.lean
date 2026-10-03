/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C066C001Part001. -/


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
noncomputable def nb066_alpha_dummy_000 (A : Class) (R : Class) : Var :=
  (freshVar ((A).fv ∪ (R).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_001 (A : Class) (R : Class) : Var :=
  (freshVar ((A).fv ∪ (R).fv) 1)

@[expose]
noncomputable def nb066_alpha_dummy_002 (A : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_003 (A : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv) 1)

@[expose]
noncomputable def nb066_alpha_dummy_004 (x : Var) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((syn_csn (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_005 (x : Var) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((syn_csn (Class.cv x))).fv) 1)

@[expose]
noncomputable def nb066_alpha_dummy_006 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_000 A R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_007 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_008 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
      ((Class.cv (nb066_alpha_dummy_002 A R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_009 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
      ((Class.cv (nb066_alpha_dummy_002 A R))).fv) 1)

@[expose]
noncomputable def nb066_alpha_dummy_010 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
      ((Class.cv (nb066_alpha_dummy_004 x R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_011 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
      ((Class.cv (nb066_alpha_dummy_004 x R))).fv) 1)

@[expose]
noncomputable def nb066_alpha_dummy_012 (A : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_013 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_014 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb066_alpha_dummy_008 A R)
          (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
            (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
              (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))))).fv ∪
      ((Class.cab (nb066_alpha_dummy_008 A R)
          (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
            (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
              (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_015 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cab (nb066_alpha_dummy_010 x R)
          (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
            (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
              (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))))).fv ∪
      ((Class.cab (nb066_alpha_dummy_010 x R)
          (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
            (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
              (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_016 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_009 A R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_017 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_009 A R))).fv) 1)

@[expose]
noncomputable def nb066_alpha_dummy_018 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_011 x R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_019 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_011 x R))).fv) 1)

@[expose]
noncomputable def nb066_alpha_dummy_020 (A : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb066_alpha_dummy_016 A R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb066_alpha_dummy_016 A R)) (syn_c1c))).fv ∪
      ((Class.cv (nb066_alpha_dummy_016 A R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_021 (x : Var) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb066_alpha_dummy_018 x R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb066_alpha_dummy_018 x R)) (syn_c1c))).fv ∪
      ((Class.cv (nb066_alpha_dummy_018 x R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_022 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_023 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb066_alpha_dummy_024 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb066_alpha_dummy_025 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_026 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb066_alpha_dummy_027 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb066_alpha_dummy_028 (A : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb066_alpha_dummy_023 A R))
          (Class.cv (nb066_alpha_dummy_024 A R)))).fv ∪
      ((syn_cnin (Class.cv (nb066_alpha_dummy_023 A R))
          (Class.cv (nb066_alpha_dummy_024 A R)))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_029 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb066_alpha_dummy_026 x R))
          (Class.cv (nb066_alpha_dummy_027 x R)))).fv ∪
      ((syn_cnin (Class.cv (nb066_alpha_dummy_026 x R))
          (Class.cv (nb066_alpha_dummy_027 x R)))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_030 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_023 A R))).fv ∪
      ((Class.cv (nb066_alpha_dummy_024 A R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_031 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_026 x R))).fv ∪
      ((Class.cv (nb066_alpha_dummy_027 x R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_032 (A : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb066_alpha_dummy_023 A R)))).fv ∪
      ((syn_ccompl (Class.cv (nb066_alpha_dummy_024 A R)))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_033 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb066_alpha_dummy_026 x R)))).fv ∪
      ((syn_ccompl (Class.cv (nb066_alpha_dummy_027 x R)))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_034 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_023 A R))).fv ∪
      ((Class.cv (nb066_alpha_dummy_023 A R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_035 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_026 x R))).fv ∪
      ((Class.cv (nb066_alpha_dummy_026 x R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_036 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_024 A R))).fv ∪
      ((Class.cv (nb066_alpha_dummy_024 A R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_037 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066_alpha_dummy_027 x R))).fv ∪
      ((Class.cv (nb066_alpha_dummy_027 x R))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_038 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb066_alpha_dummy_008 A R)
          (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
            (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
              (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb066_alpha_dummy_008 A R)
          (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
            (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
              (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_039 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cab (nb066_alpha_dummy_010 x R)
          (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
            (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
              (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb066_alpha_dummy_010 x R)
          (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
            (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
              (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_040 (A : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_041 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_042 (A : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))).fv ∪
      ((syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))).fv) 0)

@[expose]
noncomputable def nb066_alpha_dummy_043 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))).fv ∪
      ((syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))).fv) 0)

theorem nb066_fresh_000 (A : Class) (R : Class) :
    (nb066_alpha_dummy_038 A R) ∉
      (((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb066_alpha_dummy_038] using
    freshVar_not_mem
      (((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb066_fresh_001 (A : Class) (R : Class) :
    (nb066_alpha_dummy_014 A R) ∉
      (((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))))).fv ∪
        ((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))))).fv) :=
  by
  simpa only [nb066_alpha_dummy_014] using
    freshVar_not_mem
      (((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))))).fv ∪
        ((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))))).fv)
      0

theorem nb066_fresh_002 (x : Var) (R : Class) :
    (nb066_alpha_dummy_039 x R) ∉
      (((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb066_alpha_dummy_039] using
    freshVar_not_mem
      (((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb066_fresh_003 (x : Var) (R : Class) :
    (nb066_alpha_dummy_015 x R) ∉
      (((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))))).fv ∪
        ((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))))).fv) :=
  by
  simpa only [nb066_alpha_dummy_015] using
    freshVar_not_mem
      (((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))))).fv ∪
        ((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))))).fv)
      0

theorem nb066_fresh_004 (A : Class) (R : Class) :
    (nb066_alpha_dummy_006 A R) ∉ (((Class.cv (nb066_alpha_dummy_000 A R))).fv) := by
  simpa only [nb066_alpha_dummy_006] using
    freshVar_not_mem (((Class.cv (nb066_alpha_dummy_000 A R))).fv) 0

theorem nb066_fresh_005 (A : Class) (R : Class) :
    (nb066_alpha_dummy_008 A R) ∉
      (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_002 A R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_008] using
    freshVar_not_mem
      (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_002 A R))).fv)
      0

theorem nb066_fresh_006 (A : Class) (R : Class) :
    (nb066_alpha_dummy_009 A R) ∉
      (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_002 A R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_009] using
    freshVar_not_mem
      (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_002 A R))).fv)
      1

theorem nb066_distinct_007 (A : Class) (R : Class) :
    (nb066_alpha_dummy_008 A R) ≠ (nb066_alpha_dummy_009 A R) := by
  simpa only [nb066_alpha_dummy_008, nb066_alpha_dummy_009] using
    (freshVar_injective (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_002 A R))).fv) (i := 0) (j := 1) (by decide))

theorem nb066_fresh_008 (x : Var) (R : Class) :
    (nb066_alpha_dummy_010 x R) ∉
      (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_004 x R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_010] using
    freshVar_not_mem
      (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_004 x R))).fv)
      0

theorem nb066_fresh_009 (x : Var) (R : Class) :
    (nb066_alpha_dummy_011 x R) ∉
      (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_004 x R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_004 x R))).fv)
      1

theorem nb066_distinct_010 (x : Var) (R : Class) :
    (nb066_alpha_dummy_010 x R) ≠ (nb066_alpha_dummy_011 x R) := by
  simpa only [nb066_alpha_dummy_010, nb066_alpha_dummy_011] using
    (freshVar_injective (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_004 x R))).fv) (i := 0) (j := 1) (by decide))

theorem nb066_fresh_011 (A : Class) (R : Class) :
    (nb066_alpha_dummy_016 A R) ∉ (((Class.cv (nb066_alpha_dummy_009 A R))).fv) := by
  simpa only [nb066_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb066_alpha_dummy_009 A R))).fv) 0

theorem nb066_fresh_012 (A : Class) (R : Class) :
    (nb066_alpha_dummy_017 A R) ∉ (((Class.cv (nb066_alpha_dummy_009 A R))).fv) := by
  simpa only [nb066_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb066_alpha_dummy_009 A R))).fv) 1

theorem nb066_distinct_013 (A : Class) (R : Class) :
    (nb066_alpha_dummy_016 A R) ≠ (nb066_alpha_dummy_017 A R) := by
  simpa only [nb066_alpha_dummy_016, nb066_alpha_dummy_017] using
    (freshVar_injective (((Class.cv (nb066_alpha_dummy_009 A R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb066_fresh_014 (x : Var) (R : Class) :
    (nb066_alpha_dummy_018 x R) ∉ (((Class.cv (nb066_alpha_dummy_011 x R))).fv) := by
  simpa only [nb066_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb066_alpha_dummy_011 x R))).fv) 0

theorem nb066_fresh_015 (x : Var) (R : Class) :
    (nb066_alpha_dummy_019 x R) ∉ (((Class.cv (nb066_alpha_dummy_011 x R))).fv) := by
  simpa only [nb066_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb066_alpha_dummy_011 x R))).fv) 1

theorem nb066_distinct_016 (x : Var) (R : Class) :
    (nb066_alpha_dummy_018 x R) ≠ (nb066_alpha_dummy_019 x R) := by
  simpa only [nb066_alpha_dummy_018, nb066_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb066_alpha_dummy_011 x R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb066_fresh_017 (A : Class) (R : Class) :
    (nb066_alpha_dummy_022 A R) ∉
      (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb066_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb066_fresh_018 (A : Class) (R : Class) :
    (nb066_alpha_dummy_023 A R) ∉
      (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb066_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb066_fresh_019 (A : Class) (R : Class) :
    (nb066_alpha_dummy_024 A R) ∉
      (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb066_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb066_distinct_020 (A : Class) (R : Class) :
    (nb066_alpha_dummy_022 A R) ≠ (nb066_alpha_dummy_023 A R) := by
  simpa only [nb066_alpha_dummy_022, nb066_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb066_distinct_021 (A : Class) (R : Class) :
    (nb066_alpha_dummy_022 A R) ≠ (nb066_alpha_dummy_024 A R) := by
  simpa only [nb066_alpha_dummy_022, nb066_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb066_distinct_022 (A : Class) (R : Class) :
    (nb066_alpha_dummy_023 A R) ≠ (nb066_alpha_dummy_024 A R) := by
  simpa only [nb066_alpha_dummy_023, nb066_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb066_fresh_023 (x : Var) (R : Class) :
    (nb066_alpha_dummy_025 x R) ∉
      (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb066_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb066_fresh_024 (x : Var) (R : Class) :
    (nb066_alpha_dummy_026 x R) ∉
      (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb066_alpha_dummy_026] using
    freshVar_not_mem (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb066_fresh_025 (x : Var) (R : Class) :
    (nb066_alpha_dummy_027 x R) ∉
      (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb066_alpha_dummy_027] using
    freshVar_not_mem (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb066_distinct_026 (x : Var) (R : Class) :
    (nb066_alpha_dummy_025 x R) ≠ (nb066_alpha_dummy_026 x R) := by
  simpa only [nb066_alpha_dummy_025, nb066_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb066_distinct_027 (x : Var) (R : Class) :
    (nb066_alpha_dummy_025 x R) ≠ (nb066_alpha_dummy_027 x R) := by
  simpa only [nb066_alpha_dummy_025, nb066_alpha_dummy_027] using
    (freshVar_injective (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb066_distinct_028 (x : Var) (R : Class) :
    (nb066_alpha_dummy_026 x R) ≠ (nb066_alpha_dummy_027 x R) := by
  simpa only [nb066_alpha_dummy_026, nb066_alpha_dummy_027] using
    (freshVar_injective (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb066_fresh_029 (A : Class) (R : Class) :
    (nb066_alpha_dummy_034 A R) ∉
      (((Class.cv (nb066_alpha_dummy_023 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_023 A R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb066_alpha_dummy_023 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_023 A R))).fv)
      0

theorem nb066_fresh_030 (A : Class) (R : Class) :
    (nb066_alpha_dummy_030 A R) ∉
      (((Class.cv (nb066_alpha_dummy_023 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_024 A R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb066_alpha_dummy_023 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_024 A R))).fv)
      0

theorem nb066_fresh_031 (A : Class) (R : Class) :
    (nb066_alpha_dummy_036 A R) ∉
      (((Class.cv (nb066_alpha_dummy_024 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_024 A R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cv (nb066_alpha_dummy_024 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_024 A R))).fv)
      0

theorem nb066_fresh_032 (x : Var) (R : Class) :
    (nb066_alpha_dummy_035 x R) ∉
      (((Class.cv (nb066_alpha_dummy_026 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_026 x R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cv (nb066_alpha_dummy_026 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_026 x R))).fv)
      0

theorem nb066_fresh_033 (x : Var) (R : Class) :
    (nb066_alpha_dummy_031 x R) ∉
      (((Class.cv (nb066_alpha_dummy_026 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_027 x R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb066_alpha_dummy_026 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_027 x R))).fv)
      0

theorem nb066_fresh_034 (x : Var) (R : Class) :
    (nb066_alpha_dummy_037 x R) ∉
      (((Class.cv (nb066_alpha_dummy_027 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_027 x R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cv (nb066_alpha_dummy_027 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_027 x R))).fv)
      0

theorem nb066_fresh_035 (x : Var) : (nb066_alpha_dummy_007 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb066_alpha_dummy_007] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb066_fresh_036 (A : Class) (R : Class) :
    (nb066_alpha_dummy_020 A R) ∉
      (((Wff.classMem (Class.cv (nb066_alpha_dummy_016 A R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb066_alpha_dummy_016 A R)) (syn_c1c))).fv ∪
        ((Class.cv (nb066_alpha_dummy_016 A R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_020] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb066_alpha_dummy_016 A R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb066_alpha_dummy_016 A R)) (syn_c1c))).fv ∪
        ((Class.cv (nb066_alpha_dummy_016 A R))).fv)
      0

theorem nb066_fresh_037 (x : Var) (R : Class) :
    (nb066_alpha_dummy_021 x R) ∉
      (((Wff.classMem (Class.cv (nb066_alpha_dummy_018 x R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb066_alpha_dummy_018 x R)) (syn_c1c))).fv ∪
        ((Class.cv (nb066_alpha_dummy_018 x R))).fv) :=
  by
  simpa only [nb066_alpha_dummy_021] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb066_alpha_dummy_018 x R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb066_alpha_dummy_018 x R)) (syn_c1c))).fv ∪
        ((Class.cv (nb066_alpha_dummy_018 x R))).fv)
      0

theorem nb066_fresh_038 (A : Class) (R : Class) :
    (nb066_alpha_dummy_012 A R) ∉
      (((syn_ccompl (Class.cab (nb066_alpha_dummy_008 A R)
              (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                  (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb066_alpha_dummy_008 A R)
              (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                  (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb066_alpha_dummy_012] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb066_alpha_dummy_008 A R)
              (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                  (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb066_alpha_dummy_008 A R)
              (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                  (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb066_fresh_039 (x : Var) (R : Class) :
    (nb066_alpha_dummy_013 x R) ∉
      (((syn_ccompl (Class.cab (nb066_alpha_dummy_010 x R)
              (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                  (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb066_alpha_dummy_010 x R)
              (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                  (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb066_alpha_dummy_013] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb066_alpha_dummy_010 x R)
              (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                  (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb066_alpha_dummy_010 x R)
              (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                  (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb066_fresh_040 (A : Class) (R : Class) :
    (nb066_alpha_dummy_032 A R) ∉
      (((syn_ccompl (Class.cv (nb066_alpha_dummy_023 A R)))).fv ∪
        ((syn_ccompl (Class.cv (nb066_alpha_dummy_024 A R)))).fv) :=
  by
  simpa only [nb066_alpha_dummy_032] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb066_alpha_dummy_023 A R)))).fv ∪
        ((syn_ccompl (Class.cv (nb066_alpha_dummy_024 A R)))).fv)
      0

theorem nb066_fresh_041 (x : Var) (R : Class) :
    (nb066_alpha_dummy_033 x R) ∉
      (((syn_ccompl (Class.cv (nb066_alpha_dummy_026 x R)))).fv ∪
        ((syn_ccompl (Class.cv (nb066_alpha_dummy_027 x R)))).fv) :=
  by
  simpa only [nb066_alpha_dummy_033] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb066_alpha_dummy_026 x R)))).fv ∪
        ((syn_ccompl (Class.cv (nb066_alpha_dummy_027 x R)))).fv)
      0

theorem nb066_fresh_042 (A : Class) (R : Class) :
    (nb066_alpha_dummy_040 A R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb066_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb066_fresh_043 (x : Var) (R : Class) :
    (nb066_alpha_dummy_041 x R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb066_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb066_fresh_044 (A : Class) (R : Class) :
    (nb066_alpha_dummy_028 A R) ∉
      (((syn_cnin (Class.cv (nb066_alpha_dummy_023 A R))
            (Class.cv (nb066_alpha_dummy_024 A R)))).fv ∪
        ((syn_cnin (Class.cv (nb066_alpha_dummy_023 A R))
            (Class.cv (nb066_alpha_dummy_024 A R)))).fv) :=
  by
  simpa only [nb066_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb066_alpha_dummy_023 A R))
            (Class.cv (nb066_alpha_dummy_024 A R)))).fv ∪
        ((syn_cnin (Class.cv (nb066_alpha_dummy_023 A R))
            (Class.cv (nb066_alpha_dummy_024 A R)))).fv)
      0

theorem nb066_fresh_045 (x : Var) (R : Class) :
    (nb066_alpha_dummy_029 x R) ∉
      (((syn_cnin (Class.cv (nb066_alpha_dummy_026 x R))
            (Class.cv (nb066_alpha_dummy_027 x R)))).fv ∪
        ((syn_cnin (Class.cv (nb066_alpha_dummy_026 x R))
            (Class.cv (nb066_alpha_dummy_027 x R)))).fv) :=
  by
  simpa only [nb066_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb066_alpha_dummy_026 x R))
            (Class.cv (nb066_alpha_dummy_027 x R)))).fv ∪
        ((syn_cnin (Class.cv (nb066_alpha_dummy_026 x R))
            (Class.cv (nb066_alpha_dummy_027 x R)))).fv)
      0

theorem nb066_fresh_046 (A : Class) (R : Class) :
    (nb066_alpha_dummy_042 A R) ∉
      (((syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))).fv ∪
        ((syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))).fv) :=
  by
  simpa only [nb066_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))).fv ∪
        ((syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))).fv)
      0

theorem nb066_fresh_047 (x : Var) (R : Class) :
    (nb066_alpha_dummy_043 x R) ∉
      (((syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))).fv ∪
        ((syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))).fv) :=
  by
  simpa only [nb066_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))).fv ∪
        ((syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))).fv)
      0

theorem nb066_fresh_048 (A : Class) (R : Class) :
    (nb066_alpha_dummy_000 A R) ∉ ((A).fv ∪ (R).fv) := by
  simpa only [nb066_alpha_dummy_000] using freshVar_not_mem ((A).fv ∪ (R).fv) 0

theorem nb066_fresh_049 (A : Class) (R : Class) :
    (nb066_alpha_dummy_001 A R) ∉ ((A).fv ∪ (R).fv) := by
  simpa only [nb066_alpha_dummy_001] using freshVar_not_mem ((A).fv ∪ (R).fv) 1

theorem nb066_distinct_050 (A : Class) (R : Class) :
    (nb066_alpha_dummy_000 A R) ≠ (nb066_alpha_dummy_001 A R) := by
  simpa only [nb066_alpha_dummy_000, nb066_alpha_dummy_001] using
    (freshVar_injective ((A).fv ∪ (R).fv) (i := 0) (j := 1) (by decide))

theorem nb066_fresh_051 (A : Class) (R : Class) :
    (nb066_alpha_dummy_002 A R) ∉
      ((R).fv ∪ ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv) :=
  by
  simpa only [nb066_alpha_dummy_002] using
    freshVar_not_mem ((R).fv ∪ ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv) 0

theorem nb066_fresh_052 (A : Class) (R : Class) :
    (nb066_alpha_dummy_003 A R) ∉
      ((R).fv ∪ ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv) :=
  by
  simpa only [nb066_alpha_dummy_003] using
    freshVar_not_mem ((R).fv ∪ ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv) 1

theorem nb066_distinct_053 (A : Class) (R : Class) :
    (nb066_alpha_dummy_002 A R) ≠ (nb066_alpha_dummy_003 A R) := by
  simpa only [nb066_alpha_dummy_002, nb066_alpha_dummy_003] using
    (freshVar_injective ((R).fv ∪ ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb066_fresh_054 (x : Var) (R : Class) :
    (nb066_alpha_dummy_004 x R) ∉ ((R).fv ∪ ((syn_csn (Class.cv x))).fv) := by
  simpa only [nb066_alpha_dummy_004] using
    freshVar_not_mem ((R).fv ∪ ((syn_csn (Class.cv x))).fv) 0

theorem nb066_fresh_055 (x : Var) (R : Class) :
    (nb066_alpha_dummy_005 x R) ∉ ((R).fv ∪ ((syn_csn (Class.cv x))).fv) := by
  simpa only [nb066_alpha_dummy_005] using
    freshVar_not_mem ((R).fv ∪ ((syn_csn (Class.cv x))).fv) 1

theorem nb066_distinct_056 (x : Var) (R : Class) :
    (nb066_alpha_dummy_004 x R) ≠ (nb066_alpha_dummy_005 x R) := by
  simpa only [nb066_alpha_dummy_004, nb066_alpha_dummy_005] using
    (freshVar_injective ((R).fv ∪ ((syn_csn (Class.cv x))).fv) (i := 0) (j := 1) (by decide))

theorem nb066_support_mem_0000 (A : Class) (R : Class) :
    (nb066_alpha_dummy_000 A R) ∈
      ((R).fv ∪ ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0001 (x : Var) (R : Class) :
    x ∈ ((R).fv ∪ ((syn_csn (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0002 (A : Class) (R : Class) :
    (nb066_alpha_dummy_000 A R) ∈ (((Class.cv (nb066_alpha_dummy_000 A R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0003 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0004 (A : Class) (R : Class) :
    (nb066_alpha_dummy_003 A R) ∈
      (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_002 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0005 (A : Class) (R : Class) :
    (nb066_alpha_dummy_003 A R) ∈
      (((syn_ccompl (Class.cab (nb066_alpha_dummy_008 A R)
              (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                  (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb066_alpha_dummy_008 A R)
              (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                  (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0006 (x : Var) (R : Class) :
    (nb066_alpha_dummy_005 x R) ∈
      (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_004 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0007 (x : Var) (R : Class) :
    (nb066_alpha_dummy_005 x R) ∈
      (((syn_ccompl (Class.cab (nb066_alpha_dummy_010 x R)
              (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                  (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb066_alpha_dummy_010 x R)
              (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                  (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0008 (A : Class) (R : Class) :
    (nb066_alpha_dummy_003 A R) ∈
      (((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))))).fv ∪
        ((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0009 (x : Var) (R : Class) :
    (nb066_alpha_dummy_005 x R) ∈
      (((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))))).fv ∪
        ((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0010 (A : Class) (R : Class) :
    (nb066_alpha_dummy_009 A R) ∈ (((Class.cv (nb066_alpha_dummy_009 A R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0011 (x : Var) (R : Class) :
    (nb066_alpha_dummy_011 x R) ∈ (((Class.cv (nb066_alpha_dummy_011 x R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0012 (A : Class) (R : Class) :
    (nb066_alpha_dummy_016 A R) ∈
      (((Wff.classMem (Class.cv (nb066_alpha_dummy_016 A R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb066_alpha_dummy_016 A R)) (syn_c1c))).fv ∪
        ((Class.cv (nb066_alpha_dummy_016 A R))).fv) :=
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

theorem nb066_support_mem_0013 (x : Var) (R : Class) :
    (nb066_alpha_dummy_018 x R) ∈
      (((Wff.classMem (Class.cv (nb066_alpha_dummy_018 x R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb066_alpha_dummy_018 x R)) (syn_c1c))).fv ∪
        ((Class.cv (nb066_alpha_dummy_018 x R))).fv) :=
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

theorem nb066_support_mem_0014 (A : Class) (R : Class) :
    (nb066_alpha_dummy_016 A R) ∈
      (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0015 (x : Var) (R : Class) :
    (nb066_alpha_dummy_018 x R) ∈
      (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0016 (A : Class) (R : Class) :
    (nb066_alpha_dummy_023 A R) ∈
      (((syn_cnin (Class.cv (nb066_alpha_dummy_023 A R))
            (Class.cv (nb066_alpha_dummy_024 A R)))).fv ∪
        ((syn_cnin (Class.cv (nb066_alpha_dummy_023 A R))
            (Class.cv (nb066_alpha_dummy_024 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0017 (x : Var) (R : Class) :
    (nb066_alpha_dummy_026 x R) ∈
      (((syn_cnin (Class.cv (nb066_alpha_dummy_026 x R))
            (Class.cv (nb066_alpha_dummy_027 x R)))).fv ∪
        ((syn_cnin (Class.cv (nb066_alpha_dummy_026 x R))
            (Class.cv (nb066_alpha_dummy_027 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0018 (A : Class) (R : Class) :
    (nb066_alpha_dummy_023 A R) ∈
      (((Class.cv (nb066_alpha_dummy_023 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_024 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0019 (x : Var) (R : Class) :
    (nb066_alpha_dummy_026 x R) ∈
      (((Class.cv (nb066_alpha_dummy_026 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_027 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0020 (A : Class) (R : Class) :
    (nb066_alpha_dummy_024 A R) ∈
      (((syn_cnin (Class.cv (nb066_alpha_dummy_023 A R))
            (Class.cv (nb066_alpha_dummy_024 A R)))).fv ∪
        ((syn_cnin (Class.cv (nb066_alpha_dummy_023 A R))
            (Class.cv (nb066_alpha_dummy_024 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0021 (x : Var) (R : Class) :
    (nb066_alpha_dummy_027 x R) ∈
      (((syn_cnin (Class.cv (nb066_alpha_dummy_026 x R))
            (Class.cv (nb066_alpha_dummy_027 x R)))).fv ∪
        ((syn_cnin (Class.cv (nb066_alpha_dummy_026 x R))
            (Class.cv (nb066_alpha_dummy_027 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0022 (A : Class) (R : Class) :
    (nb066_alpha_dummy_024 A R) ∈
      (((Class.cv (nb066_alpha_dummy_023 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_024 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0023 (x : Var) (R : Class) :
    (nb066_alpha_dummy_027 x R) ∈
      (((Class.cv (nb066_alpha_dummy_026 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_027 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0024 (A : Class) (R : Class) :
    (nb066_alpha_dummy_023 A R) ∈
      (((syn_ccompl (Class.cv (nb066_alpha_dummy_023 A R)))).fv ∪
        ((syn_ccompl (Class.cv (nb066_alpha_dummy_024 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0025 (x : Var) (R : Class) :
    (nb066_alpha_dummy_026 x R) ∈
      (((syn_ccompl (Class.cv (nb066_alpha_dummy_026 x R)))).fv ∪
        ((syn_ccompl (Class.cv (nb066_alpha_dummy_027 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0026 (A : Class) (R : Class) :
    (nb066_alpha_dummy_023 A R) ∈
      (((Class.cv (nb066_alpha_dummy_023 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_023 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0027 (x : Var) (R : Class) :
    (nb066_alpha_dummy_026 x R) ∈
      (((Class.cv (nb066_alpha_dummy_026 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_026 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0028 (A : Class) (R : Class) :
    (nb066_alpha_dummy_024 A R) ∈
      (((syn_ccompl (Class.cv (nb066_alpha_dummy_023 A R)))).fv ∪
        ((syn_ccompl (Class.cv (nb066_alpha_dummy_024 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0029 (x : Var) (R : Class) :
    (nb066_alpha_dummy_027 x R) ∈
      (((syn_ccompl (Class.cv (nb066_alpha_dummy_026 x R)))).fv ∪
        ((syn_ccompl (Class.cv (nb066_alpha_dummy_027 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0030 (A : Class) (R : Class) :
    (nb066_alpha_dummy_024 A R) ∈
      (((Class.cv (nb066_alpha_dummy_024 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_024 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0031 (x : Var) (R : Class) :
    (nb066_alpha_dummy_027 x R) ∈
      (((Class.cv (nb066_alpha_dummy_027 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_027 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0032 (A : Class) (R : Class) :
    (nb066_alpha_dummy_002 A R) ∈
      (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_002 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0033 (A : Class) (R : Class) :
    (nb066_alpha_dummy_002 A R) ∈
      (((syn_ccompl (Class.cab (nb066_alpha_dummy_008 A R)
              (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_003 A R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                  (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb066_alpha_dummy_008 A R)
              (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                  (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0034 (x : Var) (R : Class) :
    (nb066_alpha_dummy_004 x R) ∈
      (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
        ((Class.cv (nb066_alpha_dummy_004 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0035 (x : Var) (R : Class) :
    (nb066_alpha_dummy_004 x R) ∈
      (((syn_ccompl (Class.cab (nb066_alpha_dummy_010 x R)
              (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_005 x R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                  (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb066_alpha_dummy_010 x R)
              (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                  (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0036 (A : Class) (R : Class) :
    (nb066_alpha_dummy_002 A R) ∈
      (((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0037 (x : Var) (R : Class) :
    (nb066_alpha_dummy_004 x R) ∈
      (((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0038 (A : Class) (R : Class) :
    (nb066_alpha_dummy_009 A R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0039 (x : Var) (R : Class) :
    (nb066_alpha_dummy_011 x R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0040 (A : Class) (R : Class) :
    (nb066_alpha_dummy_009 A R) ∈
      (((syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))).fv ∪
        ((syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0041 (x : Var) (R : Class) :
    (nb066_alpha_dummy_011 x R) ∈
      (((syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))).fv ∪
        ((syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_focused_notmem_0000 (A : Class) (R : Class) :
    (nb066_alpha_dummy_000 A R) ∉ A.fv :=
  by
  change freshVar ((A).fv ∪ (R).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb066_wpp_notmem_0000 (A : Class) (R : Class) :
    (nb066_alpha_dummy_000 A R) ∉ (A).fv := by exact (nb066_focused_notmem_0000 A R)

theorem nb066_wpp_notmem_0001 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) : x ∉ (A).fv := by
  exact dv_A_x

theorem nb066_focused_notmem_0001 (A : Class) (R : Class) :
    (nb066_alpha_dummy_001 A R) ∉ A.fv :=
  by
  change freshVar ((A).fv ∪ (R).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb066_wpp_notmem_0002 (A : Class) (R : Class) :
    (nb066_alpha_dummy_001 A R) ∉ (A).fv := by exact (nb066_focused_notmem_0001 A R)

theorem nb066_wpp_notmem_0003 (y : Var) (A : Class) (dv_A_y : y ∉ A.fv) : y ∉ (A).fv := by
  exact dv_A_y

theorem nb066_compact_envfresh_0000 (x : Var) (y : Var) (A : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TEnvFresh [((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
      (A).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb066_alpha_dummy_000 A R) x (nb066_wpp_notmem_0000 A R)
      (nb066_wpp_notmem_0001 x A dv_A_x)
      (TEnvFresh.consFresh (nb066_alpha_dummy_001 A R) y (nb066_wpp_notmem_0002 A R)
        (nb066_wpp_notmem_0003 y A dv_A_y) (TEnvFresh.nil (A).fv)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
