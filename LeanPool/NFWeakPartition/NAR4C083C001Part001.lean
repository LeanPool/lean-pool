/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C083C001Part001. -/


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
noncomputable def nb083_alpha_dummy_000 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_001 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1)

@[expose]
noncomputable def nb083_alpha_dummy_002 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
      ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_003 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
      ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv) 1)

@[expose]
noncomputable def nb083_alpha_dummy_004 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv b)).fv ∪ ((Class.cv c)).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_005 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv b)).fv ∪ ((Class.cv c)).fv) 1)

@[expose]
noncomputable def nb083_alpha_dummy_006 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (Class.cab (nb083_alpha_dummy_002 A B C R)
            (syn_wrex (nb083_alpha_dummy_003 A B C R) (Class.cv (nb083_alpha_dummy_000 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
              (Class.cv (nb083_alpha_dummy_001 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_007 (b : Var) (c : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_008 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb083_alpha_dummy_002 A B C R)
          (syn_wrex (nb083_alpha_dummy_003 A B C R) (Class.cv (nb083_alpha_dummy_000 A B C R))
            (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
              (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))))).fv ∪
      ((Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
            (Class.cv (nb083_alpha_dummy_000 A B C R))
            (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
              (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_009 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cab (nb083_alpha_dummy_004 b c)
          (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
            (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
              (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))))).fv ∪
      ((Class.cab (nb083_alpha_dummy_004 b c) (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
            (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
              (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_010 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_011 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv) 1)

@[expose]
noncomputable def nb083_alpha_dummy_012 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_005 b c))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_013 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_005 b c))).fv) 1)

@[expose]
noncomputable def nb083_alpha_dummy_014 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb083_alpha_dummy_010 A B C R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb083_alpha_dummy_010 A B C R)) (syn_c1c))).fv ∪
      ((Class.cv (nb083_alpha_dummy_010 A B C R))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_015 (b : Var) (c : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb083_alpha_dummy_012 b c)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb083_alpha_dummy_012 b c)) (syn_c1c))).fv ∪
      ((Class.cv (nb083_alpha_dummy_012 b c))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_016 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_017 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb083_alpha_dummy_018 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb083_alpha_dummy_019 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_020 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb083_alpha_dummy_021 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb083_alpha_dummy_022 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((syn_cnin (Class.cv (nb083_alpha_dummy_017 A B C R))
          (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv ∪
      ((syn_cnin (Class.cv (nb083_alpha_dummy_017 A B C R))
          (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_023 (b : Var) (c : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb083_alpha_dummy_020 b c))
          (Class.cv (nb083_alpha_dummy_021 b c)))).fv ∪
      ((syn_cnin (Class.cv (nb083_alpha_dummy_020 b c))
          (Class.cv (nb083_alpha_dummy_021 b c)))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_024 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_017 A B C R))).fv ∪
      ((Class.cv (nb083_alpha_dummy_018 A B C R))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_025 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_020 b c))).fv ∪
      ((Class.cv (nb083_alpha_dummy_021 b c))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_026 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (Class.cv (nb083_alpha_dummy_017 A B C R)))).fv ∪
      ((syn_ccompl (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_027 (b : Var) (c : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb083_alpha_dummy_020 b c)))).fv ∪
      ((syn_ccompl (Class.cv (nb083_alpha_dummy_021 b c)))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_028 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_017 A B C R))).fv ∪
      ((Class.cv (nb083_alpha_dummy_017 A B C R))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_029 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_020 b c))).fv ∪
      ((Class.cv (nb083_alpha_dummy_020 b c))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_030 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_018 A B C R))).fv ∪
      ((Class.cv (nb083_alpha_dummy_018 A B C R))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_031 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083_alpha_dummy_021 b c))).fv ∪
      ((Class.cv (nb083_alpha_dummy_021 b c))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_032 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb083_alpha_dummy_002 A B C R)
          (syn_wrex (nb083_alpha_dummy_003 A B C R) (Class.cv (nb083_alpha_dummy_001 A B C R))
            (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
              (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb083_alpha_dummy_002 A B C R)
          (syn_wrex (nb083_alpha_dummy_003 A B C R) (Class.cv (nb083_alpha_dummy_001 A B C R))
            (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
              (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_033 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cab (nb083_alpha_dummy_004 b c)
          (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
            (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
              (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb083_alpha_dummy_004 b c)
          (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
            (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
              (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_034 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_035 (b : Var) (c : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_036 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))).fv ∪
      ((syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))).fv) 0)

@[expose]
noncomputable def nb083_alpha_dummy_037 (b : Var) (c : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))).fv ∪
      ((syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))).fv) 0)

theorem nb083_fresh_000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_008 A B C R) ∉
      (((Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
              (Class.cv (nb083_alpha_dummy_000 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))))).fv ∪
        ((Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
              (Class.cv (nb083_alpha_dummy_000 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))))).fv) :=
  by
  simpa only [nb083_alpha_dummy_008] using
    freshVar_not_mem
      (((Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
              (Class.cv (nb083_alpha_dummy_000 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))))).fv ∪
        ((Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
              (Class.cv (nb083_alpha_dummy_000 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))))).fv)
      0

theorem nb083_fresh_001 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_032 A B C R) ∉
      (((Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
              (Class.cv (nb083_alpha_dummy_001 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb083_alpha_dummy_002 A B C R)
            (syn_wrex (nb083_alpha_dummy_003 A B C R) (Class.cv (nb083_alpha_dummy_001 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb083_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
              (Class.cv (nb083_alpha_dummy_001 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb083_alpha_dummy_002 A B C R)
            (syn_wrex (nb083_alpha_dummy_003 A B C R) (Class.cv (nb083_alpha_dummy_001 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb083_fresh_002 (b : Var) (c : Var) :
    (nb083_alpha_dummy_009 b c) ∉
      (((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))))).fv ∪
        ((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))))).fv) :=
  by
  simpa only [nb083_alpha_dummy_009] using
    freshVar_not_mem
      (((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))))).fv ∪
        ((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))))).fv)
      0

theorem nb083_fresh_003 (b : Var) (c : Var) :
    (nb083_alpha_dummy_033 b c) ∉
      (((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb083_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb083_fresh_004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_002 A B C R) ∉
      (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv) :=
  by
  simpa only [nb083_alpha_dummy_002] using
    freshVar_not_mem
      (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv)
      0

theorem nb083_fresh_005 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_003 A B C R) ∉
      (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv) :=
  by
  simpa only [nb083_alpha_dummy_003] using
    freshVar_not_mem
      (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv)
      1

theorem nb083_distinct_006 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_002 A B C R) ≠ (nb083_alpha_dummy_003 A B C R) := by
  simpa only [nb083_alpha_dummy_002, nb083_alpha_dummy_003] using
    (freshVar_injective (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv) (i := 0) (j := 1) (by decide))

theorem nb083_fresh_007 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_010 A B C R) ∉ (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv) :=
  by
  simpa only [nb083_alpha_dummy_010] using
    freshVar_not_mem (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv) 0

theorem nb083_fresh_008 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_011 A B C R) ∉ (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv) :=
  by
  simpa only [nb083_alpha_dummy_011] using
    freshVar_not_mem (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv) 1

theorem nb083_distinct_009 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_010 A B C R) ≠ (nb083_alpha_dummy_011 A B C R) := by
  simpa only [nb083_alpha_dummy_010, nb083_alpha_dummy_011] using
    (freshVar_injective (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb083_fresh_010 (b : Var) (c : Var) :
    (nb083_alpha_dummy_012 b c) ∉ (((Class.cv (nb083_alpha_dummy_005 b c))).fv) := by
  simpa only [nb083_alpha_dummy_012] using
    freshVar_not_mem (((Class.cv (nb083_alpha_dummy_005 b c))).fv) 0

theorem nb083_fresh_011 (b : Var) (c : Var) :
    (nb083_alpha_dummy_013 b c) ∉ (((Class.cv (nb083_alpha_dummy_005 b c))).fv) := by
  simpa only [nb083_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb083_alpha_dummy_005 b c))).fv) 1

theorem nb083_distinct_012 (b : Var) (c : Var) :
    (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_013 b c) := by
  simpa only [nb083_alpha_dummy_012, nb083_alpha_dummy_013] using
    (freshVar_injective (((Class.cv (nb083_alpha_dummy_005 b c))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb083_fresh_013 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_016 A B C R) ∉
      (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb083_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb083_fresh_014 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_017 A B C R) ∉
      (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb083_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb083_fresh_015 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_018 A B C R) ∉
      (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb083_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb083_distinct_016 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_016 A B C R) ≠ (nb083_alpha_dummy_017 A B C R) := by
  simpa only [nb083_alpha_dummy_016, nb083_alpha_dummy_017] using
    (freshVar_injective (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb083_distinct_017 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_016 A B C R) ≠ (nb083_alpha_dummy_018 A B C R) := by
  simpa only [nb083_alpha_dummy_016, nb083_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb083_distinct_018 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_017 A B C R) ≠ (nb083_alpha_dummy_018 A B C R) := by
  simpa only [nb083_alpha_dummy_017, nb083_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb083_fresh_019 (b : Var) (c : Var) :
    (nb083_alpha_dummy_019 b c) ∉
      (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb083_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) 0

theorem nb083_fresh_020 (b : Var) (c : Var) :
    (nb083_alpha_dummy_020 b c) ∉
      (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb083_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) 1

theorem nb083_fresh_021 (b : Var) (c : Var) :
    (nb083_alpha_dummy_021 b c) ∉
      (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb083_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) 2

theorem nb083_distinct_022 (b : Var) (c : Var) :
    (nb083_alpha_dummy_019 b c) ≠ (nb083_alpha_dummy_020 b c) := by
  simpa only [nb083_alpha_dummy_019, nb083_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb083_distinct_023 (b : Var) (c : Var) :
    (nb083_alpha_dummy_019 b c) ≠ (nb083_alpha_dummy_021 b c) := by
  simpa only [nb083_alpha_dummy_019, nb083_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb083_distinct_024 (b : Var) (c : Var) :
    (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_021 b c) := by
  simpa only [nb083_alpha_dummy_020, nb083_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb083_fresh_025 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_028 A B C R) ∉
      (((Class.cv (nb083_alpha_dummy_017 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_017 A B C R))).fv) :=
  by
  simpa only [nb083_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb083_alpha_dummy_017 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_017 A B C R))).fv)
      0

theorem nb083_fresh_026 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_024 A B C R) ∉
      (((Class.cv (nb083_alpha_dummy_017 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_018 A B C R))).fv) :=
  by
  simpa only [nb083_alpha_dummy_024] using
    freshVar_not_mem
      (((Class.cv (nb083_alpha_dummy_017 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_018 A B C R))).fv)
      0

theorem nb083_fresh_027 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_030 A B C R) ∉
      (((Class.cv (nb083_alpha_dummy_018 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_018 A B C R))).fv) :=
  by
  simpa only [nb083_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb083_alpha_dummy_018 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_018 A B C R))).fv)
      0

theorem nb083_fresh_028 (b : Var) (c : Var) :
    (nb083_alpha_dummy_029 b c) ∉
      (((Class.cv (nb083_alpha_dummy_020 b c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_020 b c))).fv) :=
  by
  simpa only [nb083_alpha_dummy_029] using
    freshVar_not_mem
      (((Class.cv (nb083_alpha_dummy_020 b c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_020 b c))).fv)
      0

theorem nb083_fresh_029 (b : Var) (c : Var) :
    (nb083_alpha_dummy_025 b c) ∉
      (((Class.cv (nb083_alpha_dummy_020 b c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_021 b c))).fv) :=
  by
  simpa only [nb083_alpha_dummy_025] using
    freshVar_not_mem
      (((Class.cv (nb083_alpha_dummy_020 b c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_021 b c))).fv)
      0

theorem nb083_fresh_030 (b : Var) (c : Var) :
    (nb083_alpha_dummy_031 b c) ∉
      (((Class.cv (nb083_alpha_dummy_021 b c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_021 b c))).fv) :=
  by
  simpa only [nb083_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb083_alpha_dummy_021 b c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_021 b c))).fv)
      0

theorem nb083_fresh_031 (b : Var) (c : Var) :
    (nb083_alpha_dummy_004 b c) ∉ (((Class.cv b)).fv ∪ ((Class.cv c)).fv) := by
  simpa only [nb083_alpha_dummy_004] using
    freshVar_not_mem (((Class.cv b)).fv ∪ ((Class.cv c)).fv) 0

theorem nb083_fresh_032 (b : Var) (c : Var) :
    (nb083_alpha_dummy_005 b c) ∉ (((Class.cv b)).fv ∪ ((Class.cv c)).fv) := by
  simpa only [nb083_alpha_dummy_005] using
    freshVar_not_mem (((Class.cv b)).fv ∪ ((Class.cv c)).fv) 1

theorem nb083_distinct_033 (b : Var) (c : Var) :
    (nb083_alpha_dummy_004 b c) ≠ (nb083_alpha_dummy_005 b c) := by
  simpa only [nb083_alpha_dummy_004, nb083_alpha_dummy_005] using
    (freshVar_injective (((Class.cv b)).fv ∪ ((Class.cv c)).fv) (i := 0) (j := 1) (by decide))

theorem nb083_fresh_034 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_014 A B C R) ∉
      (((Wff.classMem (Class.cv (nb083_alpha_dummy_010 A B C R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb083_alpha_dummy_010 A B C R)) (syn_c1c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_010 A B C R))).fv) :=
  by
  simpa only [nb083_alpha_dummy_014] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb083_alpha_dummy_010 A B C R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb083_alpha_dummy_010 A B C R)) (syn_c1c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_010 A B C R))).fv)
      0

theorem nb083_fresh_035 (b : Var) (c : Var) :
    (nb083_alpha_dummy_015 b c) ∉
      (((Wff.classMem (Class.cv (nb083_alpha_dummy_012 b c)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb083_alpha_dummy_012 b c)) (syn_c1c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_012 b c))).fv) :=
  by
  simpa only [nb083_alpha_dummy_015] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb083_alpha_dummy_012 b c)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb083_alpha_dummy_012 b c)) (syn_c1c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_012 b c))).fv)
      0

theorem nb083_fresh_036 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_006 A B C R) ∉
      (((syn_ccompl (Class.cab (nb083_alpha_dummy_002 A B C R)
              (syn_wrex (nb083_alpha_dummy_003 A B C R)
                (Class.cv (nb083_alpha_dummy_000 A B C R))
                (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                  (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
                (Class.cv (nb083_alpha_dummy_001 A B C R))
                (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                  (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb083_alpha_dummy_006] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb083_alpha_dummy_002 A B C R)
              (syn_wrex (nb083_alpha_dummy_003 A B C R)
                (Class.cv (nb083_alpha_dummy_000 A B C R))
                (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                  (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
                (Class.cv (nb083_alpha_dummy_001 A B C R))
                (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                  (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb083_fresh_037 (b : Var) (c : Var) :
    (nb083_alpha_dummy_007 b c) ∉
      (((syn_ccompl (Class.cab (nb083_alpha_dummy_004 b c)
              (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
                (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                  (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb083_alpha_dummy_004 b c)
              (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
                (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                  (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb083_alpha_dummy_007] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb083_alpha_dummy_004 b c)
              (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
                (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                  (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb083_alpha_dummy_004 b c)
              (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
                (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                  (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb083_fresh_038 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_026 A B C R) ∉
      (((syn_ccompl (Class.cv (nb083_alpha_dummy_017 A B C R)))).fv ∪
        ((syn_ccompl (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv) :=
  by
  simpa only [nb083_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb083_alpha_dummy_017 A B C R)))).fv ∪
        ((syn_ccompl (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv)
      0

theorem nb083_fresh_039 (b : Var) (c : Var) :
    (nb083_alpha_dummy_027 b c) ∉
      (((syn_ccompl (Class.cv (nb083_alpha_dummy_020 b c)))).fv ∪
        ((syn_ccompl (Class.cv (nb083_alpha_dummy_021 b c)))).fv) :=
  by
  simpa only [nb083_alpha_dummy_027] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb083_alpha_dummy_020 b c)))).fv ∪
        ((syn_ccompl (Class.cv (nb083_alpha_dummy_021 b c)))).fv)
      0

theorem nb083_fresh_040 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_034 A B C R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb083_alpha_dummy_034] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb083_fresh_041 (b : Var) (c : Var) :
    (nb083_alpha_dummy_035 b c) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb083_alpha_dummy_035] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb083_fresh_042 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_022 A B C R) ∉
      (((syn_cnin (Class.cv (nb083_alpha_dummy_017 A B C R))
            (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv ∪
        ((syn_cnin (Class.cv (nb083_alpha_dummy_017 A B C R))
            (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv) :=
  by
  simpa only [nb083_alpha_dummy_022] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb083_alpha_dummy_017 A B C R))
            (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv ∪
        ((syn_cnin (Class.cv (nb083_alpha_dummy_017 A B C R))
            (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv)
      0

theorem nb083_fresh_043 (b : Var) (c : Var) :
    (nb083_alpha_dummy_023 b c) ∉
      (((syn_cnin (Class.cv (nb083_alpha_dummy_020 b c))
            (Class.cv (nb083_alpha_dummy_021 b c)))).fv ∪
        ((syn_cnin (Class.cv (nb083_alpha_dummy_020 b c))
            (Class.cv (nb083_alpha_dummy_021 b c)))).fv) :=
  by
  simpa only [nb083_alpha_dummy_023] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb083_alpha_dummy_020 b c))
            (Class.cv (nb083_alpha_dummy_021 b c)))).fv ∪
        ((syn_cnin (Class.cv (nb083_alpha_dummy_020 b c))
            (Class.cv (nb083_alpha_dummy_021 b c)))).fv)
      0

theorem nb083_fresh_044 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_036 A B C R) ∉
      (((syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))).fv ∪
        ((syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))).fv) :=
  by
  simpa only [nb083_alpha_dummy_036] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))).fv ∪
        ((syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))).fv)
      0

theorem nb083_fresh_045 (b : Var) (c : Var) :
    (nb083_alpha_dummy_037 b c) ∉
      (((syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))).fv ∪
        ((syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))).fv) :=
  by
  simpa only [nb083_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))).fv ∪
        ((syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))).fv)
      0

theorem nb083_fresh_046 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_000 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb083_alpha_dummy_000] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0

theorem nb083_fresh_047 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_001 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb083_alpha_dummy_001] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1

theorem nb083_distinct_048 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_000 A B C R) ≠ (nb083_alpha_dummy_001 A B C R) := by
  simpa only [nb083_alpha_dummy_000, nb083_alpha_dummy_001] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) (i := 0) (j := 1) (by decide))

theorem nb083_support_mem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_000 A B C R) ∈
      (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0001 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_000 A B C R) ∈
      (((syn_ccompl (Class.cab (nb083_alpha_dummy_002 A B C R)
              (syn_wrex (nb083_alpha_dummy_003 A B C R)
                (Class.cv (nb083_alpha_dummy_000 A B C R))
                (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                  (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
                (Class.cv (nb083_alpha_dummy_001 A B C R))
                (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                  (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb083_alpha_dummy_000 A B C R) ≠ (nb083_alpha_dummy_002 A B C R) from (by
          unfold nb083_alpha_dummy_002;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0000 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb083_alpha_dummy_000 A B C R) ≠ (nb083_alpha_dummy_003 A B C R) from (by
            unfold nb083_alpha_dummy_003;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0000 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0002 (b : Var) (c : Var) :
    b ∈ (((Class.cv b)).fv ∪ ((Class.cv c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0003 (b : Var) (c : Var) :
    b ∈
      (((syn_ccompl (Class.cab (nb083_alpha_dummy_004 b c)
              (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
                (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                  (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb083_alpha_dummy_004 b c)
              (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
                (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                  (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb083_alpha_dummy_004 b c) from (by
          unfold nb083_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0002 b c) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb083_alpha_dummy_005 b c) from (by
            unfold nb083_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0002 b c) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_000 A B C R) ∈
      (((Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
              (Class.cv (nb083_alpha_dummy_000 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))))).fv ∪
        ((Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
              (Class.cv (nb083_alpha_dummy_000 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb083_alpha_dummy_000 A B C R) ≠ (nb083_alpha_dummy_002 A B C R) from (by
          unfold nb083_alpha_dummy_002;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0000 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb083_alpha_dummy_000 A B C R) ≠ (nb083_alpha_dummy_003 A B C R) from (by
            unfold nb083_alpha_dummy_003;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0000 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0005 (b : Var) (c : Var) :
    b ∈
      (((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))))).fv ∪
        ((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb083_alpha_dummy_004 b c) from (by
          unfold nb083_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0002 b c) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb083_alpha_dummy_005 b c) from (by
            unfold nb083_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0002 b c) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0006 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_003 A B C R) ∈ (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0007 (b : Var) (c : Var) :
    (nb083_alpha_dummy_005 b c) ∈ (((Class.cv (nb083_alpha_dummy_005 b c))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0008 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_010 A B C R) ∈
      (((Wff.classMem (Class.cv (nb083_alpha_dummy_010 A B C R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb083_alpha_dummy_010 A B C R)) (syn_c1c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_010 A B C R))).fv) :=
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

theorem nb083_support_mem_0009 (b : Var) (c : Var) :
    (nb083_alpha_dummy_012 b c) ∈
      (((Wff.classMem (Class.cv (nb083_alpha_dummy_012 b c)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb083_alpha_dummy_012 b c)) (syn_c1c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_012 b c))).fv) :=
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

theorem nb083_support_mem_0010 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_010 A B C R) ∈
      (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0011 (b : Var) (c : Var) :
    (nb083_alpha_dummy_012 b c) ∈
      (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0012 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_017 A B C R) ∈
      (((syn_cnin (Class.cv (nb083_alpha_dummy_017 A B C R))
            (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv ∪
        ((syn_cnin (Class.cv (nb083_alpha_dummy_017 A B C R))
            (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0013 (b : Var) (c : Var) :
    (nb083_alpha_dummy_020 b c) ∈
      (((syn_cnin (Class.cv (nb083_alpha_dummy_020 b c))
            (Class.cv (nb083_alpha_dummy_021 b c)))).fv ∪
        ((syn_cnin (Class.cv (nb083_alpha_dummy_020 b c))
            (Class.cv (nb083_alpha_dummy_021 b c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0014 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_017 A B C R) ∈
      (((Class.cv (nb083_alpha_dummy_017 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_018 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0015 (b : Var) (c : Var) :
    (nb083_alpha_dummy_020 b c) ∈
      (((Class.cv (nb083_alpha_dummy_020 b c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_021 b c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0016 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_018 A B C R) ∈
      (((syn_cnin (Class.cv (nb083_alpha_dummy_017 A B C R))
            (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv ∪
        ((syn_cnin (Class.cv (nb083_alpha_dummy_017 A B C R))
            (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0017 (b : Var) (c : Var) :
    (nb083_alpha_dummy_021 b c) ∈
      (((syn_cnin (Class.cv (nb083_alpha_dummy_020 b c))
            (Class.cv (nb083_alpha_dummy_021 b c)))).fv ∪
        ((syn_cnin (Class.cv (nb083_alpha_dummy_020 b c))
            (Class.cv (nb083_alpha_dummy_021 b c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0018 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_018 A B C R) ∈
      (((Class.cv (nb083_alpha_dummy_017 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_018 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0019 (b : Var) (c : Var) :
    (nb083_alpha_dummy_021 b c) ∈
      (((Class.cv (nb083_alpha_dummy_020 b c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_021 b c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0020 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_017 A B C R) ∈
      (((syn_ccompl (Class.cv (nb083_alpha_dummy_017 A B C R)))).fv ∪
        ((syn_ccompl (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0021 (b : Var) (c : Var) :
    (nb083_alpha_dummy_020 b c) ∈
      (((syn_ccompl (Class.cv (nb083_alpha_dummy_020 b c)))).fv ∪
        ((syn_ccompl (Class.cv (nb083_alpha_dummy_021 b c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0022 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_017 A B C R) ∈
      (((Class.cv (nb083_alpha_dummy_017 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_017 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0023 (b : Var) (c : Var) :
    (nb083_alpha_dummy_020 b c) ∈
      (((Class.cv (nb083_alpha_dummy_020 b c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_020 b c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0024 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_018 A B C R) ∈
      (((syn_ccompl (Class.cv (nb083_alpha_dummy_017 A B C R)))).fv ∪
        ((syn_ccompl (Class.cv (nb083_alpha_dummy_018 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0025 (b : Var) (c : Var) :
    (nb083_alpha_dummy_021 b c) ∈
      (((syn_ccompl (Class.cv (nb083_alpha_dummy_020 b c)))).fv ∪
        ((syn_ccompl (Class.cv (nb083_alpha_dummy_021 b c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0026 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_018 A B C R) ∈
      (((Class.cv (nb083_alpha_dummy_018 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_018 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0027 (b : Var) (c : Var) :
    (nb083_alpha_dummy_021 b c) ∈
      (((Class.cv (nb083_alpha_dummy_021 b c))).fv ∪
        ((Class.cv (nb083_alpha_dummy_021 b c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0028 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_001 A B C R) ∈
      (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0029 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_001 A B C R) ∈
      (((syn_ccompl (Class.cab (nb083_alpha_dummy_002 A B C R)
              (syn_wrex (nb083_alpha_dummy_003 A B C R)
                (Class.cv (nb083_alpha_dummy_000 A B C R))
                (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                  (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
                (Class.cv (nb083_alpha_dummy_001 A B C R))
                (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                  (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb083_alpha_dummy_001 A B C R) ≠ (nb083_alpha_dummy_002 A B C R) from (by
          unfold nb083_alpha_dummy_002;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb083_alpha_dummy_001 A B C R) ≠ (nb083_alpha_dummy_003 A B C R) from (by
            unfold nb083_alpha_dummy_003;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0030 (b : Var) (c : Var) :
    c ∈ (((Class.cv b)).fv ∪ ((Class.cv c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0031 (b : Var) (c : Var) :
    c ∈
      (((syn_ccompl (Class.cab (nb083_alpha_dummy_004 b c)
              (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv b)
                (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                  (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb083_alpha_dummy_004 b c)
              (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
                (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                  (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show c ≠ (nb083_alpha_dummy_004 b c) from (by
          unfold nb083_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0030 b c) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show c ≠ (nb083_alpha_dummy_005 b c) from (by
            unfold nb083_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0030 b c) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0032 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_001 A B C R) ∈
      (((Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
              (Class.cv (nb083_alpha_dummy_001 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb083_alpha_dummy_002 A B C R)
            (syn_wrex (nb083_alpha_dummy_003 A B C R) (Class.cv (nb083_alpha_dummy_001 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb083_alpha_dummy_001 A B C R) ≠ (nb083_alpha_dummy_002 A B C R) from (by
          unfold nb083_alpha_dummy_002;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb083_alpha_dummy_001 A B C R) ≠ (nb083_alpha_dummy_003 A B C R) from (by
            unfold nb083_alpha_dummy_003;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0033 (b : Var) (c : Var) :
    c ∈
      (((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show c ≠ (nb083_alpha_dummy_004 b c) from (by
          unfold nb083_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0030 b c) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show c ≠ (nb083_alpha_dummy_005 b c) from (by
            unfold nb083_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0030 b c) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0034 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_003 A B C R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0035 (b : Var) (c : Var) :
    (nb083_alpha_dummy_005 b c) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0036 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_003 A B C R) ∈
      (((syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))).fv ∪
        ((syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0037 (b : Var) (c : Var) :
    (nb083_alpha_dummy_005 b c) ∈
      (((syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))).fv ∪
        ((syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_focused_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_000 A B C R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb083_compact_envfresh_0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (dv_A_b : b ∉ A.fv) :
    TEnvFresh [((nb083_alpha_dummy_000 A B C R), b)] A.fv := by
  exact
    (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b
      (nb083_focused_notmem_0000 A B C R) dv_A_b (TEnvFresh.nil A.fv))

@[expose]
noncomputable def nb083_focused_refl_0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (dv_A_b : b ∉ A.fv) : TReflOn [((nb083_alpha_dummy_000 A B C R), b)] A.fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0000 A B C R b dv_A_b)

theorem nb083_focused_notmem_0001 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_000 A B C R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb083_focused_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_000 A B C R) ∉ C.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb083_wpp_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_000 A B C R) ∉ ((syn_csep2 B C)).fv := by
  simpa only [nb083_alpha_dummy_000, fv_syn_csep2, Finset.mem_union, not_or] using
    (And.intro (nb083_focused_notmem_0001 A B C R) (nb083_focused_notmem_0002 A B C R))

theorem nb083_wpp_notmem_0001 (B : Class) (C : Class) (b : Var) (dv_B_b : b ∉ B.fv)
    (dv_C_b : b ∉ C.fv) : b ∉ ((syn_csep2 B C)).fv := by
  simpa only [fv_syn_csep2, Finset.mem_union, not_or] using (And.intro dv_B_b dv_C_b)

theorem nb083_compact_envfresh_0001 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (dv_B_b : b ∉ B.fv) (dv_C_b : b ∉ C.fv) :
    TEnvFresh [((nb083_alpha_dummy_000 A B C R), b)] ((syn_csep2 B C)).fv := by
  exact
    (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b (nb083_wpp_notmem_0000 A B C R)
      (nb083_wpp_notmem_0001 B C b dv_B_b dv_C_b) (TEnvFresh.nil ((syn_csep2 B C)).fv))

@[expose]
noncomputable def nb083_wpp_refl_0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (dv_B_b : b ∉ B.fv) (dv_C_b : b ∉ C.fv) :
    TReflOn [((nb083_alpha_dummy_000 A B C R), b)] ((syn_csep2 B C)).fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0001 A B C R b dv_B_b dv_C_b)

theorem nb083_focused_notmem_0003 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_001 A B C R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb083_compact_envfresh_0002 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_A_b : b ∉ A.fv) (dv_A_c : c ∉ A.fv) :
    TEnvFresh [((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)]
      A.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb083_alpha_dummy_001 A B C R) c
      (nb083_focused_notmem_0003 A B C R) dv_A_c
      (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b
        (nb083_focused_notmem_0000 A B C R) dv_A_b (TEnvFresh.nil A.fv)))

@[expose]
noncomputable def nb083_focused_refl_0001 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_A_b : b ∉ A.fv) (dv_A_c : c ∉ A.fv) :
    TReflOn [((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)]
      A.fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0002 A B C R b c dv_A_b dv_A_c)

theorem nb083_focused_notmem_0004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_001 A B C R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb083_focused_notmem_0005 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_001 A B C R) ∉ C.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb083_wpp_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_001 A B C R) ∉ ((syn_csep2 B C)).fv := by
  simpa only [nb083_alpha_dummy_001, fv_syn_csep2, Finset.mem_union, not_or] using
    (And.intro (nb083_focused_notmem_0004 A B C R) (nb083_focused_notmem_0005 A B C R))

theorem nb083_wpp_notmem_0003 (B : Class) (C : Class) (c : Var) (dv_B_c : c ∉ B.fv)
    (dv_C_c : c ∉ C.fv) : c ∉ ((syn_csep2 B C)).fv := by
  simpa only [fv_syn_csep2, Finset.mem_union, not_or] using (And.intro dv_B_c dv_C_c)

theorem nb083_compact_envfresh_0003 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_B_b : b ∉ B.fv) (dv_B_c : c ∉ B.fv) (dv_C_b : b ∉ C.fv)
    (dv_C_c : c ∉ C.fv) :
    TEnvFresh [((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)]
      ((syn_csep2 B C)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb083_alpha_dummy_001 A B C R) c (nb083_wpp_notmem_0002 A B C R)
      (nb083_wpp_notmem_0003 B C c dv_B_c dv_C_c)
      (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b
        (nb083_wpp_notmem_0000 A B C R) (nb083_wpp_notmem_0001 B C b dv_B_b dv_C_b)
        (TEnvFresh.nil ((syn_csep2 B C)).fv)))

@[expose]
noncomputable def nb083_wpp_refl_0001 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_B_b : b ∉ B.fv) (dv_B_c : c ∉ B.fv) (dv_C_b : b ∉ C.fv)
    (dv_C_c : c ∉ C.fv) :
    TReflOn [((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)]
      ((syn_csep2 B C)).fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0003 A B C R b c dv_B_b dv_B_c dv_C_b dv_C_c)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
