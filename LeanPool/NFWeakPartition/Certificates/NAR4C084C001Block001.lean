/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C084C001Part001`. -/


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

@[expose]
noncomputable def nb084_alpha_dummy_000 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_001 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1)

@[expose]
noncomputable def nb084_alpha_dummy_002 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2)

@[expose]
noncomputable def nb084_alpha_dummy_003 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_004 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) 1)

@[expose]
noncomputable def nb084_alpha_dummy_005 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_006 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb084_alpha_dummy_007 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_008 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_009 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_003 A B R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_004 A B R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_010 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_003 A B R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_004 A B R))).fv) 1)

@[expose]
noncomputable def nb084_alpha_dummy_011 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_005 x y A R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_006 x y A R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_012 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_005 x y A R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_006 x y A R))).fv) 1)

@[expose]
noncomputable def nb084_alpha_dummy_013 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb084_alpha_dummy_009 A B R)
            (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
              (Class.cv (nb084_alpha_dummy_004 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_014 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (Class.cab (nb084_alpha_dummy_011 x y A R)
            (syn_wrex (nb084_alpha_dummy_012 x y A R) (Class.cv (nb084_alpha_dummy_005 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
              (Class.cv (nb084_alpha_dummy_006 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_015 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb084_alpha_dummy_009 A B R)
          (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_003 A B R))
            (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
              (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))))).fv ∪
      ((Class.cab (nb084_alpha_dummy_009 A B R)
          (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_003 A B R))
            (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
              (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_016 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb084_alpha_dummy_011 x y A R)
          (syn_wrex (nb084_alpha_dummy_012 x y A R) (Class.cv (nb084_alpha_dummy_005 x y A R))
            (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
              (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))))).fv ∪
      ((Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
            (Class.cv (nb084_alpha_dummy_005 x y A R))
            (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
              (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_017 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_010 A B R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_018 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_010 A B R))).fv) 1)

@[expose]
noncomputable def nb084_alpha_dummy_019 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_012 x y A R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_020 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_012 x y A R))).fv) 1)

@[expose]
noncomputable def nb084_alpha_dummy_021 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb084_alpha_dummy_017 A B R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb084_alpha_dummy_017 A B R)) (syn_c1c))).fv ∪
      ((Class.cv (nb084_alpha_dummy_017 A B R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_022 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb084_alpha_dummy_019 x y A R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb084_alpha_dummy_019 x y A R)) (syn_c1c))).fv ∪
      ((Class.cv (nb084_alpha_dummy_019 x y A R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_023 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_024 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb084_alpha_dummy_025 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb084_alpha_dummy_026 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_027 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb084_alpha_dummy_028 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb084_alpha_dummy_029 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb084_alpha_dummy_024 A B R))
          (Class.cv (nb084_alpha_dummy_025 A B R)))).fv ∪
      ((syn_cnin (Class.cv (nb084_alpha_dummy_024 A B R))
          (Class.cv (nb084_alpha_dummy_025 A B R)))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_030 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((syn_cnin (Class.cv (nb084_alpha_dummy_027 x y A R))
          (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv ∪
      ((syn_cnin (Class.cv (nb084_alpha_dummy_027 x y A R))
          (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_031 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_024 A B R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_025 A B R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_032 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_027 x y A R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_028 x y A R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_033 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb084_alpha_dummy_024 A B R)))).fv ∪
      ((syn_ccompl (Class.cv (nb084_alpha_dummy_025 A B R)))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_034 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (Class.cv (nb084_alpha_dummy_027 x y A R)))).fv ∪
      ((syn_ccompl (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_035 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_024 A B R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_024 A B R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_036 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_027 x y A R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_027 x y A R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_037 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_025 A B R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_025 A B R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_038 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084_alpha_dummy_028 x y A R))).fv ∪
      ((Class.cv (nb084_alpha_dummy_028 x y A R))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_039 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb084_alpha_dummy_009 A B R)
          (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_004 A B R))
            (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
              (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb084_alpha_dummy_009 A B R)
          (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_004 A B R))
            (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
              (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_040 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb084_alpha_dummy_011 x y A R)
          (syn_wrex (nb084_alpha_dummy_012 x y A R) (Class.cv (nb084_alpha_dummy_006 x y A R))
            (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
              (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb084_alpha_dummy_011 x y A R)
          (syn_wrex (nb084_alpha_dummy_012 x y A R) (Class.cv (nb084_alpha_dummy_006 x y A R))
            (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
              (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_041 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_042 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_043 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))).fv ∪
      ((syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))).fv) 0)

@[expose]
noncomputable def nb084_alpha_dummy_044 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))).fv ∪
      ((syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))).fv) 0)

theorem nb084_fresh_000 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_015 A B R) ∉
      (((Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
              (Class.cv (nb084_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))))).fv ∪
        ((Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
              (Class.cv (nb084_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))))).fv) :=
  by
  simpa only [nb084_alpha_dummy_015] using
    freshVar_not_mem
      (((Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
              (Class.cv (nb084_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))))).fv ∪
        ((Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
              (Class.cv (nb084_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))))).fv)
      0

theorem nb084_fresh_001 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_039 A B R) ∉
      (((Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
              (Class.cv (nb084_alpha_dummy_004 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb084_alpha_dummy_009 A B R)
            (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_004 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb084_alpha_dummy_039] using
    freshVar_not_mem
      (((Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
              (Class.cv (nb084_alpha_dummy_004 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb084_alpha_dummy_009 A B R)
            (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_004 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb084_fresh_002 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_016 x y A R) ∉
      (((Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
              (Class.cv (nb084_alpha_dummy_005 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))))).fv ∪
        ((Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
              (Class.cv (nb084_alpha_dummy_005 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))))).fv) :=
  by
  simpa only [nb084_alpha_dummy_016] using
    freshVar_not_mem
      (((Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
              (Class.cv (nb084_alpha_dummy_005 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))))).fv ∪
        ((Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
              (Class.cv (nb084_alpha_dummy_005 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))))).fv)
      0

theorem nb084_fresh_003 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_040 x y A R) ∉
      (((Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
              (Class.cv (nb084_alpha_dummy_006 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb084_alpha_dummy_011 x y A R)
            (syn_wrex (nb084_alpha_dummy_012 x y A R) (Class.cv (nb084_alpha_dummy_006 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb084_alpha_dummy_040] using
    freshVar_not_mem
      (((Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
              (Class.cv (nb084_alpha_dummy_006 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb084_alpha_dummy_011 x y A R)
            (syn_wrex (nb084_alpha_dummy_012 x y A R) (Class.cv (nb084_alpha_dummy_006 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb084_fresh_004 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_007 A B R) ∉
      (((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_007] using
    freshVar_not_mem
      (((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_002 A B R))).fv)
      0

theorem nb084_fresh_005 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_009 A B R) ∉
      (((Class.cv (nb084_alpha_dummy_003 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_004 A B R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_009] using
    freshVar_not_mem
      (((Class.cv (nb084_alpha_dummy_003 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_004 A B R))).fv)
      0

theorem nb084_fresh_006 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_010 A B R) ∉
      (((Class.cv (nb084_alpha_dummy_003 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_004 A B R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_010] using
    freshVar_not_mem
      (((Class.cv (nb084_alpha_dummy_003 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_004 A B R))).fv)
      1

theorem nb084_distinct_007 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_009 A B R) ≠ (nb084_alpha_dummy_010 A B R) := by
  simpa only [nb084_alpha_dummy_009, nb084_alpha_dummy_010] using
    (freshVar_injective (((Class.cv (nb084_alpha_dummy_003 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_004 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb084_fresh_008 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_011 x y A R) ∉
      (((Class.cv (nb084_alpha_dummy_005 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_006 x y A R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cv (nb084_alpha_dummy_005 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_006 x y A R))).fv)
      0

theorem nb084_fresh_009 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_012 x y A R) ∉
      (((Class.cv (nb084_alpha_dummy_005 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_006 x y A R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cv (nb084_alpha_dummy_005 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_006 x y A R))).fv)
      1

theorem nb084_distinct_010 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_011 x y A R) ≠ (nb084_alpha_dummy_012 x y A R) := by
  simpa only [nb084_alpha_dummy_011, nb084_alpha_dummy_012] using
    (freshVar_injective (((Class.cv (nb084_alpha_dummy_005 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_006 x y A R))).fv) (i := 0) (j := 1) (by decide))

theorem nb084_fresh_011 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_017 A B R) ∉ (((Class.cv (nb084_alpha_dummy_010 A B R))).fv) := by
  simpa only [nb084_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb084_alpha_dummy_010 A B R))).fv) 0

theorem nb084_fresh_012 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_018 A B R) ∉ (((Class.cv (nb084_alpha_dummy_010 A B R))).fv) := by
  simpa only [nb084_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb084_alpha_dummy_010 A B R))).fv) 1

theorem nb084_distinct_013 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_017 A B R) ≠ (nb084_alpha_dummy_018 A B R) := by
  simpa only [nb084_alpha_dummy_017, nb084_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb084_alpha_dummy_010 A B R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb084_fresh_014 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_019 x y A R) ∉ (((Class.cv (nb084_alpha_dummy_012 x y A R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb084_alpha_dummy_012 x y A R))).fv) 0

theorem nb084_fresh_015 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_020 x y A R) ∉ (((Class.cv (nb084_alpha_dummy_012 x y A R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb084_alpha_dummy_012 x y A R))).fv) 1

theorem nb084_distinct_016 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_020 x y A R) := by
  simpa only [nb084_alpha_dummy_019, nb084_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb084_alpha_dummy_012 x y A R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb084_fresh_017 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_023 A B R) ∉
      (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb084_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb084_fresh_018 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_024 A B R) ∉
      (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb084_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb084_fresh_019 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_025 A B R) ∉
      (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb084_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb084_distinct_020 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_023 A B R) ≠ (nb084_alpha_dummy_024 A B R) := by
  simpa only [nb084_alpha_dummy_023, nb084_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb084_distinct_021 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_023 A B R) ≠ (nb084_alpha_dummy_025 A B R) := by
  simpa only [nb084_alpha_dummy_023, nb084_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb084_distinct_022 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_024 A B R) ≠ (nb084_alpha_dummy_025 A B R) := by
  simpa only [nb084_alpha_dummy_024, nb084_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb084_fresh_023 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_026 x y A R) ∉
      (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb084_alpha_dummy_026] using
    freshVar_not_mem (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb084_fresh_024 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_027 x y A R) ∉
      (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb084_alpha_dummy_027] using
    freshVar_not_mem (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb084_fresh_025 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_028 x y A R) ∉
      (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb084_alpha_dummy_028] using
    freshVar_not_mem (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb084_distinct_026 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_026 x y A R) ≠ (nb084_alpha_dummy_027 x y A R) := by
  simpa only [nb084_alpha_dummy_026, nb084_alpha_dummy_027] using
    (freshVar_injective (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb084_distinct_027 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_026 x y A R) ≠ (nb084_alpha_dummy_028 x y A R) := by
  simpa only [nb084_alpha_dummy_026, nb084_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb084_distinct_028 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_028 x y A R) := by
  simpa only [nb084_alpha_dummy_027, nb084_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb084_fresh_029 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_035 A B R) ∉
      (((Class.cv (nb084_alpha_dummy_024 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_024 A B R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cv (nb084_alpha_dummy_024 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_024 A B R))).fv)
      0

theorem nb084_fresh_030 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_031 A B R) ∉
      (((Class.cv (nb084_alpha_dummy_024 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_025 A B R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb084_alpha_dummy_024 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_025 A B R))).fv)
      0

theorem nb084_fresh_031 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_037 A B R) ∉
      (((Class.cv (nb084_alpha_dummy_025 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_025 A B R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cv (nb084_alpha_dummy_025 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_025 A B R))).fv)
      0

theorem nb084_fresh_032 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_036 x y A R) ∉
      (((Class.cv (nb084_alpha_dummy_027 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_027 x y A R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cv (nb084_alpha_dummy_027 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_027 x y A R))).fv)
      0

theorem nb084_fresh_033 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_032 x y A R) ∉
      (((Class.cv (nb084_alpha_dummy_027 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_028 x y A R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb084_alpha_dummy_027 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_028 x y A R))).fv)
      0

theorem nb084_fresh_034 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_038 x y A R) ∉
      (((Class.cv (nb084_alpha_dummy_028 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_028 x y A R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_038] using
    freshVar_not_mem
      (((Class.cv (nb084_alpha_dummy_028 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_028 x y A R))).fv)
      0

theorem nb084_fresh_035 (x : Var) (y : Var) :
    (nb084_alpha_dummy_008 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb084_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb084_fresh_036 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_021 A B R) ∉
      (((Wff.classMem (Class.cv (nb084_alpha_dummy_017 A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb084_alpha_dummy_017 A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb084_alpha_dummy_017 A B R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_021] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb084_alpha_dummy_017 A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb084_alpha_dummy_017 A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb084_alpha_dummy_017 A B R))).fv)
      0

theorem nb084_fresh_037 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_022 x y A R) ∉
      (((Wff.classMem (Class.cv (nb084_alpha_dummy_019 x y A R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb084_alpha_dummy_019 x y A R)) (syn_c1c))).fv ∪
        ((Class.cv (nb084_alpha_dummy_019 x y A R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_022] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb084_alpha_dummy_019 x y A R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb084_alpha_dummy_019 x y A R)) (syn_c1c))).fv ∪
        ((Class.cv (nb084_alpha_dummy_019 x y A R))).fv)
      0

theorem nb084_fresh_038 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_013 A B R) ∉
      (((syn_ccompl (Class.cab (nb084_alpha_dummy_009 A B R)
              (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_003 A B R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                  (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
                (Class.cv (nb084_alpha_dummy_004 A B R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb084_alpha_dummy_013] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb084_alpha_dummy_009 A B R)
              (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_003 A B R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                  (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
                (Class.cv (nb084_alpha_dummy_004 A B R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb084_fresh_039 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_014 x y A R) ∉
      (((syn_ccompl (Class.cab (nb084_alpha_dummy_011 x y A R)
              (syn_wrex (nb084_alpha_dummy_012 x y A R)
                (Class.cv (nb084_alpha_dummy_005 x y A R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                  (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
                (Class.cv (nb084_alpha_dummy_006 x y A R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                  (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb084_alpha_dummy_014] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb084_alpha_dummy_011 x y A R)
              (syn_wrex (nb084_alpha_dummy_012 x y A R)
                (Class.cv (nb084_alpha_dummy_005 x y A R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                  (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
                (Class.cv (nb084_alpha_dummy_006 x y A R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                  (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb084_fresh_040 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_033 A B R) ∉
      (((syn_ccompl (Class.cv (nb084_alpha_dummy_024 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb084_alpha_dummy_025 A B R)))).fv) :=
  by
  simpa only [nb084_alpha_dummy_033] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb084_alpha_dummy_024 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb084_alpha_dummy_025 A B R)))).fv)
      0

theorem nb084_fresh_041 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_034 x y A R) ∉
      (((syn_ccompl (Class.cv (nb084_alpha_dummy_027 x y A R)))).fv ∪
        ((syn_ccompl (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv) :=
  by
  simpa only [nb084_alpha_dummy_034] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb084_alpha_dummy_027 x y A R)))).fv ∪
        ((syn_ccompl (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv)
      0

theorem nb084_fresh_042 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_041 A B R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb084_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb084_fresh_043 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_042 x y A R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb084_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb084_fresh_044 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_029 A B R) ∉
      (((syn_cnin (Class.cv (nb084_alpha_dummy_024 A B R))
            (Class.cv (nb084_alpha_dummy_025 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb084_alpha_dummy_024 A B R))
            (Class.cv (nb084_alpha_dummy_025 A B R)))).fv) :=
  by
  simpa only [nb084_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb084_alpha_dummy_024 A B R))
            (Class.cv (nb084_alpha_dummy_025 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb084_alpha_dummy_024 A B R))
            (Class.cv (nb084_alpha_dummy_025 A B R)))).fv)
      0

theorem nb084_fresh_045 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_030 x y A R) ∉
      (((syn_cnin (Class.cv (nb084_alpha_dummy_027 x y A R))
            (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv ∪
        ((syn_cnin (Class.cv (nb084_alpha_dummy_027 x y A R))
            (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv) :=
  by
  simpa only [nb084_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb084_alpha_dummy_027 x y A R))
            (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv ∪
        ((syn_cnin (Class.cv (nb084_alpha_dummy_027 x y A R))
            (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv)
      0

theorem nb084_fresh_046 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_043 A B R) ∉
      (((syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))).fv) :=
  by
  simpa only [nb084_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))).fv)
      0

theorem nb084_fresh_047 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_044 x y A R) ∉
      (((syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))).fv ∪
        ((syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))).fv) :=
  by
  simpa only [nb084_alpha_dummy_044] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))).fv ∪
        ((syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))).fv)
      0

theorem nb084_fresh_048 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_003 A B R) ∉
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_003] using
    freshVar_not_mem
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_002 A B R))).fv)
      0

theorem nb084_fresh_049 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_004 A B R) ∉
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) :=
  by
  simpa only [nb084_alpha_dummy_004] using
    freshVar_not_mem
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_002 A B R))).fv)
      1

theorem nb084_distinct_050 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_003 A B R) ≠ (nb084_alpha_dummy_004 A B R) := by
  simpa only [nb084_alpha_dummy_003, nb084_alpha_dummy_004] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb084_fresh_051 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_005 x y A R) ∉
      ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  simpa only [nb084_alpha_dummy_005] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb084_fresh_052 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_006 x y A R) ∉
      ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  simpa only [nb084_alpha_dummy_006] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb084_distinct_053 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_005 x y A R) ≠ (nb084_alpha_dummy_006 x y A R) := by
  simpa only [nb084_alpha_dummy_005, nb084_alpha_dummy_006] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb084_fresh_054 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_000 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb084_alpha_dummy_000] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv) 0

theorem nb084_fresh_055 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_001 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb084_alpha_dummy_001] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv) 1

theorem nb084_fresh_056 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_002 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb084_alpha_dummy_002] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv) 2

theorem nb084_distinct_057 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_000 A B R) ≠ (nb084_alpha_dummy_001 A B R) := by
  simpa only [nb084_alpha_dummy_000, nb084_alpha_dummy_001] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv) (i := 0) (j := 1) (by decide))

theorem nb084_distinct_058 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_000 A B R) ≠ (nb084_alpha_dummy_002 A B R) := by
  simpa only [nb084_alpha_dummy_000, nb084_alpha_dummy_002] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv) (i := 0) (j := 2) (by decide))

theorem nb084_distinct_059 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_001 A B R) ≠ (nb084_alpha_dummy_002 A B R) := by
  simpa only [nb084_alpha_dummy_001, nb084_alpha_dummy_002] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv) (i := 1) (j := 2) (by decide))

theorem nb084_support_mem_0000 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_001 A B R) ∈
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0001 (x : Var) (y : Var) (A : Class) (R : Class) :
    x ∈ ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0002 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_001 A B R) ∈
      (((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0003 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0004 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_002 A B R) ∈
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0005 (x : Var) (y : Var) (A : Class) (R : Class) :
    y ∈ ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0006 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_002 A B R) ∈
      (((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0007 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0008 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_003 A B R) ∈
      (((Class.cv (nb084_alpha_dummy_003 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_004 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0009 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_003 A B R) ∈
      (((syn_ccompl (Class.cab (nb084_alpha_dummy_009 A B R)
              (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_003 A B R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                  (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
                (Class.cv (nb084_alpha_dummy_004 A B R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084_alpha_dummy_003 A B R) ≠ (nb084_alpha_dummy_009 A B R) from (by
          unfold nb084_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0008 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084_alpha_dummy_003 A B R) ≠ (nb084_alpha_dummy_010 A B R) from (by
            unfold nb084_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0008 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0010 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_005 x y A R) ∈
      (((Class.cv (nb084_alpha_dummy_005 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_006 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0011 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_005 x y A R) ∈
      (((syn_ccompl (Class.cab (nb084_alpha_dummy_011 x y A R)
              (syn_wrex (nb084_alpha_dummy_012 x y A R)
                (Class.cv (nb084_alpha_dummy_005 x y A R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                  (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
                (Class.cv (nb084_alpha_dummy_006 x y A R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                  (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084_alpha_dummy_005 x y A R) ≠ (nb084_alpha_dummy_011 x y A R) from (by
          unfold nb084_alpha_dummy_011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084_alpha_dummy_005 x y A R) ≠ (nb084_alpha_dummy_012 x y A R) from (by
            unfold nb084_alpha_dummy_012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0012 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_003 A B R) ∈
      (((Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
              (Class.cv (nb084_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))))).fv ∪
        ((Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
              (Class.cv (nb084_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084_alpha_dummy_003 A B R) ≠ (nb084_alpha_dummy_009 A B R) from (by
          unfold nb084_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0008 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084_alpha_dummy_003 A B R) ≠ (nb084_alpha_dummy_010 A B R) from (by
            unfold nb084_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0008 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0013 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_005 x y A R) ∈
      (((Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
              (Class.cv (nb084_alpha_dummy_005 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))))).fv ∪
        ((Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
              (Class.cv (nb084_alpha_dummy_005 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084_alpha_dummy_005 x y A R) ≠ (nb084_alpha_dummy_011 x y A R) from (by
          unfold nb084_alpha_dummy_011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084_alpha_dummy_005 x y A R) ≠ (nb084_alpha_dummy_012 x y A R) from (by
            unfold nb084_alpha_dummy_012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0014 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_010 A B R) ∈ (((Class.cv (nb084_alpha_dummy_010 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0015 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_012 x y A R) ∈ (((Class.cv (nb084_alpha_dummy_012 x y A R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0016 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_017 A B R) ∈
      (((Wff.classMem (Class.cv (nb084_alpha_dummy_017 A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb084_alpha_dummy_017 A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb084_alpha_dummy_017 A B R))).fv) :=
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

theorem nb084_support_mem_0017 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_019 x y A R) ∈
      (((Wff.classMem (Class.cv (nb084_alpha_dummy_019 x y A R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb084_alpha_dummy_019 x y A R)) (syn_c1c))).fv ∪
        ((Class.cv (nb084_alpha_dummy_019 x y A R))).fv) :=
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

theorem nb084_support_mem_0018 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_017 A B R) ∈
      (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0019 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_019 x y A R) ∈
      (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0020 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_024 A B R) ∈
      (((syn_cnin (Class.cv (nb084_alpha_dummy_024 A B R))
            (Class.cv (nb084_alpha_dummy_025 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb084_alpha_dummy_024 A B R))
            (Class.cv (nb084_alpha_dummy_025 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0021 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_027 x y A R) ∈
      (((syn_cnin (Class.cv (nb084_alpha_dummy_027 x y A R))
            (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv ∪
        ((syn_cnin (Class.cv (nb084_alpha_dummy_027 x y A R))
            (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0022 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_024 A B R) ∈
      (((Class.cv (nb084_alpha_dummy_024 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_025 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0023 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_027 x y A R) ∈
      (((Class.cv (nb084_alpha_dummy_027 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_028 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0024 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_025 A B R) ∈
      (((syn_cnin (Class.cv (nb084_alpha_dummy_024 A B R))
            (Class.cv (nb084_alpha_dummy_025 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb084_alpha_dummy_024 A B R))
            (Class.cv (nb084_alpha_dummy_025 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0025 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_028 x y A R) ∈
      (((syn_cnin (Class.cv (nb084_alpha_dummy_027 x y A R))
            (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv ∪
        ((syn_cnin (Class.cv (nb084_alpha_dummy_027 x y A R))
            (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0026 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_025 A B R) ∈
      (((Class.cv (nb084_alpha_dummy_024 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_025 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0027 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_028 x y A R) ∈
      (((Class.cv (nb084_alpha_dummy_027 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_028 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0028 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_024 A B R) ∈
      (((syn_ccompl (Class.cv (nb084_alpha_dummy_024 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb084_alpha_dummy_025 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0029 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_027 x y A R) ∈
      (((syn_ccompl (Class.cv (nb084_alpha_dummy_027 x y A R)))).fv ∪
        ((syn_ccompl (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0030 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_024 A B R) ∈
      (((Class.cv (nb084_alpha_dummy_024 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_024 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0031 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_027 x y A R) ∈
      (((Class.cv (nb084_alpha_dummy_027 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_027 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0032 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_025 A B R) ∈
      (((syn_ccompl (Class.cv (nb084_alpha_dummy_024 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb084_alpha_dummy_025 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0033 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_028 x y A R) ∈
      (((syn_ccompl (Class.cv (nb084_alpha_dummy_027 x y A R)))).fv ∪
        ((syn_ccompl (Class.cv (nb084_alpha_dummy_028 x y A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0034 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_025 A B R) ∈
      (((Class.cv (nb084_alpha_dummy_025 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_025 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0035 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_028 x y A R) ∈
      (((Class.cv (nb084_alpha_dummy_028 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_028 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0036 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_004 A B R) ∈
      (((Class.cv (nb084_alpha_dummy_003 A B R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_004 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0037 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_004 A B R) ∈
      (((syn_ccompl (Class.cab (nb084_alpha_dummy_009 A B R)
              (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_003 A B R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                  (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
                (Class.cv (nb084_alpha_dummy_004 A B R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084_alpha_dummy_004 A B R) ≠ (nb084_alpha_dummy_009 A B R) from (by
          unfold nb084_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084_alpha_dummy_004 A B R) ≠ (nb084_alpha_dummy_010 A B R) from (by
            unfold nb084_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0038 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_006 x y A R) ∈
      (((Class.cv (nb084_alpha_dummy_005 x y A R))).fv ∪
        ((Class.cv (nb084_alpha_dummy_006 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0039 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_006 x y A R) ∈
      (((syn_ccompl (Class.cab (nb084_alpha_dummy_011 x y A R)
              (syn_wrex (nb084_alpha_dummy_012 x y A R)
                (Class.cv (nb084_alpha_dummy_005 x y A R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                  (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
                (Class.cv (nb084_alpha_dummy_006 x y A R))
                (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                  (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084_alpha_dummy_006 x y A R) ≠ (nb084_alpha_dummy_011 x y A R) from (by
          unfold nb084_alpha_dummy_011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084_alpha_dummy_006 x y A R) ≠ (nb084_alpha_dummy_012 x y A R) from (by
            unfold nb084_alpha_dummy_012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0040 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_004 A B R) ∈
      (((Class.cab (nb084_alpha_dummy_009 A B R) (syn_wrex (nb084_alpha_dummy_010 A B R)
              (Class.cv (nb084_alpha_dummy_004 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb084_alpha_dummy_009 A B R)
            (syn_wrex (nb084_alpha_dummy_010 A B R) (Class.cv (nb084_alpha_dummy_004 A B R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084_alpha_dummy_004 A B R) ≠ (nb084_alpha_dummy_009 A B R) from (by
          unfold nb084_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084_alpha_dummy_004 A B R) ≠ (nb084_alpha_dummy_010 A B R) from (by
            unfold nb084_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0041 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_006 x y A R) ∈
      (((Class.cab (nb084_alpha_dummy_011 x y A R) (syn_wrex (nb084_alpha_dummy_012 x y A R)
              (Class.cv (nb084_alpha_dummy_006 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb084_alpha_dummy_011 x y A R)
            (syn_wrex (nb084_alpha_dummy_012 x y A R) (Class.cv (nb084_alpha_dummy_006 x y A R))
              (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
                (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084_alpha_dummy_006 x y A R) ≠ (nb084_alpha_dummy_011 x y A R) from (by
          unfold nb084_alpha_dummy_011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084_alpha_dummy_006 x y A R) ≠ (nb084_alpha_dummy_012 x y A R) from (by
            unfold nb084_alpha_dummy_012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0042 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_010 A B R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0043 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_012 x y A R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0044 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_010 A B R) ∈
      (((syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C084C001Part002`. -/


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

theorem nb084_support_mem_0045 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_012 x y A R) ∈
      (((syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))).fv ∪
        ((syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_focused_notmem_0000 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_000 A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb084_compact_envfresh_0000 (A : Class) (B : Class) (R : Class) (d : Var)
    (dv_A_d : d ∉ A.fv) : TEnvFresh [((nb084_alpha_dummy_000 A B R), d)] A.fv := by
  exact
    (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d (nb084_focused_notmem_0000 A B R)
      dv_A_d (TEnvFresh.nil A.fv))

@[expose]
noncomputable def nb084_focused_refl_0000 (A : Class) (B : Class) (R : Class) (d : Var)
    (dv_A_d : d ∉ A.fv) : TReflOn [((nb084_alpha_dummy_000 A B R), d)] A.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0000 A B R d dv_A_d)

theorem nb084_focused_notmem_0001 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_001 A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb084_focused_notmem_0002 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_000 A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb084_compact_envfresh_0001 (x : Var) (A : Class) (B : Class) (R : Class)
    (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) :
    TEnvFresh [((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)]
      B.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x (nb084_focused_notmem_0001 A B R)
      dv_B_x (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d
        (nb084_focused_notmem_0002 A B R) dv_B_d (TEnvFresh.nil B.fv)))

@[expose]
noncomputable def nb084_focused_refl_0001 (x : Var) (A : Class) (B : Class) (R : Class)
    (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) :
    TReflOn [((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)]
      B.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0001 x A B R d dv_B_d dv_B_x)

theorem nb084_focused_notmem_0003 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_002 A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb084_compact_envfresh_0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) :
    TEnvFresh
      [((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)]
      B.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb084_alpha_dummy_002 A B R) y (nb084_focused_notmem_0003 A B R)
      dv_B_y (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x
        (nb084_focused_notmem_0001 A B R) dv_B_x
        (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d
          (nb084_focused_notmem_0002 A B R) dv_B_d (TEnvFresh.nil B.fv))))

@[expose]
noncomputable def nb084_focused_refl_0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) :
    TReflOn
      [((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)]
      B.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0002 x y A B R d dv_B_d dv_B_x dv_B_y)

theorem nb084_focused_notmem_0004 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_003 A B R) ∉ A.fv :=
  by
  change
    freshVar
        ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
          ((Class.cv (nb084_alpha_dummy_002 A B R))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_focused_notmem_0005 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_005 x y A R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_focused_notmem_0006 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_002 A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb084_focused_notmem_0007 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_001 A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb084_compact_envfresh_0003 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TEnvFresh
      [((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)]
      A.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb084_alpha_dummy_003 A B R) (nb084_alpha_dummy_005 x y A R)
      (nb084_focused_notmem_0004 A B R) (nb084_focused_notmem_0005 x y A R)
      (TEnvFresh.consFresh (nb084_alpha_dummy_002 A B R) y
        (nb084_focused_notmem_0006 A B R) dv_A_y
        (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x
          (nb084_focused_notmem_0007 A B R) dv_A_x
          (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d
            (nb084_focused_notmem_0000 A B R) dv_A_d (TEnvFresh.nil A.fv)))))

@[expose]
noncomputable def nb084_focused_refl_0003 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TReflOn
      [((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)]
      A.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0003 x y A B R d dv_A_d dv_A_x dv_A_y)

theorem nb084_focused_notmem_0008 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_004 A B R) ∉ A.fv :=
  by
  change
    freshVar
        ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
          ((Class.cv (nb084_alpha_dummy_002 A B R))).fv)
        1 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_focused_notmem_0009 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_006 x y A R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_compact_envfresh_0004 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TEnvFresh
      [((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)]
      A.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb084_alpha_dummy_004 A B R) (nb084_alpha_dummy_006 x y A R)
      (nb084_focused_notmem_0008 A B R) (nb084_focused_notmem_0009 x y A R)
      (TEnvFresh.consFresh (nb084_alpha_dummy_003 A B R) (nb084_alpha_dummy_005 x y A R)
        (nb084_focused_notmem_0004 A B R) (nb084_focused_notmem_0005 x y A R)
        (TEnvFresh.consFresh (nb084_alpha_dummy_002 A B R) y
          (nb084_focused_notmem_0006 A B R) dv_A_y
          (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x
            (nb084_focused_notmem_0007 A B R) dv_A_x
            (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d
              (nb084_focused_notmem_0000 A B R) dv_A_d (TEnvFresh.nil A.fv))))))

@[expose]
noncomputable def nb084_focused_refl_0004 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TReflOn
      [((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)]
      A.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0004 x y A B R d dv_A_d dv_A_x dv_A_y)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
