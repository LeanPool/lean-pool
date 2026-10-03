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

/-! Certificates from `NAR4C079C001Part001`. -/


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
noncomputable def nb079_alpha_dummy_000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

@[expose]
noncomputable def nb079_alpha_dummy_002 (A : Class) : Var :=
  (freshVar ((A).fv) 2)

@[expose]
noncomputable def nb079_alpha_dummy_003 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A)))))).fv ∪
      ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
              (Class.cv (nb079_alpha_dummy_001 A)))))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_004 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_cpr (Class.cv x) (Class.cv y))))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_005 (A : Class) : Var :=
  (freshVar (((syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv ∪
      ((syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_006 (x : Var) : Var :=
  (freshVar (((syn_csn (syn_csn (Class.cv x)))).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_007 (A : Class) : Var :=
  (freshVar (((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_008 (x : Var) : Var :=
  (freshVar (((syn_csn (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_009 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_000 A))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_010 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_011 (A : Class) : Var :=
  (freshVar (((syn_csn (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
            (Class.cv (nb079_alpha_dummy_001 A))))).fv ∪ ((syn_csn
          (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
            (Class.cv (nb079_alpha_dummy_001 A))))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_012 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv ∪
      ((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_013 (A : Class) : Var :=
  (freshVar (((syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
        (Class.cv (nb079_alpha_dummy_001 A)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_014 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cpr (Class.cv x) (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_015 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv ∪
      ((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_001 A))))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_016 (x : Var) (y : Var) : Var :=
  (freshVar
    (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_017 (A : Class) : Var :=
  (freshVar (((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv ∪
      ((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_018 (x : Var) : Var :=
  (freshVar (((syn_csn (Class.cv x))).fv ∪ ((syn_csn (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_019 (A : Class) : Var :=
  (freshVar (((syn_csn (Class.cv (nb079_alpha_dummy_001 A)))).fv ∪
      ((syn_csn (Class.cv (nb079_alpha_dummy_001 A)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_020 (y : Var) : Var :=
  (freshVar (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_021 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_001 A))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_022 (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_023 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪
      ((Class.cv (nb079_alpha_dummy_001 A))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_024 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪
      ((Class.cv (nb079_alpha_dummy_001 A))).fv) 1)

@[expose]
noncomputable def nb079_alpha_dummy_025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_026 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb079_alpha_dummy_027 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_028 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_029 (A : Class) : Var :=
  (freshVar (((Class.cab (nb079_alpha_dummy_023 A)
          (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
            (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
              (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))))).fv ∪
      ((Class.cab (nb079_alpha_dummy_023 A)
          (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
            (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
              (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_030 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb079_alpha_dummy_025 x y)
          (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
              (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))))).fv ∪
      ((Class.cab (nb079_alpha_dummy_025 x y) (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
              (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_031 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_024 A))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_032 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_024 A))).fv) 1)

@[expose]
noncomputable def nb079_alpha_dummy_033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_026 x y))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_034 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_026 x y))).fv) 1)

@[expose]
noncomputable def nb079_alpha_dummy_035 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb079_alpha_dummy_031 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb079_alpha_dummy_031 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb079_alpha_dummy_031 A))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_036 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb079_alpha_dummy_033 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb079_alpha_dummy_033 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb079_alpha_dummy_033 x y))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_037 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_038 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb079_alpha_dummy_039 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb079_alpha_dummy_040 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_041 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb079_alpha_dummy_042 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb079_alpha_dummy_043 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb079_alpha_dummy_038 A))
          (Class.cv (nb079_alpha_dummy_039 A)))).fv ∪
      ((syn_cnin (Class.cv (nb079_alpha_dummy_038 A)) (Class.cv (nb079_alpha_dummy_039 A)))).fv)
    0)

@[expose]
noncomputable def nb079_alpha_dummy_044 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y))
          (Class.cv (nb079_alpha_dummy_042 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y))
          (Class.cv (nb079_alpha_dummy_042 x y)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_045 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪
      ((Class.cv (nb079_alpha_dummy_039 A))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_046 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪
      ((Class.cv (nb079_alpha_dummy_042 x y))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_047 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb079_alpha_dummy_038 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb079_alpha_dummy_039 A)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_048 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb079_alpha_dummy_041 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb079_alpha_dummy_042 x y)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_049 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪
      ((Class.cv (nb079_alpha_dummy_038 A))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_050 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪
      ((Class.cv (nb079_alpha_dummy_041 x y))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_051 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_039 A))).fv ∪
      ((Class.cv (nb079_alpha_dummy_039 A))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079_alpha_dummy_042 x y))).fv ∪
      ((Class.cv (nb079_alpha_dummy_042 x y))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_053 (A : Class) : Var :=
  (freshVar (((Class.cab (nb079_alpha_dummy_023 A)
          (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
              (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_023 A)
          (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
              (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_054 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb079_alpha_dummy_025 x y)
          (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
              (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_025 x y)
          (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
              (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_055 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_056 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_057 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))).fv ∪
      ((syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))).fv) 0)

@[expose]
noncomputable def nb079_alpha_dummy_058 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))).fv) 0)

theorem nb079_fresh_000 (A : Class) :
    (nb079_alpha_dummy_029 A) ∉
      (((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))))).fv ∪
        ((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))))).fv) :=
  by
  simpa only [nb079_alpha_dummy_029] using
    freshVar_not_mem
      (((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))))).fv ∪
        ((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))))).fv)
      0

theorem nb079_fresh_001 (A : Class) :
    (nb079_alpha_dummy_053 A) ∉
      (((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb079_alpha_dummy_053] using
    freshVar_not_mem
      (((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb079_fresh_002 (x : Var) (y : Var) :
    (nb079_alpha_dummy_030 x y) ∉
      (((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))))).fv ∪
        ((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))))).fv) :=
  by
  simpa only [nb079_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))))).fv ∪
        ((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))))).fv)
      0

theorem nb079_fresh_003 (x : Var) (y : Var) :
    (nb079_alpha_dummy_054 x y) ∉
      (((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb079_alpha_dummy_054] using
    freshVar_not_mem
      (((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb079_fresh_004 (A : Class) :
    (nb079_alpha_dummy_009 A) ∉ (((Class.cv (nb079_alpha_dummy_000 A))).fv) := by
  simpa only [nb079_alpha_dummy_009] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_000 A))).fv) 0

theorem nb079_fresh_005 (A : Class) :
    (nb079_alpha_dummy_023 A) ∉
      (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_001 A))).fv) :=
  by
  simpa only [nb079_alpha_dummy_023] using
    freshVar_not_mem
      (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_001 A))).fv)
      0

theorem nb079_fresh_006 (A : Class) :
    (nb079_alpha_dummy_024 A) ∉
      (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_001 A))).fv) :=
  by
  simpa only [nb079_alpha_dummy_024] using
    freshVar_not_mem
      (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_001 A))).fv)
      1

theorem nb079_distinct_007 (A : Class) :
    (nb079_alpha_dummy_023 A) ≠ (nb079_alpha_dummy_024 A) := by
  simpa only [nb079_alpha_dummy_023, nb079_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪
        ((Class.cv (nb079_alpha_dummy_001 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb079_fresh_008 (A : Class) :
    (nb079_alpha_dummy_021 A) ∉ (((Class.cv (nb079_alpha_dummy_001 A))).fv) := by
  simpa only [nb079_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_001 A))).fv) 0

theorem nb079_fresh_009 (A : Class) :
    (nb079_alpha_dummy_031 A) ∉ (((Class.cv (nb079_alpha_dummy_024 A))).fv) := by
  simpa only [nb079_alpha_dummy_031] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_024 A))).fv) 0

theorem nb079_fresh_010 (A : Class) :
    (nb079_alpha_dummy_032 A) ∉ (((Class.cv (nb079_alpha_dummy_024 A))).fv) := by
  simpa only [nb079_alpha_dummy_032] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_024 A))).fv) 1

theorem nb079_distinct_011 (A : Class) :
    (nb079_alpha_dummy_031 A) ≠ (nb079_alpha_dummy_032 A) := by
  simpa only [nb079_alpha_dummy_031, nb079_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb079_alpha_dummy_024 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb079_fresh_012 (x : Var) (y : Var) :
    (nb079_alpha_dummy_033 x y) ∉ (((Class.cv (nb079_alpha_dummy_026 x y))).fv) := by
  simpa only [nb079_alpha_dummy_033] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_026 x y))).fv) 0

theorem nb079_fresh_013 (x : Var) (y : Var) :
    (nb079_alpha_dummy_034 x y) ∉ (((Class.cv (nb079_alpha_dummy_026 x y))).fv) := by
  simpa only [nb079_alpha_dummy_034] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_026 x y))).fv) 1

theorem nb079_distinct_014 (x : Var) (y : Var) :
    (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_034 x y) := by
  simpa only [nb079_alpha_dummy_033, nb079_alpha_dummy_034] using
    (freshVar_injective (((Class.cv (nb079_alpha_dummy_026 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb079_fresh_015 (A : Class) :
    (nb079_alpha_dummy_037 A) ∉
      (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb079_alpha_dummy_037] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb079_fresh_016 (A : Class) :
    (nb079_alpha_dummy_038 A) ∉
      (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb079_alpha_dummy_038] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb079_fresh_017 (A : Class) :
    (nb079_alpha_dummy_039 A) ∉
      (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb079_alpha_dummy_039] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb079_distinct_018 (A : Class) :
    (nb079_alpha_dummy_037 A) ≠ (nb079_alpha_dummy_038 A) := by
  simpa only [nb079_alpha_dummy_037, nb079_alpha_dummy_038] using
    (freshVar_injective (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb079_distinct_019 (A : Class) :
    (nb079_alpha_dummy_037 A) ≠ (nb079_alpha_dummy_039 A) := by
  simpa only [nb079_alpha_dummy_037, nb079_alpha_dummy_039] using
    (freshVar_injective (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb079_distinct_020 (A : Class) :
    (nb079_alpha_dummy_038 A) ≠ (nb079_alpha_dummy_039 A) := by
  simpa only [nb079_alpha_dummy_038, nb079_alpha_dummy_039] using
    (freshVar_injective (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb079_fresh_021 (x : Var) (y : Var) :
    (nb079_alpha_dummy_040 x y) ∉
      (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb079_alpha_dummy_040] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb079_fresh_022 (x : Var) (y : Var) :
    (nb079_alpha_dummy_041 x y) ∉
      (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb079_alpha_dummy_041] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb079_fresh_023 (x : Var) (y : Var) :
    (nb079_alpha_dummy_042 x y) ∉
      (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb079_alpha_dummy_042] using
    freshVar_not_mem (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb079_distinct_024 (x : Var) (y : Var) :
    (nb079_alpha_dummy_040 x y) ≠ (nb079_alpha_dummy_041 x y) := by
  simpa only [nb079_alpha_dummy_040, nb079_alpha_dummy_041] using
    (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb079_distinct_025 (x : Var) (y : Var) :
    (nb079_alpha_dummy_040 x y) ≠ (nb079_alpha_dummy_042 x y) := by
  simpa only [nb079_alpha_dummy_040, nb079_alpha_dummy_042] using
    (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb079_distinct_026 (x : Var) (y : Var) :
    (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_042 x y) := by
  simpa only [nb079_alpha_dummy_041, nb079_alpha_dummy_042] using
    (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb079_fresh_027 (A : Class) :
    (nb079_alpha_dummy_049 A) ∉
      (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_038 A))).fv) :=
  by
  simpa only [nb079_alpha_dummy_049] using
    freshVar_not_mem
      (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_038 A))).fv)
      0

theorem nb079_fresh_028 (A : Class) :
    (nb079_alpha_dummy_045 A) ∉
      (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_039 A))).fv) :=
  by
  simpa only [nb079_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_039 A))).fv)
      0

theorem nb079_fresh_029 (A : Class) :
    (nb079_alpha_dummy_051 A) ∉
      (((Class.cv (nb079_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_039 A))).fv) :=
  by
  simpa only [nb079_alpha_dummy_051] using
    freshVar_not_mem
      (((Class.cv (nb079_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_039 A))).fv)
      0

theorem nb079_fresh_030 (x : Var) (y : Var) :
    (nb079_alpha_dummy_050 x y) ∉
      (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪
        ((Class.cv (nb079_alpha_dummy_041 x y))).fv) :=
  by
  simpa only [nb079_alpha_dummy_050] using
    freshVar_not_mem
      (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪
        ((Class.cv (nb079_alpha_dummy_041 x y))).fv)
      0

theorem nb079_fresh_031 (x : Var) (y : Var) :
    (nb079_alpha_dummy_046 x y) ∉
      (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪
        ((Class.cv (nb079_alpha_dummy_042 x y))).fv) :=
  by
  simpa only [nb079_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪
        ((Class.cv (nb079_alpha_dummy_042 x y))).fv)
      0

theorem nb079_fresh_032 (x : Var) (y : Var) :
    (nb079_alpha_dummy_052 x y) ∉
      (((Class.cv (nb079_alpha_dummy_042 x y))).fv ∪
        ((Class.cv (nb079_alpha_dummy_042 x y))).fv) :=
  by
  simpa only [nb079_alpha_dummy_052] using
    freshVar_not_mem
      (((Class.cv (nb079_alpha_dummy_042 x y))).fv ∪
        ((Class.cv (nb079_alpha_dummy_042 x y))).fv)
      0

theorem nb079_fresh_033 (x : Var) : (nb079_alpha_dummy_010 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb079_alpha_dummy_010] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb079_fresh_034 (x : Var) (y : Var) :
    (nb079_alpha_dummy_025 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb079_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb079_fresh_035 (x : Var) (y : Var) :
    (nb079_alpha_dummy_026 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb079_alpha_dummy_026] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb079_distinct_036 (x : Var) (y : Var) :
    (nb079_alpha_dummy_025 x y) ≠ (nb079_alpha_dummy_026 x y) := by
  simpa only [nb079_alpha_dummy_025, nb079_alpha_dummy_026] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb079_fresh_037 (y : Var) : (nb079_alpha_dummy_022 y) ∉ (((Class.cv y)).fv) := by
  simpa only [nb079_alpha_dummy_022] using freshVar_not_mem (((Class.cv y)).fv) 0

theorem nb079_fresh_038 (A : Class) :
    (nb079_alpha_dummy_035 A) ∉
      (((Wff.classMem (Class.cv (nb079_alpha_dummy_031 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb079_alpha_dummy_031 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb079_alpha_dummy_031 A))).fv) :=
  by
  simpa only [nb079_alpha_dummy_035] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb079_alpha_dummy_031 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb079_alpha_dummy_031 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb079_alpha_dummy_031 A))).fv)
      0

theorem nb079_fresh_039 (x : Var) (y : Var) :
    (nb079_alpha_dummy_036 x y) ∉
      (((Wff.classMem (Class.cv (nb079_alpha_dummy_033 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb079_alpha_dummy_033 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb079_alpha_dummy_033 x y))).fv) :=
  by
  simpa only [nb079_alpha_dummy_036] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb079_alpha_dummy_033 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb079_alpha_dummy_033 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb079_alpha_dummy_033 x y))).fv)
      0

theorem nb079_fresh_040 (A : Class) :
    (nb079_alpha_dummy_027 A) ∉
      (((syn_ccompl (Class.cab (nb079_alpha_dummy_023 A)
              (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                  (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb079_alpha_dummy_023 A)
              (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                  (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb079_alpha_dummy_027] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb079_alpha_dummy_023 A)
              (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                  (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb079_alpha_dummy_023 A)
              (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                  (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb079_fresh_041 (x : Var) (y : Var) :
    (nb079_alpha_dummy_028 x y) ∉
      (((syn_ccompl (Class.cab (nb079_alpha_dummy_025 x y)
              (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                  (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb079_alpha_dummy_025 x y)
              (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                  (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb079_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb079_alpha_dummy_025 x y)
              (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                  (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb079_alpha_dummy_025 x y)
              (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                  (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb079_fresh_042 (A : Class) :
    (nb079_alpha_dummy_047 A) ∉
      (((syn_ccompl (Class.cv (nb079_alpha_dummy_038 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb079_alpha_dummy_039 A)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb079_alpha_dummy_038 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb079_alpha_dummy_039 A)))).fv)
      0

theorem nb079_fresh_043 (x : Var) (y : Var) :
    (nb079_alpha_dummy_048 x y) ∉
      (((syn_ccompl (Class.cv (nb079_alpha_dummy_041 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb079_alpha_dummy_042 x y)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb079_alpha_dummy_041 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb079_alpha_dummy_042 x y)))).fv)
      0

theorem nb079_fresh_044 (A : Class) :
    (nb079_alpha_dummy_055 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_055] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb079_fresh_045 (x : Var) (y : Var) :
    (nb079_alpha_dummy_056 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_056] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb079_fresh_046 (A : Class) :
    (nb079_alpha_dummy_015 A) ∉
      (((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_001 A))))).fv) :=
  by
  simpa only [nb079_alpha_dummy_015] using
    freshVar_not_mem
      (((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_001 A))))).fv)
      0

theorem nb079_fresh_047 (x : Var) (y : Var) :
    (nb079_alpha_dummy_016 x y) ∉
      (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_016] using
    freshVar_not_mem
      (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv)
      0

theorem nb079_fresh_048 (A : Class) :
    (nb079_alpha_dummy_003 A) ∉
      (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A)))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
                (Class.cv (nb079_alpha_dummy_001 A)))))).fv) :=
  by
  simpa only [nb079_alpha_dummy_003] using
    freshVar_not_mem
      (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A)))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
                (Class.cv (nb079_alpha_dummy_001 A)))))).fv)
      0

theorem nb079_fresh_049 (x : Var) (y : Var) :
    (nb079_alpha_dummy_004 x y) ∉
      (((syn_ccompl (syn_csn (syn_csn (Class.cv x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb079_alpha_dummy_004] using
    freshVar_not_mem
      (((syn_ccompl (syn_csn (syn_csn (Class.cv x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb079_fresh_050 (A : Class) :
    (nb079_alpha_dummy_043 A) ∉
      (((syn_cnin (Class.cv (nb079_alpha_dummy_038 A))
            (Class.cv (nb079_alpha_dummy_039 A)))).fv ∪
        ((syn_cnin (Class.cv (nb079_alpha_dummy_038 A))
            (Class.cv (nb079_alpha_dummy_039 A)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb079_alpha_dummy_038 A))
            (Class.cv (nb079_alpha_dummy_039 A)))).fv ∪
        ((syn_cnin (Class.cv (nb079_alpha_dummy_038 A))
            (Class.cv (nb079_alpha_dummy_039 A)))).fv)
      0

theorem nb079_fresh_051 (x : Var) (y : Var) :
    (nb079_alpha_dummy_044 x y) ∉
      (((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y))
            (Class.cv (nb079_alpha_dummy_042 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y))
            (Class.cv (nb079_alpha_dummy_042 x y)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_044] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y))
            (Class.cv (nb079_alpha_dummy_042 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y))
            (Class.cv (nb079_alpha_dummy_042 x y)))).fv)
      0

theorem nb079_fresh_052 (A : Class) :
    (nb079_alpha_dummy_057 A) ∉
      (((syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))).fv ∪
        ((syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_057] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))).fv ∪
        ((syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))).fv)
      0

theorem nb079_fresh_053 (x : Var) (y : Var) :
    (nb079_alpha_dummy_058 x y) ∉
      (((syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_058] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))).fv)
      0

theorem nb079_fresh_054 (A : Class) :
    (nb079_alpha_dummy_013 A) ∉
      (((syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
          (Class.cv (nb079_alpha_dummy_001 A)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_013] using
    freshVar_not_mem
      (((syn_cpr (Class.cv (nb079_alpha_dummy_000 A)) (Class.cv (nb079_alpha_dummy_001 A)))).fv)
      0

theorem nb079_fresh_055 (x : Var) (y : Var) :
    (nb079_alpha_dummy_014 x y) ∉ (((syn_cpr (Class.cv x) (Class.cv y))).fv) := by
  simpa only [nb079_alpha_dummy_014] using
    freshVar_not_mem (((syn_cpr (Class.cv x) (Class.cv y))).fv) 0

theorem nb079_fresh_056 (A : Class) :
    (nb079_alpha_dummy_007 A) ∉ (((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_007] using
    freshVar_not_mem (((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv) 0

theorem nb079_fresh_057 (A : Class) :
    (nb079_alpha_dummy_017 A) ∉
      (((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv ∪
        ((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_017] using
    freshVar_not_mem
      (((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv ∪
        ((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv)
      0

theorem nb079_fresh_058 (A : Class) :
    (nb079_alpha_dummy_019 A) ∉
      (((syn_csn (Class.cv (nb079_alpha_dummy_001 A)))).fv ∪
        ((syn_csn (Class.cv (nb079_alpha_dummy_001 A)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_019] using
    freshVar_not_mem
      (((syn_csn (Class.cv (nb079_alpha_dummy_001 A)))).fv ∪
        ((syn_csn (Class.cv (nb079_alpha_dummy_001 A)))).fv)
      0

theorem nb079_fresh_059 (x : Var) :
    (nb079_alpha_dummy_008 x) ∉ (((syn_csn (Class.cv x))).fv) := by
  simpa only [nb079_alpha_dummy_008] using
    freshVar_not_mem (((syn_csn (Class.cv x))).fv) 0

theorem nb079_fresh_060 (x : Var) :
    (nb079_alpha_dummy_018 x) ∉
      (((syn_csn (Class.cv x))).fv ∪ ((syn_csn (Class.cv x))).fv) :=
  by
  simpa only [nb079_alpha_dummy_018] using
    freshVar_not_mem (((syn_csn (Class.cv x))).fv ∪ ((syn_csn (Class.cv x))).fv) 0

theorem nb079_fresh_061 (y : Var) :
    (nb079_alpha_dummy_020 y) ∉
      (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) :=
  by
  simpa only [nb079_alpha_dummy_020] using
    freshVar_not_mem (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) 0

theorem nb079_fresh_062 (A : Class) :
    (nb079_alpha_dummy_011 A) ∉
      (((syn_csn (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
              (Class.cv (nb079_alpha_dummy_001 A))))).fv ∪ ((syn_csn
            (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
              (Class.cv (nb079_alpha_dummy_001 A))))).fv) :=
  by
  simpa only [nb079_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_csn (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
              (Class.cv (nb079_alpha_dummy_001 A))))).fv ∪ ((syn_csn
            (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
              (Class.cv (nb079_alpha_dummy_001 A))))).fv)
      0

theorem nb079_fresh_063 (x : Var) (y : Var) :
    (nb079_alpha_dummy_012 x y) ∉
      (((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_012] using
    freshVar_not_mem
      (((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv)
      0

theorem nb079_fresh_064 (A : Class) :
    (nb079_alpha_dummy_005 A) ∉
      (((syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv ∪
        ((syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv) :=
  by
  simpa only [nb079_alpha_dummy_005] using
    freshVar_not_mem
      (((syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv ∪
        ((syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv)
      0

theorem nb079_fresh_065 (x : Var) :
    (nb079_alpha_dummy_006 x) ∉
      (((syn_csn (syn_csn (Class.cv x)))).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) :=
  by
  simpa only [nb079_alpha_dummy_006] using
    freshVar_not_mem
      (((syn_csn (syn_csn (Class.cv x)))).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) 0

theorem nb079_fresh_066 (A : Class) : (nb079_alpha_dummy_000 A) ∉ ((A).fv) := by
  simpa only [nb079_alpha_dummy_000] using freshVar_not_mem ((A).fv) 0

theorem nb079_fresh_067 (A : Class) : (nb079_alpha_dummy_001 A) ∉ ((A).fv) := by
  simpa only [nb079_alpha_dummy_001] using freshVar_not_mem ((A).fv) 1

theorem nb079_fresh_068 (A : Class) : (nb079_alpha_dummy_002 A) ∉ ((A).fv) := by
  simpa only [nb079_alpha_dummy_002] using freshVar_not_mem ((A).fv) 2

theorem nb079_distinct_069 (A : Class) :
    (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_001 A) := by
  simpa only [nb079_alpha_dummy_000, nb079_alpha_dummy_001] using
    (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))

theorem nb079_distinct_070 (A : Class) :
    (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_002 A) := by
  simpa only [nb079_alpha_dummy_000, nb079_alpha_dummy_002] using
    (freshVar_injective ((A).fv) (i := 0) (j := 2) (by decide))

theorem nb079_distinct_071 (A : Class) :
    (nb079_alpha_dummy_001 A) ≠ (nb079_alpha_dummy_002 A) := by
  simpa only [nb079_alpha_dummy_001, nb079_alpha_dummy_002] using
    (freshVar_injective ((A).fv) (i := 1) (j := 2) (by decide))

theorem nb079_support_mem_0000 (A : Class) :
    (nb079_alpha_dummy_000 A) ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A)))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
                (Class.cv (nb079_alpha_dummy_001 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0001 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0002 (A : Class) :
    (nb079_alpha_dummy_000 A) ∈
      (((syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv ∪
        ((syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0003 (x : Var) :
    x ∈ (((syn_csn (syn_csn (Class.cv x)))).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0004 (A : Class) :
    (nb079_alpha_dummy_000 A) ∈ (((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv) :=
  by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0005 (x : Var) : x ∈ (((syn_csn (Class.cv x))).fv) :=
  by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0006 (A : Class) :
    (nb079_alpha_dummy_000 A) ∈ (((Class.cv (nb079_alpha_dummy_000 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0007 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0008 (A : Class) :
    (nb079_alpha_dummy_000 A) ∈
      (((syn_csn (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
              (Class.cv (nb079_alpha_dummy_001 A))))).fv ∪ ((syn_csn
            (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
              (Class.cv (nb079_alpha_dummy_001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0009 (x : Var) (y : Var) :
    x ∈
      (((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0010 (A : Class) :
    (nb079_alpha_dummy_000 A) ∈
      (((syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
          (Class.cv (nb079_alpha_dummy_001 A)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0011 (x : Var) (y : Var) :
    x ∈ (((syn_cpr (Class.cv x) (Class.cv y))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0012 (A : Class) :
    (nb079_alpha_dummy_000 A) ∈
      (((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0013 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0014 (A : Class) :
    (nb079_alpha_dummy_000 A) ∈
      (((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv ∪
        ((syn_csn (Class.cv (nb079_alpha_dummy_000 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0015 (x : Var) :
    x ∈ (((syn_csn (Class.cv x))).fv ∪ ((syn_csn (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0016 (A : Class) :
    (nb079_alpha_dummy_001 A) ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb079_alpha_dummy_000 A)))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
                (Class.cv (nb079_alpha_dummy_001 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0017 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0018 (A : Class) :
    (nb079_alpha_dummy_001 A) ∈
      (((syn_csn (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
              (Class.cv (nb079_alpha_dummy_001 A))))).fv ∪ ((syn_csn
            (syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
              (Class.cv (nb079_alpha_dummy_001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C079C001Part002`. -/


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

theorem nb079_support_mem_0019 (x : Var) (y : Var) :
    y ∈
      (((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0020 (A : Class) :
    (nb079_alpha_dummy_001 A) ∈
      (((syn_cpr (Class.cv (nb079_alpha_dummy_000 A))
          (Class.cv (nb079_alpha_dummy_001 A)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0021 (x : Var) (y : Var) :
    y ∈ (((syn_cpr (Class.cv x) (Class.cv y))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0022 (A : Class) :
    (nb079_alpha_dummy_001 A) ∈
      (((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0023 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0024 (A : Class) :
    (nb079_alpha_dummy_001 A) ∈
      (((syn_csn (Class.cv (nb079_alpha_dummy_001 A)))).fv ∪
        ((syn_csn (Class.cv (nb079_alpha_dummy_001 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0025 (y : Var) :
    y ∈ (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0026 (A : Class) :
    (nb079_alpha_dummy_001 A) ∈ (((Class.cv (nb079_alpha_dummy_001 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0027 (y : Var) : y ∈ (((Class.cv y)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0028 (A : Class) :
    (nb079_alpha_dummy_000 A) ∈
      (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0029 (A : Class) :
    (nb079_alpha_dummy_000 A) ∈
      (((syn_ccompl (Class.cab (nb079_alpha_dummy_023 A)
              (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                  (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb079_alpha_dummy_023 A)
              (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                  (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_023 A) from (by
          unfold nb079_alpha_dummy_023;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_024 A) from (by
            unfold nb079_alpha_dummy_024;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0030 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0031 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb079_alpha_dummy_025 x y)
              (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                  (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb079_alpha_dummy_025 x y)
              (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                  (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb079_alpha_dummy_025 x y) from (by
          unfold nb079_alpha_dummy_025;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb079_alpha_dummy_026 x y) from (by
            unfold nb079_alpha_dummy_026;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0032 (A : Class) :
    (nb079_alpha_dummy_000 A) ∈
      (((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))))).fv ∪
        ((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_023 A) from (by
          unfold nb079_alpha_dummy_023;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_024 A) from (by
            unfold nb079_alpha_dummy_024;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0033 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))))).fv ∪
        ((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb079_alpha_dummy_025 x y) from (by
          unfold nb079_alpha_dummy_025;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb079_alpha_dummy_026 x y) from (by
            unfold nb079_alpha_dummy_026;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0034 (A : Class) :
    (nb079_alpha_dummy_024 A) ∈ (((Class.cv (nb079_alpha_dummy_024 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0035 (x : Var) (y : Var) :
    (nb079_alpha_dummy_026 x y) ∈ (((Class.cv (nb079_alpha_dummy_026 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0036 (A : Class) :
    (nb079_alpha_dummy_031 A) ∈
      (((Wff.classMem (Class.cv (nb079_alpha_dummy_031 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb079_alpha_dummy_031 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb079_alpha_dummy_031 A))).fv) :=
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

theorem nb079_support_mem_0037 (x : Var) (y : Var) :
    (nb079_alpha_dummy_033 x y) ∈
      (((Wff.classMem (Class.cv (nb079_alpha_dummy_033 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb079_alpha_dummy_033 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb079_alpha_dummy_033 x y))).fv) :=
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

theorem nb079_support_mem_0038 (A : Class) :
    (nb079_alpha_dummy_031 A) ∈
      (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0039 (x : Var) (y : Var) :
    (nb079_alpha_dummy_033 x y) ∈
      (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0040 (A : Class) :
    (nb079_alpha_dummy_038 A) ∈
      (((syn_cnin (Class.cv (nb079_alpha_dummy_038 A))
            (Class.cv (nb079_alpha_dummy_039 A)))).fv ∪
        ((syn_cnin (Class.cv (nb079_alpha_dummy_038 A))
            (Class.cv (nb079_alpha_dummy_039 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0041 (x : Var) (y : Var) :
    (nb079_alpha_dummy_041 x y) ∈
      (((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y))
            (Class.cv (nb079_alpha_dummy_042 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y))
            (Class.cv (nb079_alpha_dummy_042 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0042 (A : Class) :
    (nb079_alpha_dummy_038 A) ∈
      (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_039 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0043 (x : Var) (y : Var) :
    (nb079_alpha_dummy_041 x y) ∈
      (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪
        ((Class.cv (nb079_alpha_dummy_042 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0044 (A : Class) :
    (nb079_alpha_dummy_039 A) ∈
      (((syn_cnin (Class.cv (nb079_alpha_dummy_038 A))
            (Class.cv (nb079_alpha_dummy_039 A)))).fv ∪
        ((syn_cnin (Class.cv (nb079_alpha_dummy_038 A))
            (Class.cv (nb079_alpha_dummy_039 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0045 (x : Var) (y : Var) :
    (nb079_alpha_dummy_042 x y) ∈
      (((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y))
            (Class.cv (nb079_alpha_dummy_042 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y))
            (Class.cv (nb079_alpha_dummy_042 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0046 (A : Class) :
    (nb079_alpha_dummy_039 A) ∈
      (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_039 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0047 (x : Var) (y : Var) :
    (nb079_alpha_dummy_042 x y) ∈
      (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪
        ((Class.cv (nb079_alpha_dummy_042 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0048 (A : Class) :
    (nb079_alpha_dummy_038 A) ∈
      (((syn_ccompl (Class.cv (nb079_alpha_dummy_038 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb079_alpha_dummy_039 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0049 (x : Var) (y : Var) :
    (nb079_alpha_dummy_041 x y) ∈
      (((syn_ccompl (Class.cv (nb079_alpha_dummy_041 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb079_alpha_dummy_042 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0050 (A : Class) :
    (nb079_alpha_dummy_038 A) ∈
      (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_038 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0051 (x : Var) (y : Var) :
    (nb079_alpha_dummy_041 x y) ∈
      (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪
        ((Class.cv (nb079_alpha_dummy_041 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0052 (A : Class) :
    (nb079_alpha_dummy_039 A) ∈
      (((syn_ccompl (Class.cv (nb079_alpha_dummy_038 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb079_alpha_dummy_039 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0053 (x : Var) (y : Var) :
    (nb079_alpha_dummy_042 x y) ∈
      (((syn_ccompl (Class.cv (nb079_alpha_dummy_041 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb079_alpha_dummy_042 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0054 (A : Class) :
    (nb079_alpha_dummy_039 A) ∈
      (((Class.cv (nb079_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_039 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0055 (x : Var) (y : Var) :
    (nb079_alpha_dummy_042 x y) ∈
      (((Class.cv (nb079_alpha_dummy_042 x y))).fv ∪
        ((Class.cv (nb079_alpha_dummy_042 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0056 (A : Class) :
    (nb079_alpha_dummy_001 A) ∈
      (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0057 (A : Class) :
    (nb079_alpha_dummy_001 A) ∈
      (((syn_ccompl (Class.cab (nb079_alpha_dummy_023 A)
              (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                  (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb079_alpha_dummy_023 A)
              (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                  (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb079_alpha_dummy_001 A) ≠ (nb079_alpha_dummy_023 A) from (by
          unfold nb079_alpha_dummy_023;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb079_alpha_dummy_001 A) ≠ (nb079_alpha_dummy_024 A) from (by
            unfold nb079_alpha_dummy_024;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0058 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0059 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb079_alpha_dummy_025 x y)
              (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                  (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb079_alpha_dummy_025 x y)
              (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                  (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb079_alpha_dummy_025 x y) from (by
          unfold nb079_alpha_dummy_025;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb079_alpha_dummy_026 x y) from (by
            unfold nb079_alpha_dummy_026;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0060 (A : Class) :
    (nb079_alpha_dummy_001 A) ∈
      (((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_023 A)
            (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb079_alpha_dummy_001 A) ≠ (nb079_alpha_dummy_023 A) from (by
          unfold nb079_alpha_dummy_023;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb079_alpha_dummy_001 A) ≠ (nb079_alpha_dummy_024 A) from (by
            unfold nb079_alpha_dummy_024;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0061 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_025 x y)
            (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y))
                (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb079_alpha_dummy_025 x y) from (by
          unfold nb079_alpha_dummy_025;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb079_alpha_dummy_026 x y) from (by
            unfold nb079_alpha_dummy_026;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0062 (A : Class) :
    (nb079_alpha_dummy_024 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0063 (x : Var) (y : Var) :
    (nb079_alpha_dummy_026 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0064 (A : Class) :
    (nb079_alpha_dummy_024 A) ∈
      (((syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))).fv ∪
        ((syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0065 (x : Var) (y : Var) :
    (nb079_alpha_dummy_026 x y) ∈
      (((syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
