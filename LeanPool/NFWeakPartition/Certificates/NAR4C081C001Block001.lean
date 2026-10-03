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

/-! Certificates from `NAR4C081C001Part001`. -/


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
noncomputable def nb081_alpha_dummy_000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

@[expose]
noncomputable def nb081_alpha_dummy_002 (A : Class) : Var :=
  (freshVar (({(nb081_alpha_dummy_000 A)} : Finset Var) ∪
        ({(nb081_alpha_dummy_001 A)} : Finset Var) ∪ ((Wff.classMem
          (syn_copk (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A)))
          A)).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_003 (x : Var) (y : Var) (A : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ((Wff.classMem (syn_copk (Class.cv x) (Class.cv y)) A)).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_004 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪
      ((Class.cv (nb081_alpha_dummy_001 A))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_005 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪
      ((Class.cv (nb081_alpha_dummy_001 A))).fv) 1)

@[expose]
noncomputable def nb081_alpha_dummy_006 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_007 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb081_alpha_dummy_008 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_009 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_010 (A : Class) : Var :=
  (freshVar (((Class.cab (nb081_alpha_dummy_004 A)
          (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
            (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
              (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))))).fv ∪
      ((Class.cab (nb081_alpha_dummy_004 A)
          (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
            (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
              (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_011 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb081_alpha_dummy_006 x y)
          (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
              (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))))).fv ∪
      ((Class.cab (nb081_alpha_dummy_006 x y) (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
              (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_012 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_005 A))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_013 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_005 A))).fv) 1)

@[expose]
noncomputable def nb081_alpha_dummy_014 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_007 x y))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_015 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_007 x y))).fv) 1)

@[expose]
noncomputable def nb081_alpha_dummy_016 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb081_alpha_dummy_012 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb081_alpha_dummy_012 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb081_alpha_dummy_012 A))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_017 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb081_alpha_dummy_014 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb081_alpha_dummy_014 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb081_alpha_dummy_014 x y))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_018 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_019 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb081_alpha_dummy_020 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb081_alpha_dummy_021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_022 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb081_alpha_dummy_023 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb081_alpha_dummy_024 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb081_alpha_dummy_019 A))
          (Class.cv (nb081_alpha_dummy_020 A)))).fv ∪
      ((syn_cnin (Class.cv (nb081_alpha_dummy_019 A)) (Class.cv (nb081_alpha_dummy_020 A)))).fv)
    0)

@[expose]
noncomputable def nb081_alpha_dummy_025 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y))
          (Class.cv (nb081_alpha_dummy_023 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y))
          (Class.cv (nb081_alpha_dummy_023 x y)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_026 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_019 A))).fv ∪
      ((Class.cv (nb081_alpha_dummy_020 A))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_027 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪
      ((Class.cv (nb081_alpha_dummy_023 x y))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_028 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb081_alpha_dummy_019 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb081_alpha_dummy_020 A)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_029 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb081_alpha_dummy_022 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb081_alpha_dummy_023 x y)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_030 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_019 A))).fv ∪
      ((Class.cv (nb081_alpha_dummy_019 A))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪
      ((Class.cv (nb081_alpha_dummy_022 x y))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_032 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_020 A))).fv ∪
      ((Class.cv (nb081_alpha_dummy_020 A))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_023 x y))).fv ∪
      ((Class.cv (nb081_alpha_dummy_023 x y))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_034 (A : Class) : Var :=
  (freshVar (((Class.cab (nb081_alpha_dummy_004 A)
          (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
              (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb081_alpha_dummy_004 A)
          (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
              (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_035 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb081_alpha_dummy_006 x y)
          (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
              (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb081_alpha_dummy_006 x y)
          (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
              (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_036 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_037 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_038 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))).fv ∪
      ((syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_039 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_040 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A)))))).fv ∪
      ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A)))))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_041 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_cpr (Class.cv x) (Class.cv y))))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_042 (A : Class) : Var :=
  (freshVar (((syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪
      ((syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_043 (x : Var) : Var :=
  (freshVar (((syn_csn (syn_csn (Class.cv x)))).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_044 (A : Class) : Var :=
  (freshVar (((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_045 (x : Var) : Var :=
  (freshVar (((syn_csn (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_046 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_000 A))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_047 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_048 (A : Class) : Var :=
  (freshVar (((syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
            (Class.cv (nb081_alpha_dummy_001 A))))).fv ∪ ((syn_csn
          (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
            (Class.cv (nb081_alpha_dummy_001 A))))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_049 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv ∪
      ((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_050 (A : Class) : Var :=
  (freshVar (((syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
        (Class.cv (nb081_alpha_dummy_001 A)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_051 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cpr (Class.cv x) (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_052 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪
      ((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_001 A))))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_053 (x : Var) (y : Var) : Var :=
  (freshVar
    (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_054 (A : Class) : Var :=
  (freshVar (((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv ∪
      ((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_055 (x : Var) : Var :=
  (freshVar (((syn_csn (Class.cv x))).fv ∪ ((syn_csn (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_056 (A : Class) : Var :=
  (freshVar (((syn_csn (Class.cv (nb081_alpha_dummy_001 A)))).fv ∪
      ((syn_csn (Class.cv (nb081_alpha_dummy_001 A)))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_057 (y : Var) : Var :=
  (freshVar (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_058 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081_alpha_dummy_001 A))).fv) 0)

@[expose]
noncomputable def nb081_alpha_dummy_059 (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv) 0)

theorem nb081_fresh_000 (A : Class) :
    (nb081_alpha_dummy_010 A) ∉
      (((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))))).fv ∪
        ((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))))).fv) :=
  by
  simpa only [nb081_alpha_dummy_010] using
    freshVar_not_mem
      (((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))))).fv ∪
        ((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))))).fv)
      0

theorem nb081_fresh_001 (A : Class) :
    (nb081_alpha_dummy_034 A) ∉
      (((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb081_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb081_fresh_002 (x : Var) (y : Var) :
    (nb081_alpha_dummy_011 x y) ∉
      (((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))))).fv ∪
        ((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))))).fv) :=
  by
  simpa only [nb081_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))))).fv ∪
        ((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))))).fv)
      0

theorem nb081_fresh_003 (x : Var) (y : Var) :
    (nb081_alpha_dummy_035 x y) ∉
      (((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb081_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb081_fresh_004 (A : Class) :
    (nb081_alpha_dummy_046 A) ∉ (((Class.cv (nb081_alpha_dummy_000 A))).fv) := by
  simpa only [nb081_alpha_dummy_046] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_000 A))).fv) 0

theorem nb081_fresh_005 (A : Class) :
    (nb081_alpha_dummy_004 A) ∉
      (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_001 A))).fv) :=
  by
  simpa only [nb081_alpha_dummy_004] using
    freshVar_not_mem
      (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_001 A))).fv)
      0

theorem nb081_fresh_006 (A : Class) :
    (nb081_alpha_dummy_005 A) ∉
      (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_001 A))).fv) :=
  by
  simpa only [nb081_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_001 A))).fv)
      1

theorem nb081_distinct_007 (A : Class) :
    (nb081_alpha_dummy_004 A) ≠ (nb081_alpha_dummy_005 A) := by
  simpa only [nb081_alpha_dummy_004, nb081_alpha_dummy_005] using
    (freshVar_injective (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪
        ((Class.cv (nb081_alpha_dummy_001 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb081_fresh_008 (A : Class) :
    (nb081_alpha_dummy_058 A) ∉ (((Class.cv (nb081_alpha_dummy_001 A))).fv) := by
  simpa only [nb081_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_001 A))).fv) 0

theorem nb081_fresh_009 (A : Class) :
    (nb081_alpha_dummy_012 A) ∉ (((Class.cv (nb081_alpha_dummy_005 A))).fv) := by
  simpa only [nb081_alpha_dummy_012] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_005 A))).fv) 0

theorem nb081_fresh_010 (A : Class) :
    (nb081_alpha_dummy_013 A) ∉ (((Class.cv (nb081_alpha_dummy_005 A))).fv) := by
  simpa only [nb081_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_005 A))).fv) 1

theorem nb081_distinct_011 (A : Class) :
    (nb081_alpha_dummy_012 A) ≠ (nb081_alpha_dummy_013 A) := by
  simpa only [nb081_alpha_dummy_012, nb081_alpha_dummy_013] using
    (freshVar_injective (((Class.cv (nb081_alpha_dummy_005 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb081_fresh_012 (x : Var) (y : Var) :
    (nb081_alpha_dummy_014 x y) ∉ (((Class.cv (nb081_alpha_dummy_007 x y))).fv) := by
  simpa only [nb081_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_007 x y))).fv) 0

theorem nb081_fresh_013 (x : Var) (y : Var) :
    (nb081_alpha_dummy_015 x y) ∉ (((Class.cv (nb081_alpha_dummy_007 x y))).fv) := by
  simpa only [nb081_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_007 x y))).fv) 1

theorem nb081_distinct_014 (x : Var) (y : Var) :
    (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_015 x y) := by
  simpa only [nb081_alpha_dummy_014, nb081_alpha_dummy_015] using
    (freshVar_injective (((Class.cv (nb081_alpha_dummy_007 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb081_fresh_015 (A : Class) :
    (nb081_alpha_dummy_018 A) ∉
      (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb081_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb081_fresh_016 (A : Class) :
    (nb081_alpha_dummy_019 A) ∉
      (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb081_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb081_fresh_017 (A : Class) :
    (nb081_alpha_dummy_020 A) ∉
      (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb081_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb081_distinct_018 (A : Class) :
    (nb081_alpha_dummy_018 A) ≠ (nb081_alpha_dummy_019 A) := by
  simpa only [nb081_alpha_dummy_018, nb081_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb081_distinct_019 (A : Class) :
    (nb081_alpha_dummy_018 A) ≠ (nb081_alpha_dummy_020 A) := by
  simpa only [nb081_alpha_dummy_018, nb081_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb081_distinct_020 (A : Class) :
    (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_020 A) := by
  simpa only [nb081_alpha_dummy_019, nb081_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb081_fresh_021 (x : Var) (y : Var) :
    (nb081_alpha_dummy_021 x y) ∉
      (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb081_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb081_fresh_022 (x : Var) (y : Var) :
    (nb081_alpha_dummy_022 x y) ∉
      (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb081_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb081_fresh_023 (x : Var) (y : Var) :
    (nb081_alpha_dummy_023 x y) ∉
      (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb081_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb081_distinct_024 (x : Var) (y : Var) :
    (nb081_alpha_dummy_021 x y) ≠ (nb081_alpha_dummy_022 x y) := by
  simpa only [nb081_alpha_dummy_021, nb081_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb081_distinct_025 (x : Var) (y : Var) :
    (nb081_alpha_dummy_021 x y) ≠ (nb081_alpha_dummy_023 x y) := by
  simpa only [nb081_alpha_dummy_021, nb081_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb081_distinct_026 (x : Var) (y : Var) :
    (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_023 x y) := by
  simpa only [nb081_alpha_dummy_022, nb081_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb081_fresh_027 (A : Class) :
    (nb081_alpha_dummy_030 A) ∉
      (((Class.cv (nb081_alpha_dummy_019 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_019 A))).fv) :=
  by
  simpa only [nb081_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb081_alpha_dummy_019 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_019 A))).fv)
      0

theorem nb081_fresh_028 (A : Class) :
    (nb081_alpha_dummy_026 A) ∉
      (((Class.cv (nb081_alpha_dummy_019 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_020 A))).fv) :=
  by
  simpa only [nb081_alpha_dummy_026] using
    freshVar_not_mem
      (((Class.cv (nb081_alpha_dummy_019 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_020 A))).fv)
      0

theorem nb081_fresh_029 (A : Class) :
    (nb081_alpha_dummy_032 A) ∉
      (((Class.cv (nb081_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_020 A))).fv) :=
  by
  simpa only [nb081_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb081_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_020 A))).fv)
      0

theorem nb081_fresh_030 (x : Var) (y : Var) :
    (nb081_alpha_dummy_031 x y) ∉
      (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb081_alpha_dummy_022 x y))).fv) :=
  by
  simpa only [nb081_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb081_alpha_dummy_022 x y))).fv)
      0

theorem nb081_fresh_031 (x : Var) (y : Var) :
    (nb081_alpha_dummy_027 x y) ∉
      (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb081_alpha_dummy_023 x y))).fv) :=
  by
  simpa only [nb081_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb081_alpha_dummy_023 x y))).fv)
      0

theorem nb081_fresh_032 (x : Var) (y : Var) :
    (nb081_alpha_dummy_033 x y) ∉
      (((Class.cv (nb081_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb081_alpha_dummy_023 x y))).fv) :=
  by
  simpa only [nb081_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb081_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb081_alpha_dummy_023 x y))).fv)
      0

theorem nb081_fresh_033 (x : Var) : (nb081_alpha_dummy_047 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb081_alpha_dummy_047] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb081_fresh_034 (x : Var) (y : Var) :
    (nb081_alpha_dummy_006 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb081_alpha_dummy_006] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb081_fresh_035 (x : Var) (y : Var) :
    (nb081_alpha_dummy_007 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb081_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb081_distinct_036 (x : Var) (y : Var) :
    (nb081_alpha_dummy_006 x y) ≠ (nb081_alpha_dummy_007 x y) := by
  simpa only [nb081_alpha_dummy_006, nb081_alpha_dummy_007] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb081_fresh_037 (y : Var) : (nb081_alpha_dummy_059 y) ∉ (((Class.cv y)).fv) := by
  simpa only [nb081_alpha_dummy_059] using freshVar_not_mem (((Class.cv y)).fv) 0

theorem nb081_fresh_038 (A : Class) :
    (nb081_alpha_dummy_016 A) ∉
      (((Wff.classMem (Class.cv (nb081_alpha_dummy_012 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb081_alpha_dummy_012 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb081_alpha_dummy_012 A))).fv) :=
  by
  simpa only [nb081_alpha_dummy_016] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb081_alpha_dummy_012 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb081_alpha_dummy_012 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb081_alpha_dummy_012 A))).fv)
      0

theorem nb081_fresh_039 (x : Var) (y : Var) :
    (nb081_alpha_dummy_017 x y) ∉
      (((Wff.classMem (Class.cv (nb081_alpha_dummy_014 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb081_alpha_dummy_014 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb081_alpha_dummy_014 x y))).fv) :=
  by
  simpa only [nb081_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb081_alpha_dummy_014 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb081_alpha_dummy_014 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb081_alpha_dummy_014 x y))).fv)
      0

theorem nb081_fresh_040 (A : Class) :
    (nb081_alpha_dummy_008 A) ∉
      (((syn_ccompl (Class.cab (nb081_alpha_dummy_004 A)
              (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                  (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb081_alpha_dummy_004 A)
              (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                  (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb081_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb081_alpha_dummy_004 A)
              (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                  (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb081_alpha_dummy_004 A)
              (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                  (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb081_fresh_041 (x : Var) (y : Var) :
    (nb081_alpha_dummy_009 x y) ∉
      (((syn_ccompl (Class.cab (nb081_alpha_dummy_006 x y)
              (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                  (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb081_alpha_dummy_006 x y)
              (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                  (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb081_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb081_alpha_dummy_006 x y)
              (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                  (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb081_alpha_dummy_006 x y)
              (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                  (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb081_fresh_042 (A : Class) :
    (nb081_alpha_dummy_028 A) ∉
      (((syn_ccompl (Class.cv (nb081_alpha_dummy_019 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb081_alpha_dummy_020 A)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb081_alpha_dummy_019 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb081_alpha_dummy_020 A)))).fv)
      0

theorem nb081_fresh_043 (x : Var) (y : Var) :
    (nb081_alpha_dummy_029 x y) ∉
      (((syn_ccompl (Class.cv (nb081_alpha_dummy_022 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb081_alpha_dummy_023 x y)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb081_alpha_dummy_022 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb081_alpha_dummy_023 x y)))).fv)
      0

theorem nb081_fresh_044 (A : Class) :
    (nb081_alpha_dummy_036 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_036] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb081_fresh_045 (x : Var) (y : Var) :
    (nb081_alpha_dummy_037 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb081_fresh_046 (A : Class) :
    (nb081_alpha_dummy_052 A) ∉
      (((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_001 A))))).fv) :=
  by
  simpa only [nb081_alpha_dummy_052] using
    freshVar_not_mem
      (((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_001 A))))).fv)
      0

theorem nb081_fresh_047 (x : Var) (y : Var) :
    (nb081_alpha_dummy_053 x y) ∉
      (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_053] using
    freshVar_not_mem
      (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv)
      0

theorem nb081_fresh_048 (A : Class) :
    (nb081_alpha_dummy_040 A) ∉
      (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A)))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
                (Class.cv (nb081_alpha_dummy_001 A)))))).fv) :=
  by
  simpa only [nb081_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A)))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
                (Class.cv (nb081_alpha_dummy_001 A)))))).fv)
      0

theorem nb081_fresh_049 (x : Var) (y : Var) :
    (nb081_alpha_dummy_041 x y) ∉
      (((syn_ccompl (syn_csn (syn_csn (Class.cv x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb081_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_ccompl (syn_csn (syn_csn (Class.cv x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb081_fresh_050 (A : Class) :
    (nb081_alpha_dummy_024 A) ∉
      (((syn_cnin (Class.cv (nb081_alpha_dummy_019 A))
            (Class.cv (nb081_alpha_dummy_020 A)))).fv ∪
        ((syn_cnin (Class.cv (nb081_alpha_dummy_019 A))
            (Class.cv (nb081_alpha_dummy_020 A)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_024] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb081_alpha_dummy_019 A))
            (Class.cv (nb081_alpha_dummy_020 A)))).fv ∪
        ((syn_cnin (Class.cv (nb081_alpha_dummy_019 A))
            (Class.cv (nb081_alpha_dummy_020 A)))).fv)
      0

theorem nb081_fresh_051 (x : Var) (y : Var) :
    (nb081_alpha_dummy_025 x y) ∉
      (((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y))
            (Class.cv (nb081_alpha_dummy_023 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y))
            (Class.cv (nb081_alpha_dummy_023 x y)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y))
            (Class.cv (nb081_alpha_dummy_023 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y))
            (Class.cv (nb081_alpha_dummy_023 x y)))).fv)
      0

theorem nb081_fresh_052 (A : Class) :
    (nb081_alpha_dummy_038 A) ∉
      (((syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))).fv ∪
        ((syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))).fv ∪
        ((syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))).fv)
      0

theorem nb081_fresh_053 (x : Var) (y : Var) :
    (nb081_alpha_dummy_039 x y) ∉
      (((syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))).fv)
      0

theorem nb081_fresh_054 (A : Class) :
    (nb081_alpha_dummy_050 A) ∉
      (((syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
          (Class.cv (nb081_alpha_dummy_001 A)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_050] using
    freshVar_not_mem
      (((syn_cpr (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A)))).fv)
      0

theorem nb081_fresh_055 (x : Var) (y : Var) :
    (nb081_alpha_dummy_051 x y) ∉ (((syn_cpr (Class.cv x) (Class.cv y))).fv) := by
  simpa only [nb081_alpha_dummy_051] using
    freshVar_not_mem (((syn_cpr (Class.cv x) (Class.cv y))).fv) 0

theorem nb081_fresh_056 (A : Class) :
    (nb081_alpha_dummy_044 A) ∉ (((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_044] using
    freshVar_not_mem (((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv) 0

theorem nb081_fresh_057 (A : Class) :
    (nb081_alpha_dummy_054 A) ∉
      (((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv ∪
        ((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_054] using
    freshVar_not_mem
      (((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv ∪
        ((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv)
      0

theorem nb081_fresh_058 (A : Class) :
    (nb081_alpha_dummy_056 A) ∉
      (((syn_csn (Class.cv (nb081_alpha_dummy_001 A)))).fv ∪
        ((syn_csn (Class.cv (nb081_alpha_dummy_001 A)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_056] using
    freshVar_not_mem
      (((syn_csn (Class.cv (nb081_alpha_dummy_001 A)))).fv ∪
        ((syn_csn (Class.cv (nb081_alpha_dummy_001 A)))).fv)
      0

theorem nb081_fresh_059 (x : Var) :
    (nb081_alpha_dummy_045 x) ∉ (((syn_csn (Class.cv x))).fv) := by
  simpa only [nb081_alpha_dummy_045] using
    freshVar_not_mem (((syn_csn (Class.cv x))).fv) 0

theorem nb081_fresh_060 (x : Var) :
    (nb081_alpha_dummy_055 x) ∉
      (((syn_csn (Class.cv x))).fv ∪ ((syn_csn (Class.cv x))).fv) :=
  by
  simpa only [nb081_alpha_dummy_055] using
    freshVar_not_mem (((syn_csn (Class.cv x))).fv ∪ ((syn_csn (Class.cv x))).fv) 0

theorem nb081_fresh_061 (y : Var) :
    (nb081_alpha_dummy_057 y) ∉
      (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) :=
  by
  simpa only [nb081_alpha_dummy_057] using
    freshVar_not_mem (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) 0

theorem nb081_fresh_062 (A : Class) :
    (nb081_alpha_dummy_048 A) ∉
      (((syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))))).fv ∪ ((syn_csn
            (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))))).fv) :=
  by
  simpa only [nb081_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))))).fv ∪ ((syn_csn
            (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))))).fv)
      0

theorem nb081_fresh_063 (x : Var) (y : Var) :
    (nb081_alpha_dummy_049 x y) ∉
      (((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv)
      0

theorem nb081_fresh_064 (A : Class) :
    (nb081_alpha_dummy_042 A) ∉
      (((syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪
        ((syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv) :=
  by
  simpa only [nb081_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪
        ((syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv)
      0

theorem nb081_fresh_065 (x : Var) :
    (nb081_alpha_dummy_043 x) ∉
      (((syn_csn (syn_csn (Class.cv x)))).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) :=
  by
  simpa only [nb081_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_csn (syn_csn (Class.cv x)))).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) 0

theorem nb081_fresh_066 (A : Class) : (nb081_alpha_dummy_000 A) ∉ ((A).fv) := by
  simpa only [nb081_alpha_dummy_000] using freshVar_not_mem ((A).fv) 0

theorem nb081_fresh_067 (A : Class) : (nb081_alpha_dummy_001 A) ∉ ((A).fv) := by
  simpa only [nb081_alpha_dummy_001] using freshVar_not_mem ((A).fv) 1

theorem nb081_distinct_068 (A : Class) :
    (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_001 A) := by
  simpa only [nb081_alpha_dummy_000, nb081_alpha_dummy_001] using
    (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))

theorem nb081_fresh_069 (A : Class) :
    (nb081_alpha_dummy_002 A) ∉
      (({(nb081_alpha_dummy_000 A)} : Finset Var) ∪ ({(nb081_alpha_dummy_001 A)} : Finset Var) ∪
        ((Wff.classMem (syn_copk (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))) A)).fv) :=
  by
  simpa only [nb081_alpha_dummy_002] using
    freshVar_not_mem
      (({(nb081_alpha_dummy_000 A)} : Finset Var) ∪ ({(nb081_alpha_dummy_001 A)} : Finset Var) ∪
        ((Wff.classMem (syn_copk (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))) A)).fv)
      0

theorem nb081_fresh_070 (x : Var) (y : Var) (A : Class) :
    (nb081_alpha_dummy_003 x y A) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classMem (syn_copk (Class.cv x) (Class.cv y)) A)).fv) :=
  by
  simpa only [nb081_alpha_dummy_003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classMem (syn_copk (Class.cv x) (Class.cv y)) A)).fv)
      0

theorem nb081_support_mem_0000 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈
      (({(nb081_alpha_dummy_000 A)} : Finset Var) ∪ ({(nb081_alpha_dummy_001 A)} : Finset Var) ∪
        ((Wff.classMem (syn_copk (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))) A)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0001 (x : Var) (y : Var) (A : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classMem (syn_copk (Class.cv x) (Class.cv y)) A)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0002 (A : Class) :
    (nb081_alpha_dummy_001 A) ∈
      (({(nb081_alpha_dummy_000 A)} : Finset Var) ∪ ({(nb081_alpha_dummy_001 A)} : Finset Var) ∪
        ((Wff.classMem (syn_copk (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))) A)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0003 (x : Var) (y : Var) (A : Class) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classMem (syn_copk (Class.cv x) (Class.cv y)) A)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0004 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈
      (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0005 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈
      (((syn_ccompl (Class.cab (nb081_alpha_dummy_004 A)
              (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                  (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb081_alpha_dummy_004 A)
              (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                  (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_004 A) from (by
          unfold nb081_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_005 A) from (by
            unfold nb081_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0006 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb081_alpha_dummy_006 x y)
              (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                  (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb081_alpha_dummy_006 x y)
              (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                  (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb081_alpha_dummy_006 x y) from (by
          unfold nb081_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0006 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb081_alpha_dummy_007 x y) from (by
            unfold nb081_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0006 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0008 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈
      (((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))))).fv ∪
        ((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_004 A) from (by
          unfold nb081_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_005 A) from (by
            unfold nb081_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0009 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))))).fv ∪
        ((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb081_alpha_dummy_006 x y) from (by
          unfold nb081_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0006 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb081_alpha_dummy_007 x y) from (by
            unfold nb081_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0006 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0010 (A : Class) :
    (nb081_alpha_dummy_005 A) ∈ (((Class.cv (nb081_alpha_dummy_005 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0011 (x : Var) (y : Var) :
    (nb081_alpha_dummy_007 x y) ∈ (((Class.cv (nb081_alpha_dummy_007 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0012 (A : Class) :
    (nb081_alpha_dummy_012 A) ∈
      (((Wff.classMem (Class.cv (nb081_alpha_dummy_012 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb081_alpha_dummy_012 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb081_alpha_dummy_012 A))).fv) :=
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

theorem nb081_support_mem_0013 (x : Var) (y : Var) :
    (nb081_alpha_dummy_014 x y) ∈
      (((Wff.classMem (Class.cv (nb081_alpha_dummy_014 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb081_alpha_dummy_014 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb081_alpha_dummy_014 x y))).fv) :=
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

theorem nb081_support_mem_0014 (A : Class) :
    (nb081_alpha_dummy_012 A) ∈
      (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0015 (x : Var) (y : Var) :
    (nb081_alpha_dummy_014 x y) ∈
      (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0016 (A : Class) :
    (nb081_alpha_dummy_019 A) ∈
      (((syn_cnin (Class.cv (nb081_alpha_dummy_019 A))
            (Class.cv (nb081_alpha_dummy_020 A)))).fv ∪
        ((syn_cnin (Class.cv (nb081_alpha_dummy_019 A))
            (Class.cv (nb081_alpha_dummy_020 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0017 (x : Var) (y : Var) :
    (nb081_alpha_dummy_022 x y) ∈
      (((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y))
            (Class.cv (nb081_alpha_dummy_023 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y))
            (Class.cv (nb081_alpha_dummy_023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0018 (A : Class) :
    (nb081_alpha_dummy_019 A) ∈
      (((Class.cv (nb081_alpha_dummy_019 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_020 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C081C001Part002`. -/


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

theorem nb081_support_mem_0019 (x : Var) (y : Var) :
    (nb081_alpha_dummy_022 x y) ∈
      (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb081_alpha_dummy_023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0020 (A : Class) :
    (nb081_alpha_dummy_020 A) ∈
      (((syn_cnin (Class.cv (nb081_alpha_dummy_019 A))
            (Class.cv (nb081_alpha_dummy_020 A)))).fv ∪
        ((syn_cnin (Class.cv (nb081_alpha_dummy_019 A))
            (Class.cv (nb081_alpha_dummy_020 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0021 (x : Var) (y : Var) :
    (nb081_alpha_dummy_023 x y) ∈
      (((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y))
            (Class.cv (nb081_alpha_dummy_023 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y))
            (Class.cv (nb081_alpha_dummy_023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0022 (A : Class) :
    (nb081_alpha_dummy_020 A) ∈
      (((Class.cv (nb081_alpha_dummy_019 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_020 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0023 (x : Var) (y : Var) :
    (nb081_alpha_dummy_023 x y) ∈
      (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb081_alpha_dummy_023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0024 (A : Class) :
    (nb081_alpha_dummy_019 A) ∈
      (((syn_ccompl (Class.cv (nb081_alpha_dummy_019 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb081_alpha_dummy_020 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0025 (x : Var) (y : Var) :
    (nb081_alpha_dummy_022 x y) ∈
      (((syn_ccompl (Class.cv (nb081_alpha_dummy_022 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb081_alpha_dummy_023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0026 (A : Class) :
    (nb081_alpha_dummy_019 A) ∈
      (((Class.cv (nb081_alpha_dummy_019 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_019 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0027 (x : Var) (y : Var) :
    (nb081_alpha_dummy_022 x y) ∈
      (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb081_alpha_dummy_022 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0028 (A : Class) :
    (nb081_alpha_dummy_020 A) ∈
      (((syn_ccompl (Class.cv (nb081_alpha_dummy_019 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb081_alpha_dummy_020 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0029 (x : Var) (y : Var) :
    (nb081_alpha_dummy_023 x y) ∈
      (((syn_ccompl (Class.cv (nb081_alpha_dummy_022 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb081_alpha_dummy_023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0030 (A : Class) :
    (nb081_alpha_dummy_020 A) ∈
      (((Class.cv (nb081_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_020 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0031 (x : Var) (y : Var) :
    (nb081_alpha_dummy_023 x y) ∈
      (((Class.cv (nb081_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb081_alpha_dummy_023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0032 (A : Class) :
    (nb081_alpha_dummy_001 A) ∈
      (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0033 (A : Class) :
    (nb081_alpha_dummy_001 A) ∈
      (((syn_ccompl (Class.cab (nb081_alpha_dummy_004 A)
              (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                  (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb081_alpha_dummy_004 A)
              (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                  (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_004 A) from (by
          unfold nb081_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_005 A) from (by
            unfold nb081_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0034 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0035 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb081_alpha_dummy_006 x y)
              (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                  (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb081_alpha_dummy_006 x y)
              (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                  (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb081_alpha_dummy_006 x y) from (by
          unfold nb081_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb081_alpha_dummy_007 x y) from (by
            unfold nb081_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0036 (A : Class) :
    (nb081_alpha_dummy_001 A) ∈
      (((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_004 A) from (by
          unfold nb081_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_005 A) from (by
            unfold nb081_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0037 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb081_alpha_dummy_006 x y) from (by
          unfold nb081_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb081_alpha_dummy_007 x y) from (by
            unfold nb081_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0038 (A : Class) :
    (nb081_alpha_dummy_005 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0039 (x : Var) (y : Var) :
    (nb081_alpha_dummy_007 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0040 (A : Class) :
    (nb081_alpha_dummy_005 A) ∈
      (((syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))).fv ∪
        ((syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0041 (x : Var) (y : Var) :
    (nb081_alpha_dummy_007 x y) ∈
      (((syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0042 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A)))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
                (Class.cv (nb081_alpha_dummy_001 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0043 (x : Var) (y : Var) :
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

theorem nb081_support_mem_0044 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈
      (((syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪
        ((syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0045 (x : Var) :
    x ∈ (((syn_csn (syn_csn (Class.cv x)))).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0046 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈ (((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv) :=
  by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0047 (x : Var) : x ∈ (((syn_csn (Class.cv x))).fv) :=
  by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0048 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈ (((Class.cv (nb081_alpha_dummy_000 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0049 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0050 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈
      (((syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))))).fv ∪ ((syn_csn
            (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0051 (x : Var) (y : Var) :
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

theorem nb081_support_mem_0052 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈
      (((syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
          (Class.cv (nb081_alpha_dummy_001 A)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0053 (x : Var) (y : Var) :
    x ∈ (((syn_cpr (Class.cv x) (Class.cv y))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0054 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈
      (((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0055 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0056 (A : Class) :
    (nb081_alpha_dummy_000 A) ∈
      (((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv ∪
        ((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0057 (x : Var) :
    x ∈ (((syn_csn (Class.cv x))).fv ∪ ((syn_csn (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0058 (A : Class) :
    (nb081_alpha_dummy_001 A) ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A)))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
                (Class.cv (nb081_alpha_dummy_001 A)))))).fv) :=
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

theorem nb081_support_mem_0059 (x : Var) (y : Var) :
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

theorem nb081_support_mem_0060 (A : Class) :
    (nb081_alpha_dummy_001 A) ∈
      (((syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))))).fv ∪ ((syn_csn
            (syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0061 (x : Var) (y : Var) :
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

theorem nb081_support_mem_0062 (A : Class) :
    (nb081_alpha_dummy_001 A) ∈
      (((syn_cpr (Class.cv (nb081_alpha_dummy_000 A))
          (Class.cv (nb081_alpha_dummy_001 A)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0063 (x : Var) (y : Var) :
    y ∈ (((syn_cpr (Class.cv x) (Class.cv y))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0064 (A : Class) :
    (nb081_alpha_dummy_001 A) ∈
      (((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0065 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0066 (A : Class) :
    (nb081_alpha_dummy_001 A) ∈
      (((syn_csn (Class.cv (nb081_alpha_dummy_001 A)))).fv ∪
        ((syn_csn (Class.cv (nb081_alpha_dummy_001 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0067 (y : Var) :
    y ∈ (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0068 (A : Class) :
    (nb081_alpha_dummy_001 A) ∈ (((Class.cv (nb081_alpha_dummy_001 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0069 (y : Var) : y ∈ (((Class.cv y)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
