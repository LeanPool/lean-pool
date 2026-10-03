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

/-! Certificates from `NAR4C075C001Part001`. -/


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
noncomputable def nb075_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb075_alpha_dummy_001 : Var :=
  (freshVar (({(nb075_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
      ((syn_crn (Class.cv (nb075_alpha_dummy_000)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_002 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_crn (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_003 : Var :=
  (freshVar
    (({(nb075_alpha_dummy_000)} : Finset Var) ∪ ({(nb075_alpha_dummy_001)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb075_alpha_dummy_000)) (syn_cvv))
          (Wff.classEq (Class.cv (nb075_alpha_dummy_001))
            (syn_crn (Class.cv (nb075_alpha_dummy_000)))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_004 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({(nb075_alpha_dummy_002 x)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
          (Wff.classEq (Class.cv (nb075_alpha_dummy_002 x)) (syn_crn (Class.cv x))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_005 : Var :=
  (freshVar
    (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_006 : Var :=
  (freshVar
    (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_007 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_008 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_009 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cphi (Class.cv (nb075_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_010 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb075_alpha_dummy_007 x)
            (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb075_alpha_dummy_007 x)
            (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_011 : Var :=
  (freshVar (((Class.cab (nb075_alpha_dummy_005)
          (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
              (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv ∪
      ((Class.cab (nb075_alpha_dummy_005)
          (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
              (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_012 (x : Var) : Var :=
  (freshVar (((Class.cab (nb075_alpha_dummy_007 x)
          (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
              (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv ∪
      ((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
              (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_013 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_006))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_014 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_006))).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_015 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_008 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_016 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_008 x))).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb075_alpha_dummy_013)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb075_alpha_dummy_013)) (syn_c1c))).fv ∪
      ((Class.cv (nb075_alpha_dummy_013))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_018 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb075_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb075_alpha_dummy_015 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb075_alpha_dummy_015 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_019 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_020 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_021 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb075_alpha_dummy_022 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_023 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_024 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb075_alpha_dummy_025 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb075_alpha_dummy_020))
          (Class.cv (nb075_alpha_dummy_021)))).fv ∪
      ((syn_cnin (Class.cv (nb075_alpha_dummy_020)) (Class.cv (nb075_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_026 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb075_alpha_dummy_023 x))
          (Class.cv (nb075_alpha_dummy_024 x)))).fv ∪
      ((syn_cnin (Class.cv (nb075_alpha_dummy_023 x)) (Class.cv (nb075_alpha_dummy_024 x)))).fv)
    0)

@[expose]
noncomputable def nb075_alpha_dummy_027 : Var :=
  (freshVar
    (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_028 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪
      ((Class.cv (nb075_alpha_dummy_024 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_029 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb075_alpha_dummy_020)))).fv ∪
      ((syn_ccompl (Class.cv (nb075_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_030 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb075_alpha_dummy_023 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb075_alpha_dummy_024 x)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_031 : Var :=
  (freshVar
    (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_020))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_032 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪
      ((Class.cv (nb075_alpha_dummy_023 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_033 : Var :=
  (freshVar
    (((Class.cv (nb075_alpha_dummy_021))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_034 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_024 x))).fv ∪
      ((Class.cv (nb075_alpha_dummy_024 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_035 : Var :=
  (freshVar (((Class.cab (nb075_alpha_dummy_005)
          (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_005)
          (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_036 (x : Var) : Var :=
  (freshVar (((Class.cab (nb075_alpha_dummy_007 x)
          (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
              (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_007 x)
          (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
              (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_037 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_006))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_038 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_039 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb075_alpha_dummy_006)))).fv ∪
      ((syn_cphi (Class.cv (nb075_alpha_dummy_006)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_040 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))).fv ∪
      ((syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_041 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_042 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_043 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_044 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_045 : Var :=
  (freshVar
    (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_046 : Var :=
  (freshVar
    (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_047 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪
      ((Class.cv (nb075_alpha_dummy_043 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_048 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪
      ((Class.cv (nb075_alpha_dummy_043 x))).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_049 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cphi (Class.cv (nb075_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_050 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_051 : Var :=
  (freshVar (((Class.cab (nb075_alpha_dummy_045)
          (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
              (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv ∪
      ((Class.cab (nb075_alpha_dummy_045)
          (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
              (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_052 (x : Var) : Var :=
  (freshVar (((Class.cab (nb075_alpha_dummy_047 x)
          (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
              (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv ∪
      ((Class.cab (nb075_alpha_dummy_047 x)
          (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
              (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_053 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_046))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_054 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_046))).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_055 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_048 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_056 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_048 x))).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_057 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb075_alpha_dummy_053)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb075_alpha_dummy_053)) (syn_c1c))).fv ∪
      ((Class.cv (nb075_alpha_dummy_053))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_058 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb075_alpha_dummy_055 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb075_alpha_dummy_055 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb075_alpha_dummy_055 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_059 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_060 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_061 : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb075_alpha_dummy_062 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_063 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb075_alpha_dummy_064 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb075_alpha_dummy_065 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb075_alpha_dummy_060))
          (Class.cv (nb075_alpha_dummy_061)))).fv ∪
      ((syn_cnin (Class.cv (nb075_alpha_dummy_060)) (Class.cv (nb075_alpha_dummy_061)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_066 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb075_alpha_dummy_063 x))
          (Class.cv (nb075_alpha_dummy_064 x)))).fv ∪
      ((syn_cnin (Class.cv (nb075_alpha_dummy_063 x)) (Class.cv (nb075_alpha_dummy_064 x)))).fv)
    0)

@[expose]
noncomputable def nb075_alpha_dummy_067 : Var :=
  (freshVar
    (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_068 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪
      ((Class.cv (nb075_alpha_dummy_064 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_069 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb075_alpha_dummy_060)))).fv ∪
      ((syn_ccompl (Class.cv (nb075_alpha_dummy_061)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_070 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb075_alpha_dummy_063 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb075_alpha_dummy_064 x)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_071 : Var :=
  (freshVar
    (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_060))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_072 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪
      ((Class.cv (nb075_alpha_dummy_063 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_073 : Var :=
  (freshVar
    (((Class.cv (nb075_alpha_dummy_061))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_074 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075_alpha_dummy_064 x))).fv ∪
      ((Class.cv (nb075_alpha_dummy_064 x))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_075 : Var :=
  (freshVar (((Class.cab (nb075_alpha_dummy_045)
          (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
              (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_045)
          (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
              (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_076 (x : Var) : Var :=
  (freshVar (((Class.cab (nb075_alpha_dummy_047 x)
          (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
              (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_047 x)
          (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
              (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_077 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_046))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_078 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_079 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb075_alpha_dummy_046)))).fv ∪
      ((syn_cphi (Class.cv (nb075_alpha_dummy_046)))).fv) 0)

@[expose]
noncomputable def nb075_alpha_dummy_080 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))).fv ∪
      ((syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))).fv) 0)

theorem nb075_fresh_000 :
    (nb075_alpha_dummy_011) ∉
      (((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv)
      0

theorem nb075_fresh_001 :
    (nb075_alpha_dummy_035) ∉
      (((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb075_fresh_002 (x : Var) :
    (nb075_alpha_dummy_036 x) ∉
      (((Class.cab (nb075_alpha_dummy_007 x)
            (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_007 x)
            (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb075_alpha_dummy_007 x)
            (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_007 x)
            (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb075_fresh_003 (x : Var) :
    (nb075_alpha_dummy_012 x) ∉
      (((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv)
      0

theorem nb075_fresh_004 :
    (nb075_alpha_dummy_075) ∉
      (((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_075] using
    freshVar_not_mem
      (((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb075_fresh_005 :
    (nb075_alpha_dummy_051) ∉
      (((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_051] using
    freshVar_not_mem
      (((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv)
      0

theorem nb075_fresh_006 (x : Var) :
    (nb075_alpha_dummy_076 x) ∉
      (((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_076] using
    freshVar_not_mem
      (((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb075_fresh_007 (x : Var) :
    (nb075_alpha_dummy_052 x) ∉
      (((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_052] using
    freshVar_not_mem
      (((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv)
      0

theorem nb075_fresh_008 :
    (nb075_alpha_dummy_005) ∉
      (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) :=
  by
  simpa only [nb075_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv)
      0

theorem nb075_fresh_009 :
    (nb075_alpha_dummy_006) ∉
      (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) :=
  by
  simpa only [nb075_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv)
      1

theorem nb075_distinct_010 : (nb075_alpha_dummy_005) ≠ (nb075_alpha_dummy_006) := by
  simpa only [nb075_alpha_dummy_005, nb075_alpha_dummy_006] using
    (freshVar_injective
      (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb075_fresh_011 :
    (nb075_alpha_dummy_041) ∉
      (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb075_alpha_dummy_041] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0

theorem nb075_fresh_012 :
    (nb075_alpha_dummy_042) ∉
      (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb075_alpha_dummy_042] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1

theorem nb075_distinct_013 : (nb075_alpha_dummy_041) ≠ (nb075_alpha_dummy_042) := by
  simpa only [nb075_alpha_dummy_041, nb075_alpha_dummy_042] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb075_fresh_014 :
    (nb075_alpha_dummy_013) ∉ (((Class.cv (nb075_alpha_dummy_006))).fv) := by
  simpa only [nb075_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_006))).fv) 0

theorem nb075_fresh_015 :
    (nb075_alpha_dummy_014) ∉ (((Class.cv (nb075_alpha_dummy_006))).fv) := by
  simpa only [nb075_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_006))).fv) 1

theorem nb075_distinct_016 : (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_014) := by
  simpa only [nb075_alpha_dummy_013, nb075_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_017 (x : Var) :
    (nb075_alpha_dummy_015 x) ∉ (((Class.cv (nb075_alpha_dummy_008 x))).fv) := by
  simpa only [nb075_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_008 x))).fv) 0

theorem nb075_fresh_018 (x : Var) :
    (nb075_alpha_dummy_016 x) ∉ (((Class.cv (nb075_alpha_dummy_008 x))).fv) := by
  simpa only [nb075_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_008 x))).fv) 1

theorem nb075_distinct_019 (x : Var) :
    (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_016 x) := by
  simpa only [nb075_alpha_dummy_015, nb075_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_008 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb075_fresh_020 :
    (nb075_alpha_dummy_019) ∉
      (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0

theorem nb075_fresh_021 :
    (nb075_alpha_dummy_020) ∉
      (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1

theorem nb075_fresh_022 :
    (nb075_alpha_dummy_021) ∉
      (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2

theorem nb075_distinct_023 : (nb075_alpha_dummy_019) ≠ (nb075_alpha_dummy_020) := by
  simpa only [nb075_alpha_dummy_019, nb075_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb075_distinct_024 : (nb075_alpha_dummy_019) ≠ (nb075_alpha_dummy_021) := by
  simpa only [nb075_alpha_dummy_019, nb075_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb075_distinct_025 : (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_021) := by
  simpa only [nb075_alpha_dummy_020, nb075_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb075_fresh_026 (x : Var) :
    (nb075_alpha_dummy_022 x) ∉
      (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb075_fresh_027 (x : Var) :
    (nb075_alpha_dummy_023 x) ∉
      (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb075_fresh_028 (x : Var) :
    (nb075_alpha_dummy_024 x) ∉
      (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb075_distinct_029 (x : Var) :
    (nb075_alpha_dummy_022 x) ≠ (nb075_alpha_dummy_023 x) := by
  simpa only [nb075_alpha_dummy_022, nb075_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb075_distinct_030 (x : Var) :
    (nb075_alpha_dummy_022 x) ≠ (nb075_alpha_dummy_024 x) := by
  simpa only [nb075_alpha_dummy_022, nb075_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb075_distinct_031 (x : Var) :
    (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_024 x) := by
  simpa only [nb075_alpha_dummy_023, nb075_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb075_fresh_032 :
    (nb075_alpha_dummy_031) ∉
      (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_020))).fv) :=
  by
  simpa only [nb075_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_020))).fv)
      0

theorem nb075_fresh_033 :
    (nb075_alpha_dummy_027) ∉
      (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) :=
  by
  simpa only [nb075_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv)
      0

theorem nb075_fresh_034 :
    (nb075_alpha_dummy_033) ∉
      (((Class.cv (nb075_alpha_dummy_021))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) :=
  by
  simpa only [nb075_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_021))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv)
      0

theorem nb075_fresh_035 (x : Var) :
    (nb075_alpha_dummy_032 x) ∉
      (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_023 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_023 x))).fv)
      0

theorem nb075_fresh_036 (x : Var) :
    (nb075_alpha_dummy_028 x) ∉
      (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv)
      0

theorem nb075_fresh_037 (x : Var) :
    (nb075_alpha_dummy_034 x) ∉
      (((Class.cv (nb075_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv)
      0

theorem nb075_fresh_038 :
    (nb075_alpha_dummy_045) ∉
      (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) :=
  by
  simpa only [nb075_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv)
      0

theorem nb075_fresh_039 :
    (nb075_alpha_dummy_046) ∉
      (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) :=
  by
  simpa only [nb075_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv)
      1

theorem nb075_distinct_040 : (nb075_alpha_dummy_045) ≠ (nb075_alpha_dummy_046) := by
  simpa only [nb075_alpha_dummy_045, nb075_alpha_dummy_046] using
    (freshVar_injective
      (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb075_fresh_041 (x : Var) :
    (nb075_alpha_dummy_047 x) ∉
      (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_047] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv)
      0

theorem nb075_fresh_042 (x : Var) :
    (nb075_alpha_dummy_048 x) ∉
      (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_048] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv)
      1

theorem nb075_distinct_043 (x : Var) :
    (nb075_alpha_dummy_047 x) ≠ (nb075_alpha_dummy_048 x) := by
  simpa only [nb075_alpha_dummy_047, nb075_alpha_dummy_048] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪
        ((Class.cv (nb075_alpha_dummy_043 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_044 :
    (nb075_alpha_dummy_053) ∉ (((Class.cv (nb075_alpha_dummy_046))).fv) := by
  simpa only [nb075_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_046))).fv) 0

theorem nb075_fresh_045 :
    (nb075_alpha_dummy_054) ∉ (((Class.cv (nb075_alpha_dummy_046))).fv) := by
  simpa only [nb075_alpha_dummy_054] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_046))).fv) 1

theorem nb075_distinct_046 : (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_054) := by
  simpa only [nb075_alpha_dummy_053, nb075_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_046))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_047 (x : Var) :
    (nb075_alpha_dummy_055 x) ∉ (((Class.cv (nb075_alpha_dummy_048 x))).fv) := by
  simpa only [nb075_alpha_dummy_055] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_048 x))).fv) 0

theorem nb075_fresh_048 (x : Var) :
    (nb075_alpha_dummy_056 x) ∉ (((Class.cv (nb075_alpha_dummy_048 x))).fv) := by
  simpa only [nb075_alpha_dummy_056] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_048 x))).fv) 1

theorem nb075_distinct_049 (x : Var) :
    (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_056 x) := by
  simpa only [nb075_alpha_dummy_055, nb075_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_048 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb075_fresh_050 :
    (nb075_alpha_dummy_059) ∉
      (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0

theorem nb075_fresh_051 :
    (nb075_alpha_dummy_060) ∉
      (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1

theorem nb075_fresh_052 :
    (nb075_alpha_dummy_061) ∉
      (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2

theorem nb075_distinct_053 : (nb075_alpha_dummy_059) ≠ (nb075_alpha_dummy_060) := by
  simpa only [nb075_alpha_dummy_059, nb075_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb075_distinct_054 : (nb075_alpha_dummy_059) ≠ (nb075_alpha_dummy_061) := by
  simpa only [nb075_alpha_dummy_059, nb075_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb075_distinct_055 : (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_061) := by
  simpa only [nb075_alpha_dummy_060, nb075_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb075_fresh_056 (x : Var) :
    (nb075_alpha_dummy_062 x) ∉
      (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_062] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb075_fresh_057 (x : Var) :
    (nb075_alpha_dummy_063 x) ∉
      (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_063] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb075_fresh_058 (x : Var) :
    (nb075_alpha_dummy_064 x) ∉
      (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb075_alpha_dummy_064] using
    freshVar_not_mem (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb075_distinct_059 (x : Var) :
    (nb075_alpha_dummy_062 x) ≠ (nb075_alpha_dummy_063 x) := by
  simpa only [nb075_alpha_dummy_062, nb075_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb075_distinct_060 (x : Var) :
    (nb075_alpha_dummy_062 x) ≠ (nb075_alpha_dummy_064 x) := by
  simpa only [nb075_alpha_dummy_062, nb075_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb075_distinct_061 (x : Var) :
    (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_064 x) := by
  simpa only [nb075_alpha_dummy_063, nb075_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb075_fresh_062 :
    (nb075_alpha_dummy_071) ∉
      (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_060))).fv) :=
  by
  simpa only [nb075_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_060))).fv)
      0

theorem nb075_fresh_063 :
    (nb075_alpha_dummy_067) ∉
      (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) :=
  by
  simpa only [nb075_alpha_dummy_067] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv)
      0

theorem nb075_fresh_064 :
    (nb075_alpha_dummy_073) ∉
      (((Class.cv (nb075_alpha_dummy_061))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) :=
  by
  simpa only [nb075_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_061))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv)
      0

theorem nb075_fresh_065 (x : Var) :
    (nb075_alpha_dummy_072 x) ∉
      (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_063 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_063 x))).fv)
      0

theorem nb075_fresh_066 (x : Var) :
    (nb075_alpha_dummy_068 x) ∉
      (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv)
      0

theorem nb075_fresh_067 (x : Var) :
    (nb075_alpha_dummy_074 x) ∉
      (((Class.cv (nb075_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_074] using
    freshVar_not_mem
      (((Class.cv (nb075_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv)
      0

theorem nb075_fresh_068 (x : Var) :
    (nb075_alpha_dummy_007 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C075C001Part002`. -/


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

theorem nb075_fresh_069 (x : Var) :
    (nb075_alpha_dummy_008 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) 1

theorem nb075_distinct_070 (x : Var) :
    (nb075_alpha_dummy_007 x) ≠ (nb075_alpha_dummy_008 x) := by
  simpa only [nb075_alpha_dummy_007, nb075_alpha_dummy_008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb075_fresh_071 (x : Var) :
    (nb075_alpha_dummy_043 x) ∉ (((Class.cv x)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb075_alpha_dummy_043] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((syn_cvv)).fv) 0

theorem nb075_fresh_072 (x : Var) :
    (nb075_alpha_dummy_044 x) ∉ (((Class.cv x)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb075_alpha_dummy_044] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((syn_cvv)).fv) 1

theorem nb075_distinct_073 (x : Var) :
    (nb075_alpha_dummy_043 x) ≠ (nb075_alpha_dummy_044 x) := by
  simpa only [nb075_alpha_dummy_043, nb075_alpha_dummy_044] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_074 :
    (nb075_alpha_dummy_017) ∉
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_013))).fv) :=
  by
  simpa only [nb075_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_013))).fv)
      0

theorem nb075_fresh_075 (x : Var) :
    (nb075_alpha_dummy_018 x) ∉
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_015 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_015 x))).fv)
      0

theorem nb075_fresh_076 :
    (nb075_alpha_dummy_057) ∉
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_053)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_053)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_053))).fv) :=
  by
  simpa only [nb075_alpha_dummy_057] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_053)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_053)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_053))).fv)
      0

theorem nb075_fresh_077 (x : Var) :
    (nb075_alpha_dummy_058 x) ∉
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_055 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_055 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_055 x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_058] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_055 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_055 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_055 x))).fv)
      0

theorem nb075_fresh_078 :
    (nb075_alpha_dummy_009) ∉
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_005)
              (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_005)
              (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_005)
              (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_005)
              (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb075_fresh_079 (x : Var) :
    (nb075_alpha_dummy_010 x) ∉
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_007 x)
              (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_007 x)
              (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_007 x)
              (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_007 x)
              (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb075_fresh_080 :
    (nb075_alpha_dummy_049) ∉
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_045)
              (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_045)
              (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_045)
              (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_045)
              (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb075_fresh_081 (x : Var) :
    (nb075_alpha_dummy_050 x) ∉
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_047 x)
              (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_047 x)
              (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_050] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_047 x)
              (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_047 x)
              (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb075_fresh_082 :
    (nb075_alpha_dummy_029) ∉
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_021)))).fv)
      0

theorem nb075_fresh_083 (x : Var) :
    (nb075_alpha_dummy_030 x) ∉
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_024 x)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_024 x)))).fv)
      0

theorem nb075_fresh_084 :
    (nb075_alpha_dummy_069) ∉
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_061)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_069] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_061)))).fv)
      0

theorem nb075_fresh_085 (x : Var) :
    (nb075_alpha_dummy_070 x) ∉
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_063 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_064 x)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_070] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_063 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_064 x)))).fv)
      0

theorem nb075_fresh_086 :
    (nb075_alpha_dummy_037) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb075_fresh_087 (x : Var) :
    (nb075_alpha_dummy_038 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb075_fresh_088 :
    (nb075_alpha_dummy_077) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_046))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_046))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb075_fresh_089 (x : Var) :
    (nb075_alpha_dummy_078 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_078] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb075_fresh_090 :
    (nb075_alpha_dummy_025) ∉
      (((syn_cnin (Class.cv (nb075_alpha_dummy_020)) (Class.cv (nb075_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_020))
            (Class.cv (nb075_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb075_alpha_dummy_020)) (Class.cv (nb075_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_020)) (Class.cv (nb075_alpha_dummy_021)))).fv)
      0

theorem nb075_fresh_091 (x : Var) :
    (nb075_alpha_dummy_026 x) ∉
      (((syn_cnin (Class.cv (nb075_alpha_dummy_023 x))
            (Class.cv (nb075_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_023 x))
            (Class.cv (nb075_alpha_dummy_024 x)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb075_alpha_dummy_023 x))
            (Class.cv (nb075_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_023 x))
            (Class.cv (nb075_alpha_dummy_024 x)))).fv)
      0

theorem nb075_fresh_092 :
    (nb075_alpha_dummy_065) ∉
      (((syn_cnin (Class.cv (nb075_alpha_dummy_060)) (Class.cv (nb075_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_060))
            (Class.cv (nb075_alpha_dummy_061)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_065] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb075_alpha_dummy_060)) (Class.cv (nb075_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_060)) (Class.cv (nb075_alpha_dummy_061)))).fv)
      0

theorem nb075_fresh_093 (x : Var) :
    (nb075_alpha_dummy_066 x) ∉
      (((syn_cnin (Class.cv (nb075_alpha_dummy_063 x))
            (Class.cv (nb075_alpha_dummy_064 x)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_063 x))
            (Class.cv (nb075_alpha_dummy_064 x)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_066] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb075_alpha_dummy_063 x))
            (Class.cv (nb075_alpha_dummy_064 x)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_063 x))
            (Class.cv (nb075_alpha_dummy_064 x)))).fv)
      0

theorem nb075_fresh_094 :
    (nb075_alpha_dummy_039) ∉
      (((syn_cphi (Class.cv (nb075_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_006)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb075_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_006)))).fv)
      0

theorem nb075_fresh_095 (x : Var) :
    (nb075_alpha_dummy_040 x) ∉
      (((syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))).fv)
      0

theorem nb075_fresh_096 :
    (nb075_alpha_dummy_079) ∉
      (((syn_cphi (Class.cv (nb075_alpha_dummy_046)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_046)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_079] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb075_alpha_dummy_046)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_046)))).fv)
      0

theorem nb075_fresh_097 (x : Var) :
    (nb075_alpha_dummy_080 x) ∉
      (((syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_080] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))).fv)
      0

theorem nb075_fresh_098 :
    (nb075_alpha_dummy_001) ∉
      (({(nb075_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_crn (Class.cv (nb075_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb075_alpha_dummy_001] using
    freshVar_not_mem
      (({(nb075_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_crn (Class.cv (nb075_alpha_dummy_000)))).fv)
      0

theorem nb075_fresh_099 :
    (nb075_alpha_dummy_003) ∉
      (({(nb075_alpha_dummy_000)} : Finset Var) ∪ ({(nb075_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb075_alpha_dummy_000)) (syn_cvv))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_001))
              (syn_crn (Class.cv (nb075_alpha_dummy_000)))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_003] using
    freshVar_not_mem
      (({(nb075_alpha_dummy_000)} : Finset Var) ∪ ({(nb075_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb075_alpha_dummy_000)) (syn_cvv))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_001))
              (syn_crn (Class.cv (nb075_alpha_dummy_000)))))).fv)
      0

theorem nb075_fresh_100 (x : Var) :
    (nb075_alpha_dummy_002 x) ∉
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_crn (Class.cv x))).fv) :=
  by
  simpa only [nb075_alpha_dummy_002] using
    freshVar_not_mem (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_crn (Class.cv x))).fv)
      0

theorem nb075_fresh_101 (x : Var) :
    (nb075_alpha_dummy_004 x) ∉
      (({ x } : Finset Var) ∪ ({(nb075_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_002 x)) (syn_crn (Class.cv x))))).fv) :=
  by
  simpa only [nb075_alpha_dummy_004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({(nb075_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_002 x)) (syn_crn (Class.cv x))))).fv)
      0

theorem nb075_fresh_102 : (nb075_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb075_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb075_support_mem_0000 :
    (nb075_alpha_dummy_000) ∈
      (({(nb075_alpha_dummy_000)} : Finset Var) ∪ ({(nb075_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb075_alpha_dummy_000)) (syn_cvv))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_001))
              (syn_crn (Class.cv (nb075_alpha_dummy_000)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0001 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({(nb075_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_002 x)) (syn_crn (Class.cv x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0002 :
    (nb075_alpha_dummy_001) ∈
      (({(nb075_alpha_dummy_000)} : Finset Var) ∪ ({(nb075_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb075_alpha_dummy_000)) (syn_cvv))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_001))
              (syn_crn (Class.cv (nb075_alpha_dummy_000)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0003 (x : Var) :
    (nb075_alpha_dummy_002 x) ∈
      (({ x } : Finset Var) ∪ ({(nb075_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb075_alpha_dummy_002 x)) (syn_crn (Class.cv x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0004 :
    (nb075_alpha_dummy_000) ∈
      (({(nb075_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_crn (Class.cv (nb075_alpha_dummy_000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0005 (x : Var) :
    x ∈ (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_crn (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0006 :
    (nb075_alpha_dummy_000) ∈
      (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0007 :
    (nb075_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_005)
              (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_005)
              (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_005) from (by
          unfold nb075_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_006) from (by
            unfold nb075_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0008 (x : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0009 (x : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_007 x)
              (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_007 x)
              (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb075_alpha_dummy_007 x) from (by
          unfold nb075_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb075_alpha_dummy_008 x) from (by
            unfold nb075_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0010 :
    (nb075_alpha_dummy_000) ∈
      (((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_005) from (by
          unfold nb075_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_006) from (by
            unfold nb075_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0011 (x : Var) :
    x ∈
      (((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb075_alpha_dummy_007 x) from (by
          unfold nb075_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb075_alpha_dummy_008 x) from (by
            unfold nb075_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0012 :
    (nb075_alpha_dummy_006) ∈ (((Class.cv (nb075_alpha_dummy_006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0013 (x : Var) :
    (nb075_alpha_dummy_008 x) ∈ (((Class.cv (nb075_alpha_dummy_008 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0014 :
    (nb075_alpha_dummy_013) ∈
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_013))).fv) :=
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

theorem nb075_support_mem_0015 (x : Var) :
    (nb075_alpha_dummy_015 x) ∈
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_015 x))).fv) :=
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

theorem nb075_support_mem_0016 :
    (nb075_alpha_dummy_013) ∈
      (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0017 (x : Var) :
    (nb075_alpha_dummy_015 x) ∈
      (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0018 :
    (nb075_alpha_dummy_020) ∈
      (((syn_cnin (Class.cv (nb075_alpha_dummy_020)) (Class.cv (nb075_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_020))
            (Class.cv (nb075_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0019 (x : Var) :
    (nb075_alpha_dummy_023 x) ∈
      (((syn_cnin (Class.cv (nb075_alpha_dummy_023 x))
            (Class.cv (nb075_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_023 x))
            (Class.cv (nb075_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0020 :
    (nb075_alpha_dummy_020) ∈
      (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0021 (x : Var) :
    (nb075_alpha_dummy_023 x) ∈
      (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0022 :
    (nb075_alpha_dummy_021) ∈
      (((syn_cnin (Class.cv (nb075_alpha_dummy_020)) (Class.cv (nb075_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_020))
            (Class.cv (nb075_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0023 (x : Var) :
    (nb075_alpha_dummy_024 x) ∈
      (((syn_cnin (Class.cv (nb075_alpha_dummy_023 x))
            (Class.cv (nb075_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_023 x))
            (Class.cv (nb075_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0024 :
    (nb075_alpha_dummy_021) ∈
      (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0025 (x : Var) :
    (nb075_alpha_dummy_024 x) ∈
      (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0026 :
    (nb075_alpha_dummy_020) ∈
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0027 (x : Var) :
    (nb075_alpha_dummy_023 x) ∈
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0028 :
    (nb075_alpha_dummy_020) ∈
      (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0029 (x : Var) :
    (nb075_alpha_dummy_023 x) ∈
      (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_023 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0030 :
    (nb075_alpha_dummy_021) ∈
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0031 (x : Var) :
    (nb075_alpha_dummy_024 x) ∈
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0032 :
    (nb075_alpha_dummy_021) ∈
      (((Class.cv (nb075_alpha_dummy_021))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0033 (x : Var) :
    (nb075_alpha_dummy_024 x) ∈
      (((Class.cv (nb075_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0034 :
    (nb075_alpha_dummy_001) ∈
      (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0035 :
    (nb075_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_005)
              (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_005)
              (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_001) ≠ (nb075_alpha_dummy_005) from (by
          unfold nb075_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_001) ≠ (nb075_alpha_dummy_006) from (by
            unfold nb075_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0036 (x : Var) :
    (nb075_alpha_dummy_002 x) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0037 (x : Var) :
    (nb075_alpha_dummy_002 x) ∈
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_007 x)
              (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_007 x)
              (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_002 x) ≠ (nb075_alpha_dummy_007 x) from (by
          unfold nb075_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_002 x) ≠ (nb075_alpha_dummy_008 x) from (by
            unfold nb075_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0038 :
    (nb075_alpha_dummy_001) ∈
      (((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_005)
            (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_001) ≠ (nb075_alpha_dummy_005) from (by
          unfold nb075_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_001) ≠ (nb075_alpha_dummy_006) from (by
            unfold nb075_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0039 (x : Var) :
    (nb075_alpha_dummy_002 x) ∈
      (((Class.cab (nb075_alpha_dummy_007 x)
            (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_007 x)
            (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_002 x) ≠ (nb075_alpha_dummy_007 x) from (by
          unfold nb075_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_002 x) ≠ (nb075_alpha_dummy_008 x) from (by
            unfold nb075_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0040 :
    (nb075_alpha_dummy_006) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0041 (x : Var) :
    (nb075_alpha_dummy_008 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0042 :
    (nb075_alpha_dummy_006) ∈
      (((syn_cphi (Class.cv (nb075_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0043 (x : Var) :
    (nb075_alpha_dummy_008 x) ∈
      (((syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0044 :
    (nb075_alpha_dummy_042) ∈
      (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0045 :
    (nb075_alpha_dummy_042) ∈
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_045)
              (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_045)
              (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_045) from (by
          unfold nb075_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_046) from (by
            unfold nb075_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0044) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0046 (x : Var) :
    (nb075_alpha_dummy_044 x) ∈
      (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0047 (x : Var) :
    (nb075_alpha_dummy_044 x) ∈
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_047 x)
              (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_047 x)
              (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_047 x) from (by
          unfold nb075_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0046 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_048 x) from (by
            unfold nb075_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0046 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0048 :
    (nb075_alpha_dummy_042) ∈
      (((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_045) from (by
          unfold nb075_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_046) from (by
            unfold nb075_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0044) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0049 (x : Var) :
    (nb075_alpha_dummy_044 x) ∈
      (((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv ∪
        ((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_047 x) from (by
          unfold nb075_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0046 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_048 x) from (by
            unfold nb075_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0046 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0050 :
    (nb075_alpha_dummy_046) ∈ (((Class.cv (nb075_alpha_dummy_046))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0051 (x : Var) :
    (nb075_alpha_dummy_048 x) ∈ (((Class.cv (nb075_alpha_dummy_048 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0052 :
    (nb075_alpha_dummy_053) ∈
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_053)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_053)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_053))).fv) :=
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

theorem nb075_support_mem_0053 (x : Var) :
    (nb075_alpha_dummy_055 x) ∈
      (((Wff.classMem (Class.cv (nb075_alpha_dummy_055 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb075_alpha_dummy_055 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb075_alpha_dummy_055 x))).fv) :=
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

theorem nb075_support_mem_0054 :
    (nb075_alpha_dummy_053) ∈
      (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0055 (x : Var) :
    (nb075_alpha_dummy_055 x) ∈
      (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0056 :
    (nb075_alpha_dummy_060) ∈
      (((syn_cnin (Class.cv (nb075_alpha_dummy_060)) (Class.cv (nb075_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_060))
            (Class.cv (nb075_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0057 (x : Var) :
    (nb075_alpha_dummy_063 x) ∈
      (((syn_cnin (Class.cv (nb075_alpha_dummy_063 x))
            (Class.cv (nb075_alpha_dummy_064 x)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_063 x))
            (Class.cv (nb075_alpha_dummy_064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0058 :
    (nb075_alpha_dummy_060) ∈
      (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0059 (x : Var) :
    (nb075_alpha_dummy_063 x) ∈
      (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0060 :
    (nb075_alpha_dummy_061) ∈
      (((syn_cnin (Class.cv (nb075_alpha_dummy_060)) (Class.cv (nb075_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_060))
            (Class.cv (nb075_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0061 (x : Var) :
    (nb075_alpha_dummy_064 x) ∈
      (((syn_cnin (Class.cv (nb075_alpha_dummy_063 x))
            (Class.cv (nb075_alpha_dummy_064 x)))).fv ∪
        ((syn_cnin (Class.cv (nb075_alpha_dummy_063 x))
            (Class.cv (nb075_alpha_dummy_064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0062 :
    (nb075_alpha_dummy_061) ∈
      (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0063 (x : Var) :
    (nb075_alpha_dummy_064 x) ∈
      (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0064 :
    (nb075_alpha_dummy_060) ∈
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0065 (x : Var) :
    (nb075_alpha_dummy_063 x) ∈
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_063 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0066 :
    (nb075_alpha_dummy_060) ∈
      (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_060))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0067 (x : Var) :
    (nb075_alpha_dummy_063 x) ∈
      (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_063 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0068 :
    (nb075_alpha_dummy_061) ∈
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0069 (x : Var) :
    (nb075_alpha_dummy_064 x) ∈
      (((syn_ccompl (Class.cv (nb075_alpha_dummy_063 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb075_alpha_dummy_064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0070 :
    (nb075_alpha_dummy_061) ∈
      (((Class.cv (nb075_alpha_dummy_061))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0071 (x : Var) :
    (nb075_alpha_dummy_064 x) ∈
      (((Class.cv (nb075_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0072 :
    (nb075_alpha_dummy_041) ∈
      (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0073 :
    (nb075_alpha_dummy_041) ∈
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_045)
              (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_045)
              (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_041) ≠ (nb075_alpha_dummy_045) from (by
          unfold nb075_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_041) ≠ (nb075_alpha_dummy_046) from (by
            unfold nb075_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0074 (x : Var) :
    (nb075_alpha_dummy_043 x) ∈
      (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0075 (x : Var) :
    (nb075_alpha_dummy_043 x) ∈
      (((syn_ccompl (Class.cab (nb075_alpha_dummy_047 x)
              (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb075_alpha_dummy_047 x)
              (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                  (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_043 x) ≠ (nb075_alpha_dummy_047 x) from (by
          unfold nb075_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_043 x) ≠ (nb075_alpha_dummy_048 x) from (by
            unfold nb075_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0076 :
    (nb075_alpha_dummy_041) ∈
      (((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_045)
            (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_041) ≠ (nb075_alpha_dummy_045) from (by
          unfold nb075_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_041) ≠ (nb075_alpha_dummy_046) from (by
            unfold nb075_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0077 (x : Var) :
    (nb075_alpha_dummy_043 x) ∈
      (((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_047 x)
            (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075_alpha_dummy_043 x) ≠ (nb075_alpha_dummy_047 x) from (by
          unfold nb075_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075_alpha_dummy_043 x) ≠ (nb075_alpha_dummy_048 x) from (by
            unfold nb075_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0078 :
    (nb075_alpha_dummy_046) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_046))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0079 (x : Var) :
    (nb075_alpha_dummy_048 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0080 :
    (nb075_alpha_dummy_046) ∈
      (((syn_cphi (Class.cv (nb075_alpha_dummy_046)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_046)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0081 (x : Var) :
    (nb075_alpha_dummy_048 x) ∈
      (((syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))).fv ∪
        ((syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0082 :
    (nb075_alpha_dummy_000) ∈
      (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0083 (x : Var) : x ∈ (((Class.cv x)).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
