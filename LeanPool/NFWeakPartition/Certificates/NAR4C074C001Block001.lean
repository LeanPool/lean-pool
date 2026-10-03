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

/-! Certificates from `NAR4C074C001Part001`. -/


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
noncomputable def nb074_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb074_alpha_dummy_001 : Var :=
  (freshVar (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
      ((syn_cdm (Class.cv (nb074_alpha_dummy_000)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_002 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_003 : Var :=
  (freshVar
    (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ({(nb074_alpha_dummy_001)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb074_alpha_dummy_000)) (syn_cvv))
          (Wff.classEq (Class.cv (nb074_alpha_dummy_001))
            (syn_cdm (Class.cv (nb074_alpha_dummy_000)))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_004 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({(nb074_alpha_dummy_002 x)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
          (Wff.classEq (Class.cv (nb074_alpha_dummy_002 x)) (syn_cdm (Class.cv x))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_005 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_006 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_007 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_008 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_009 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cphi (Class.cv (nb074_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_010 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x)
            (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb074_alpha_dummy_007 x)
            (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_011 : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_005)
          (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
              (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv ∪
      ((Class.cab (nb074_alpha_dummy_005)
          (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
              (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_012 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_007 x)
          (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
              (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv ∪
      ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
              (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_013 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_006))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_014 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_006))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_015 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_008 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_016 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_008 x))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_013)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb074_alpha_dummy_013)) (syn_c1c))).fv ∪
      ((Class.cv (nb074_alpha_dummy_013))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_018 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb074_alpha_dummy_015 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb074_alpha_dummy_015 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_019 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_020 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_021 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb074_alpha_dummy_022 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_023 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_024 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb074_alpha_dummy_025 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_020))
          (Class.cv (nb074_alpha_dummy_021)))).fv ∪
      ((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_026 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_023 x))
          (Class.cv (nb074_alpha_dummy_024 x)))).fv ∪
      ((syn_cnin (Class.cv (nb074_alpha_dummy_023 x)) (Class.cv (nb074_alpha_dummy_024 x)))).fv)
    0)

@[expose]
noncomputable def nb074_alpha_dummy_027 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_028 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_024 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_029 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_020)))).fv ∪
      ((syn_ccompl (Class.cv (nb074_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_030 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_023 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb074_alpha_dummy_024 x)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_031 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_020))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_032 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_023 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_033 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_021))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_034 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_024 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_024 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_035 : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_005)
          (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005)
          (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_036 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_007 x)
          (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x)
          (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_037 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_006))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_038 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_039 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv ∪
      ((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_040 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv ∪
      ((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_041 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_042 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_043 (x : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_044 (x : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_045 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_046 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_047 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_043 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_048 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_043 x))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_049 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cphi (Class.cv (nb074_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_050 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_051 : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_045)
          (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
              (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv ∪
      ((Class.cab (nb074_alpha_dummy_045)
          (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
              (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_052 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_047 x)
          (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
              (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv ∪
      ((Class.cab (nb074_alpha_dummy_047 x)
          (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
              (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_053 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_046))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_054 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_046))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_055 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_048 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_056 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_048 x))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_057 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_053)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb074_alpha_dummy_053)) (syn_c1c))).fv ∪
      ((Class.cv (nb074_alpha_dummy_053))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_058 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_055 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb074_alpha_dummy_055 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb074_alpha_dummy_055 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_059 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_060 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_061 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb074_alpha_dummy_062 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_063 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_064 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb074_alpha_dummy_065 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_060))
          (Class.cv (nb074_alpha_dummy_061)))).fv ∪
      ((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_066 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_063 x))
          (Class.cv (nb074_alpha_dummy_064 x)))).fv ∪
      ((syn_cnin (Class.cv (nb074_alpha_dummy_063 x)) (Class.cv (nb074_alpha_dummy_064 x)))).fv)
    0)

@[expose]
noncomputable def nb074_alpha_dummy_067 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_068 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_064 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_069 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_060)))).fv ∪
      ((syn_ccompl (Class.cv (nb074_alpha_dummy_061)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_070 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_063 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb074_alpha_dummy_064 x)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_071 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_060))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_072 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_063 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_073 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_061))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_074 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_064 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_064 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_075 : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_045)
          (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045)
          (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_076 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_047 x)
          (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x)
          (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_077 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_046))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_078 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_079 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv ∪
      ((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_080 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv ∪
      ((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_081 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_082 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_000))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_083 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_084 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_085 : Var :=
  (freshVar
    (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000))
          (Class.cv (nb074_alpha_dummy_081)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_086 (x : Var) : Var :=
  (freshVar (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪
        ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x)
          (Class.cv (nb074_alpha_dummy_083 x)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_087 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_088 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_089 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_084 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_090 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_084 x))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_091 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cphi (Class.cv (nb074_alpha_dummy_088)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_092 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_093 : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_087)
          (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
              (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv ∪
      ((Class.cab (nb074_alpha_dummy_087)
          (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
              (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_094 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_089 x)
          (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
              (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv ∪
      ((Class.cab (nb074_alpha_dummy_089 x)
          (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
              (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_095 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_088))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_096 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_088))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_097 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_090 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_098 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_090 x))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_099 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_095)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb074_alpha_dummy_095)) (syn_c1c))).fv ∪
      ((Class.cv (nb074_alpha_dummy_095))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_100 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_097 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb074_alpha_dummy_097 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb074_alpha_dummy_097 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_101 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_102 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_103 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb074_alpha_dummy_104 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_105 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_106 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb074_alpha_dummy_107 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_102))
          (Class.cv (nb074_alpha_dummy_103)))).fv ∪
      ((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_108 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_105 x))
          (Class.cv (nb074_alpha_dummy_106 x)))).fv ∪
      ((syn_cnin (Class.cv (nb074_alpha_dummy_105 x)) (Class.cv (nb074_alpha_dummy_106 x)))).fv)
    0)

@[expose]
noncomputable def nb074_alpha_dummy_109 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_110 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_106 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_111 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_102)))).fv ∪
      ((syn_ccompl (Class.cv (nb074_alpha_dummy_103)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_112 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_105 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb074_alpha_dummy_106 x)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_113 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_102))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_114 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_105 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_115 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_103))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_116 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_106 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_106 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_117 : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_087)
          (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087)
          (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_118 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_089 x)
          (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x)
          (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_119 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_088))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_120 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_121 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv ∪
      ((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_122 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv ∪
      ((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_123 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_124 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_125 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_083 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_126 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_083 x))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_127 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cphi (Class.cv (nb074_alpha_dummy_124)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_128 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_129 : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_123)
          (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
              (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv ∪
      ((Class.cab (nb074_alpha_dummy_123)
          (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
              (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_130 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_125 x)
          (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
              (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv ∪
      ((Class.cab (nb074_alpha_dummy_125 x)
          (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
              (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_131 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_124))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_132 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_124))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_133 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_126 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_134 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_126 x))).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_135 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_131)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb074_alpha_dummy_131)) (syn_c1c))).fv ∪
      ((Class.cv (nb074_alpha_dummy_131))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_136 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_133 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb074_alpha_dummy_133 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb074_alpha_dummy_133 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_137 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_138 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_139 : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb074_alpha_dummy_140 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_141 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb074_alpha_dummy_142 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb074_alpha_dummy_143 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_138))
          (Class.cv (nb074_alpha_dummy_139)))).fv ∪
      ((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_144 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_141 x))
          (Class.cv (nb074_alpha_dummy_142 x)))).fv ∪
      ((syn_cnin (Class.cv (nb074_alpha_dummy_141 x)) (Class.cv (nb074_alpha_dummy_142 x)))).fv)
    0)

@[expose]
noncomputable def nb074_alpha_dummy_145 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_146 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_142 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_147 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_138)))).fv ∪
      ((syn_ccompl (Class.cv (nb074_alpha_dummy_139)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_148 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_141 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb074_alpha_dummy_142 x)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_149 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_138))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C074C001Part002`. -/


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
noncomputable def nb074_alpha_dummy_150 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_141 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_151 : Var :=
  (freshVar
    (((Class.cv (nb074_alpha_dummy_139))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_152 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074_alpha_dummy_142 x))).fv ∪
      ((Class.cv (nb074_alpha_dummy_142 x))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_153 : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_123)
          (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123)
          (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_154 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074_alpha_dummy_125 x)
          (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x)
          (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
              (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_155 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_124))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_156 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_157 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv ∪
      ((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv) 0)

@[expose]
noncomputable def nb074_alpha_dummy_158 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv ∪
      ((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv) 0)

theorem nb074_fresh_000 :
    (nb074_alpha_dummy_011) ∉
      (((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv)
      0

theorem nb074_fresh_001 :
    (nb074_alpha_dummy_035) ∉
      (((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb074_fresh_002 (x : Var) :
    (nb074_alpha_dummy_036 x) ∉
      (((Class.cab (nb074_alpha_dummy_007 x)
            (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x)
            (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_007 x)
            (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x)
            (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb074_fresh_003 (x : Var) :
    (nb074_alpha_dummy_012 x) ∉
      (((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv)
      0

theorem nb074_fresh_004 :
    (nb074_alpha_dummy_075) ∉
      (((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_075] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb074_fresh_005 :
    (nb074_alpha_dummy_051) ∉
      (((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_051] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv)
      0

theorem nb074_fresh_006 (x : Var) :
    (nb074_alpha_dummy_076 x) ∉
      (((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_076] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb074_fresh_007 (x : Var) :
    (nb074_alpha_dummy_052 x) ∉
      (((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_052] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv)
      0

theorem nb074_fresh_008 :
    (nb074_alpha_dummy_093) ∉
      (((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_093] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv)
      0

theorem nb074_fresh_009 :
    (nb074_alpha_dummy_117) ∉
      (((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_117] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb074_fresh_010 (x : Var) :
    (nb074_alpha_dummy_094 x) ∉
      (((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_094] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv)
      0

theorem nb074_fresh_011 (x : Var) :
    (nb074_alpha_dummy_118 x) ∉
      (((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_118] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb074_fresh_012 :
    (nb074_alpha_dummy_153) ∉
      (((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_153] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb074_fresh_013 :
    (nb074_alpha_dummy_129) ∉
      (((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_129] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv)
      0

theorem nb074_fresh_014 (x : Var) :
    (nb074_alpha_dummy_154 x) ∉
      (((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_154] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb074_fresh_015 (x : Var) :
    (nb074_alpha_dummy_130 x) ∉
      (((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_130] using
    freshVar_not_mem
      (((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv)
      0

theorem nb074_fresh_016 :
    (nb074_alpha_dummy_081) ∉ (((Class.cv (nb074_alpha_dummy_000))).fv) := by
  simpa only [nb074_alpha_dummy_081] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_000))).fv) 0

theorem nb074_fresh_017 :
    (nb074_alpha_dummy_082) ∉ (((Class.cv (nb074_alpha_dummy_000))).fv) := by
  simpa only [nb074_alpha_dummy_082] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_000))).fv) 1

theorem nb074_distinct_018 : (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_082) := by
  simpa only [nb074_alpha_dummy_081, nb074_alpha_dummy_082] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_019 :
    (nb074_alpha_dummy_005) ∉
      (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) :=
  by
  simpa only [nb074_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv)
      0

theorem nb074_fresh_020 :
    (nb074_alpha_dummy_006) ∉
      (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) :=
  by
  simpa only [nb074_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv)
      1

theorem nb074_distinct_021 : (nb074_alpha_dummy_005) ≠ (nb074_alpha_dummy_006) := by
  simpa only [nb074_alpha_dummy_005, nb074_alpha_dummy_006] using
    (freshVar_injective
      (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb074_fresh_022 :
    (nb074_alpha_dummy_013) ∉ (((Class.cv (nb074_alpha_dummy_006))).fv) := by
  simpa only [nb074_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_006))).fv) 0

theorem nb074_fresh_023 :
    (nb074_alpha_dummy_014) ∉ (((Class.cv (nb074_alpha_dummy_006))).fv) := by
  simpa only [nb074_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_006))).fv) 1

theorem nb074_distinct_024 : (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_014) := by
  simpa only [nb074_alpha_dummy_013, nb074_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_025 (x : Var) :
    (nb074_alpha_dummy_015 x) ∉ (((Class.cv (nb074_alpha_dummy_008 x))).fv) := by
  simpa only [nb074_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_008 x))).fv) 0

theorem nb074_fresh_026 (x : Var) :
    (nb074_alpha_dummy_016 x) ∉ (((Class.cv (nb074_alpha_dummy_008 x))).fv) := by
  simpa only [nb074_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_008 x))).fv) 1

theorem nb074_distinct_027 (x : Var) :
    (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_016 x) := by
  simpa only [nb074_alpha_dummy_015, nb074_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_008 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb074_fresh_028 :
    (nb074_alpha_dummy_019) ∉
      (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_029 :
    (nb074_alpha_dummy_020) ∉
      (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_030 :
    (nb074_alpha_dummy_021) ∉
      (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_031 : (nb074_alpha_dummy_019) ≠ (nb074_alpha_dummy_020) := by
  simpa only [nb074_alpha_dummy_019, nb074_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_032 : (nb074_alpha_dummy_019) ≠ (nb074_alpha_dummy_021) := by
  simpa only [nb074_alpha_dummy_019, nb074_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_033 : (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_021) := by
  simpa only [nb074_alpha_dummy_020, nb074_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_034 (x : Var) :
    (nb074_alpha_dummy_022 x) ∉
      (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_035 (x : Var) :
    (nb074_alpha_dummy_023 x) ∉
      (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_036 (x : Var) :
    (nb074_alpha_dummy_024 x) ∉
      (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_037 (x : Var) :
    (nb074_alpha_dummy_022 x) ≠ (nb074_alpha_dummy_023 x) := by
  simpa only [nb074_alpha_dummy_022, nb074_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_038 (x : Var) :
    (nb074_alpha_dummy_022 x) ≠ (nb074_alpha_dummy_024 x) := by
  simpa only [nb074_alpha_dummy_022, nb074_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_039 (x : Var) :
    (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_024 x) := by
  simpa only [nb074_alpha_dummy_023, nb074_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_040 :
    (nb074_alpha_dummy_031) ∉
      (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_020))).fv) :=
  by
  simpa only [nb074_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_020))).fv)
      0

theorem nb074_fresh_041 :
    (nb074_alpha_dummy_027) ∉
      (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) :=
  by
  simpa only [nb074_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv)
      0

theorem nb074_fresh_042 :
    (nb074_alpha_dummy_033) ∉
      (((Class.cv (nb074_alpha_dummy_021))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) :=
  by
  simpa only [nb074_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_021))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv)
      0

theorem nb074_fresh_043 (x : Var) :
    (nb074_alpha_dummy_032 x) ∉
      (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_023 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_023 x))).fv)
      0

theorem nb074_fresh_044 (x : Var) :
    (nb074_alpha_dummy_028 x) ∉
      (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv)
      0

theorem nb074_fresh_045 (x : Var) :
    (nb074_alpha_dummy_034 x) ∉
      (((Class.cv (nb074_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv)
      0

theorem nb074_fresh_046 :
    (nb074_alpha_dummy_045) ∉
      (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) :=
  by
  simpa only [nb074_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv)
      0

theorem nb074_fresh_047 :
    (nb074_alpha_dummy_046) ∉
      (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) :=
  by
  simpa only [nb074_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv)
      1

theorem nb074_distinct_048 : (nb074_alpha_dummy_045) ≠ (nb074_alpha_dummy_046) := by
  simpa only [nb074_alpha_dummy_045, nb074_alpha_dummy_046] using
    (freshVar_injective
      (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb074_fresh_049 (x : Var) :
    (nb074_alpha_dummy_047 x) ∉
      (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_047] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv)
      0

theorem nb074_fresh_050 (x : Var) :
    (nb074_alpha_dummy_048 x) ∉
      (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_048] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv)
      1

theorem nb074_distinct_051 (x : Var) :
    (nb074_alpha_dummy_047 x) ≠ (nb074_alpha_dummy_048 x) := by
  simpa only [nb074_alpha_dummy_047, nb074_alpha_dummy_048] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪
        ((Class.cv (nb074_alpha_dummy_043 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_052 :
    (nb074_alpha_dummy_053) ∉ (((Class.cv (nb074_alpha_dummy_046))).fv) := by
  simpa only [nb074_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_046))).fv) 0

theorem nb074_fresh_053 :
    (nb074_alpha_dummy_054) ∉ (((Class.cv (nb074_alpha_dummy_046))).fv) := by
  simpa only [nb074_alpha_dummy_054] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_046))).fv) 1

theorem nb074_distinct_054 : (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_054) := by
  simpa only [nb074_alpha_dummy_053, nb074_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_046))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_055 (x : Var) :
    (nb074_alpha_dummy_055 x) ∉ (((Class.cv (nb074_alpha_dummy_048 x))).fv) := by
  simpa only [nb074_alpha_dummy_055] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_048 x))).fv) 0

theorem nb074_fresh_056 (x : Var) :
    (nb074_alpha_dummy_056 x) ∉ (((Class.cv (nb074_alpha_dummy_048 x))).fv) := by
  simpa only [nb074_alpha_dummy_056] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_048 x))).fv) 1

theorem nb074_distinct_057 (x : Var) :
    (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_056 x) := by
  simpa only [nb074_alpha_dummy_055, nb074_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_048 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb074_fresh_058 :
    (nb074_alpha_dummy_059) ∉
      (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_059 :
    (nb074_alpha_dummy_060) ∉
      (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_060 :
    (nb074_alpha_dummy_061) ∉
      (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_061 : (nb074_alpha_dummy_059) ≠ (nb074_alpha_dummy_060) := by
  simpa only [nb074_alpha_dummy_059, nb074_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_062 : (nb074_alpha_dummy_059) ≠ (nb074_alpha_dummy_061) := by
  simpa only [nb074_alpha_dummy_059, nb074_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_063 : (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_061) := by
  simpa only [nb074_alpha_dummy_060, nb074_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_064 (x : Var) :
    (nb074_alpha_dummy_062 x) ∉
      (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_062] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_065 (x : Var) :
    (nb074_alpha_dummy_063 x) ∉
      (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_063] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_066 (x : Var) :
    (nb074_alpha_dummy_064 x) ∉
      (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_064] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_067 (x : Var) :
    (nb074_alpha_dummy_062 x) ≠ (nb074_alpha_dummy_063 x) := by
  simpa only [nb074_alpha_dummy_062, nb074_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_068 (x : Var) :
    (nb074_alpha_dummy_062 x) ≠ (nb074_alpha_dummy_064 x) := by
  simpa only [nb074_alpha_dummy_062, nb074_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_069 (x : Var) :
    (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_064 x) := by
  simpa only [nb074_alpha_dummy_063, nb074_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_070 :
    (nb074_alpha_dummy_071) ∉
      (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_060))).fv) :=
  by
  simpa only [nb074_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_060))).fv)
      0

theorem nb074_fresh_071 :
    (nb074_alpha_dummy_067) ∉
      (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) :=
  by
  simpa only [nb074_alpha_dummy_067] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv)
      0

theorem nb074_fresh_072 :
    (nb074_alpha_dummy_073) ∉
      (((Class.cv (nb074_alpha_dummy_061))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) :=
  by
  simpa only [nb074_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_061))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv)
      0

theorem nb074_fresh_073 (x : Var) :
    (nb074_alpha_dummy_072 x) ∉
      (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_063 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_063 x))).fv)
      0

theorem nb074_fresh_074 (x : Var) :
    (nb074_alpha_dummy_068 x) ∉
      (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv)
      0

theorem nb074_fresh_075 (x : Var) :
    (nb074_alpha_dummy_074 x) ∉
      (((Class.cv (nb074_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_074] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv)
      0

theorem nb074_fresh_076 :
    (nb074_alpha_dummy_087) ∉
      (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) :=
  by
  simpa only [nb074_alpha_dummy_087] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv)
      0

theorem nb074_fresh_077 :
    (nb074_alpha_dummy_088) ∉
      (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) :=
  by
  simpa only [nb074_alpha_dummy_088] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv)
      1

theorem nb074_distinct_078 : (nb074_alpha_dummy_087) ≠ (nb074_alpha_dummy_088) := by
  simpa only [nb074_alpha_dummy_087, nb074_alpha_dummy_088] using
    (freshVar_injective
      (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb074_fresh_079 :
    (nb074_alpha_dummy_123) ∉
      (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) :=
  by
  simpa only [nb074_alpha_dummy_123] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv)
      0

theorem nb074_fresh_080 :
    (nb074_alpha_dummy_124) ∉
      (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) :=
  by
  simpa only [nb074_alpha_dummy_124] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv)
      1

theorem nb074_distinct_081 : (nb074_alpha_dummy_123) ≠ (nb074_alpha_dummy_124) := by
  simpa only [nb074_alpha_dummy_123, nb074_alpha_dummy_124] using
    (freshVar_injective
      (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb074_fresh_082 (x : Var) :
    (nb074_alpha_dummy_089 x) ∉
      (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_089] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv)
      0

theorem nb074_fresh_083 (x : Var) :
    (nb074_alpha_dummy_090 x) ∉
      (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_090] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv)
      1

theorem nb074_distinct_084 (x : Var) :
    (nb074_alpha_dummy_089 x) ≠ (nb074_alpha_dummy_090 x) := by
  simpa only [nb074_alpha_dummy_089, nb074_alpha_dummy_090] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪
        ((Class.cv (nb074_alpha_dummy_084 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_085 (x : Var) :
    (nb074_alpha_dummy_125 x) ∉
      (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_125] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv)
      0

theorem nb074_fresh_086 (x : Var) :
    (nb074_alpha_dummy_126 x) ∉
      (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_126] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv)
      1

theorem nb074_distinct_087 (x : Var) :
    (nb074_alpha_dummy_125 x) ≠ (nb074_alpha_dummy_126 x) := by
  simpa only [nb074_alpha_dummy_125, nb074_alpha_dummy_126] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪
        ((Class.cv (nb074_alpha_dummy_083 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_088 :
    (nb074_alpha_dummy_095) ∉ (((Class.cv (nb074_alpha_dummy_088))).fv) := by
  simpa only [nb074_alpha_dummy_095] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_088))).fv) 0

theorem nb074_fresh_089 :
    (nb074_alpha_dummy_096) ∉ (((Class.cv (nb074_alpha_dummy_088))).fv) := by
  simpa only [nb074_alpha_dummy_096] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_088))).fv) 1

theorem nb074_distinct_090 : (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_096) := by
  simpa only [nb074_alpha_dummy_095, nb074_alpha_dummy_096] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_088))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_091 (x : Var) :
    (nb074_alpha_dummy_097 x) ∉ (((Class.cv (nb074_alpha_dummy_090 x))).fv) := by
  simpa only [nb074_alpha_dummy_097] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_090 x))).fv) 0

theorem nb074_fresh_092 (x : Var) :
    (nb074_alpha_dummy_098 x) ∉ (((Class.cv (nb074_alpha_dummy_090 x))).fv) := by
  simpa only [nb074_alpha_dummy_098] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_090 x))).fv) 1

theorem nb074_distinct_093 (x : Var) :
    (nb074_alpha_dummy_097 x) ≠ (nb074_alpha_dummy_098 x) := by
  simpa only [nb074_alpha_dummy_097, nb074_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_090 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb074_fresh_094 :
    (nb074_alpha_dummy_101) ∉
      (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_101] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_095 :
    (nb074_alpha_dummy_102) ∉
      (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_102] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_096 :
    (nb074_alpha_dummy_103) ∉
      (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_103] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_097 : (nb074_alpha_dummy_101) ≠ (nb074_alpha_dummy_102) := by
  simpa only [nb074_alpha_dummy_101, nb074_alpha_dummy_102] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_098 : (nb074_alpha_dummy_101) ≠ (nb074_alpha_dummy_103) := by
  simpa only [nb074_alpha_dummy_101, nb074_alpha_dummy_103] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_099 : (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_103) := by
  simpa only [nb074_alpha_dummy_102, nb074_alpha_dummy_103] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_100 (x : Var) :
    (nb074_alpha_dummy_104 x) ∉
      (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_104] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_101 (x : Var) :
    (nb074_alpha_dummy_105 x) ∉
      (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_105] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_102 (x : Var) :
    (nb074_alpha_dummy_106 x) ∉
      (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_106] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_103 (x : Var) :
    (nb074_alpha_dummy_104 x) ≠ (nb074_alpha_dummy_105 x) := by
  simpa only [nb074_alpha_dummy_104, nb074_alpha_dummy_105] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_104 (x : Var) :
    (nb074_alpha_dummy_104 x) ≠ (nb074_alpha_dummy_106 x) := by
  simpa only [nb074_alpha_dummy_104, nb074_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_105 (x : Var) :
    (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_106 x) := by
  simpa only [nb074_alpha_dummy_105, nb074_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_106 :
    (nb074_alpha_dummy_113) ∉
      (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_102))).fv) :=
  by
  simpa only [nb074_alpha_dummy_113] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_102))).fv)
      0

theorem nb074_fresh_107 :
    (nb074_alpha_dummy_109) ∉
      (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) :=
  by
  simpa only [nb074_alpha_dummy_109] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv)
      0

theorem nb074_fresh_108 :
    (nb074_alpha_dummy_115) ∉
      (((Class.cv (nb074_alpha_dummy_103))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) :=
  by
  simpa only [nb074_alpha_dummy_115] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_103))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv)
      0

theorem nb074_fresh_109 (x : Var) :
    (nb074_alpha_dummy_114 x) ∉
      (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_105 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_114] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_105 x))).fv)
      0

theorem nb074_fresh_110 (x : Var) :
    (nb074_alpha_dummy_110 x) ∉
      (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_110] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv)
      0

theorem nb074_fresh_111 (x : Var) :
    (nb074_alpha_dummy_116 x) ∉
      (((Class.cv (nb074_alpha_dummy_106 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_116] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_106 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv)
      0

theorem nb074_fresh_112 :
    (nb074_alpha_dummy_131) ∉ (((Class.cv (nb074_alpha_dummy_124))).fv) := by
  simpa only [nb074_alpha_dummy_131] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_124))).fv) 0

theorem nb074_fresh_113 :
    (nb074_alpha_dummy_132) ∉ (((Class.cv (nb074_alpha_dummy_124))).fv) := by
  simpa only [nb074_alpha_dummy_132] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_124))).fv) 1

theorem nb074_distinct_114 : (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_132) := by
  simpa only [nb074_alpha_dummy_131, nb074_alpha_dummy_132] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_124))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_115 (x : Var) :
    (nb074_alpha_dummy_133 x) ∉ (((Class.cv (nb074_alpha_dummy_126 x))).fv) := by
  simpa only [nb074_alpha_dummy_133] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_126 x))).fv) 0

theorem nb074_fresh_116 (x : Var) :
    (nb074_alpha_dummy_134 x) ∉ (((Class.cv (nb074_alpha_dummy_126 x))).fv) := by
  simpa only [nb074_alpha_dummy_134] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_126 x))).fv) 1

theorem nb074_distinct_117 (x : Var) :
    (nb074_alpha_dummy_133 x) ≠ (nb074_alpha_dummy_134 x) := by
  simpa only [nb074_alpha_dummy_133, nb074_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_126 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb074_fresh_118 :
    (nb074_alpha_dummy_137) ∉
      (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_137] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_119 :
    (nb074_alpha_dummy_138) ∉
      (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_138] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_120 :
    (nb074_alpha_dummy_139) ∉
      (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_139] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_121 : (nb074_alpha_dummy_137) ≠ (nb074_alpha_dummy_138) := by
  simpa only [nb074_alpha_dummy_137, nb074_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_122 : (nb074_alpha_dummy_137) ≠ (nb074_alpha_dummy_139) := by
  simpa only [nb074_alpha_dummy_137, nb074_alpha_dummy_139] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_123 : (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_139) := by
  simpa only [nb074_alpha_dummy_138, nb074_alpha_dummy_139] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_124 (x : Var) :
    (nb074_alpha_dummy_140 x) ∉
      (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_140] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_125 (x : Var) :
    (nb074_alpha_dummy_141 x) ∉
      (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_141] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_126 (x : Var) :
    (nb074_alpha_dummy_142 x) ∉
      (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb074_alpha_dummy_142] using
    freshVar_not_mem (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_127 (x : Var) :
    (nb074_alpha_dummy_140 x) ≠ (nb074_alpha_dummy_141 x) := by
  simpa only [nb074_alpha_dummy_140, nb074_alpha_dummy_141] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_128 (x : Var) :
    (nb074_alpha_dummy_140 x) ≠ (nb074_alpha_dummy_142 x) := by
  simpa only [nb074_alpha_dummy_140, nb074_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_129 (x : Var) :
    (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_142 x) := by
  simpa only [nb074_alpha_dummy_141, nb074_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_130 :
    (nb074_alpha_dummy_149) ∉
      (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_138))).fv) :=
  by
  simpa only [nb074_alpha_dummy_149] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_138))).fv)
      0

theorem nb074_fresh_131 :
    (nb074_alpha_dummy_145) ∉
      (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) :=
  by
  simpa only [nb074_alpha_dummy_145] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv)
      0

theorem nb074_fresh_132 :
    (nb074_alpha_dummy_151) ∉
      (((Class.cv (nb074_alpha_dummy_139))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) :=
  by
  simpa only [nb074_alpha_dummy_151] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_139))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv)
      0

theorem nb074_fresh_133 (x : Var) :
    (nb074_alpha_dummy_150 x) ∉
      (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_141 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_150] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_141 x))).fv)
      0

theorem nb074_fresh_134 (x : Var) :
    (nb074_alpha_dummy_146 x) ∉
      (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_146] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv)
      0

theorem nb074_fresh_135 (x : Var) :
    (nb074_alpha_dummy_152 x) ∉
      (((Class.cv (nb074_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_152] using
    freshVar_not_mem
      (((Class.cv (nb074_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv)
      0

theorem nb074_fresh_136 (x : Var) : (nb074_alpha_dummy_083 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb074_alpha_dummy_083] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb074_fresh_137 (x : Var) : (nb074_alpha_dummy_084 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb074_alpha_dummy_084] using freshVar_not_mem (((Class.cv x)).fv) 1

theorem nb074_distinct_138 (x : Var) :
    (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_084 x) := by
  simpa only [nb074_alpha_dummy_083, nb074_alpha_dummy_084] using
    (freshVar_injective (((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_139 (x : Var) :
    (nb074_alpha_dummy_007 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) 0

theorem nb074_fresh_140 (x : Var) :
    (nb074_alpha_dummy_008 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C074C001Part003`. -/


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

theorem nb074_distinct_141 (x : Var) :
    (nb074_alpha_dummy_007 x) ≠ (nb074_alpha_dummy_008 x) := by
  simpa only [nb074_alpha_dummy_007, nb074_alpha_dummy_008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb074_fresh_142 :
    (nb074_alpha_dummy_017) ∉
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_013))).fv) :=
  by
  simpa only [nb074_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_013))).fv)
      0

theorem nb074_fresh_143 (x : Var) :
    (nb074_alpha_dummy_018 x) ∉
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_015 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_015 x))).fv)
      0

theorem nb074_fresh_144 :
    (nb074_alpha_dummy_057) ∉
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_053)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_053)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_053))).fv) :=
  by
  simpa only [nb074_alpha_dummy_057] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_053)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_053)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_053))).fv)
      0

theorem nb074_fresh_145 (x : Var) :
    (nb074_alpha_dummy_058 x) ∉
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_055 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_055 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_055 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_058] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_055 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_055 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_055 x))).fv)
      0

theorem nb074_fresh_146 :
    (nb074_alpha_dummy_099) ∉
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_095)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_095)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_095))).fv) :=
  by
  simpa only [nb074_alpha_dummy_099] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_095)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_095)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_095))).fv)
      0

theorem nb074_fresh_147 (x : Var) :
    (nb074_alpha_dummy_100 x) ∉
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_097 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_097 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_097 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_100] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_097 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_097 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_097 x))).fv)
      0

theorem nb074_fresh_148 :
    (nb074_alpha_dummy_135) ∉
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_131)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_131)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_131))).fv) :=
  by
  simpa only [nb074_alpha_dummy_135] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_131)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_131)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_131))).fv)
      0

theorem nb074_fresh_149 (x : Var) :
    (nb074_alpha_dummy_136 x) ∉
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_133 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_133 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_133 x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_136] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_133 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_133 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_133 x))).fv)
      0

theorem nb074_fresh_150 :
    (nb074_alpha_dummy_041) ∉
      (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb074_alpha_dummy_041] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv)
      0

theorem nb074_fresh_151 :
    (nb074_alpha_dummy_042) ∉
      (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb074_alpha_dummy_042] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv)
      1

theorem nb074_distinct_152 : (nb074_alpha_dummy_041) ≠ (nb074_alpha_dummy_042) := by
  simpa only [nb074_alpha_dummy_041, nb074_alpha_dummy_042] using
    (freshVar_injective
      (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb074_fresh_153 (x : Var) :
    (nb074_alpha_dummy_043 x) ∉ (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb074_alpha_dummy_043] using
    freshVar_not_mem (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) 0

theorem nb074_fresh_154 (x : Var) :
    (nb074_alpha_dummy_044 x) ∉ (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb074_alpha_dummy_044] using
    freshVar_not_mem (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) 1

theorem nb074_distinct_155 (x : Var) :
    (nb074_alpha_dummy_043 x) ≠ (nb074_alpha_dummy_044 x) := by
  simpa only [nb074_alpha_dummy_043, nb074_alpha_dummy_044] using
    (freshVar_injective (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb074_fresh_156 :
    (nb074_alpha_dummy_009) ∉
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_005)
              (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_005)
              (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_005)
              (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_005)
              (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb074_fresh_157 (x : Var) :
    (nb074_alpha_dummy_010 x) ∉
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x)
              (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_007 x)
              (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x)
              (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_007 x)
              (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb074_fresh_158 :
    (nb074_alpha_dummy_049) ∉
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_045)
              (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_045)
              (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_045)
              (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_045)
              (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb074_fresh_159 (x : Var) :
    (nb074_alpha_dummy_050 x) ∉
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x)
              (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_047 x)
              (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_050] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x)
              (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_047 x)
              (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb074_fresh_160 :
    (nb074_alpha_dummy_091) ∉
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_087)
              (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_088)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_087)
              (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_091] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_087)
              (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_088)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_087)
              (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb074_fresh_161 (x : Var) :
    (nb074_alpha_dummy_092 x) ∉
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x)
              (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_089 x)
              (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_092] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x)
              (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_089 x)
              (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb074_fresh_162 :
    (nb074_alpha_dummy_127) ∉
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_123)
              (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_124)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_123)
              (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_127] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_123)
              (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_124)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_123)
              (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb074_fresh_163 (x : Var) :
    (nb074_alpha_dummy_128 x) ∉
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x)
              (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_125 x)
              (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_128] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x)
              (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_125 x)
              (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb074_fresh_164 :
    (nb074_alpha_dummy_029) ∉
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_021)))).fv)
      0

theorem nb074_fresh_165 (x : Var) :
    (nb074_alpha_dummy_030 x) ∉
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_024 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_024 x)))).fv)
      0

theorem nb074_fresh_166 :
    (nb074_alpha_dummy_069) ∉
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_061)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_069] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_061)))).fv)
      0

theorem nb074_fresh_167 (x : Var) :
    (nb074_alpha_dummy_070 x) ∉
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_063 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_064 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_070] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_063 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_064 x)))).fv)
      0

theorem nb074_fresh_168 :
    (nb074_alpha_dummy_111) ∉
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_102)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_103)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_111] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_102)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_103)))).fv)
      0

theorem nb074_fresh_169 (x : Var) :
    (nb074_alpha_dummy_112 x) ∉
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_105 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_106 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_112] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_105 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_106 x)))).fv)
      0

theorem nb074_fresh_170 :
    (nb074_alpha_dummy_147) ∉
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_138)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_139)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_147] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_138)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_139)))).fv)
      0

theorem nb074_fresh_171 (x : Var) :
    (nb074_alpha_dummy_148 x) ∉
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_141 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_142 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_148] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_141 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_142 x)))).fv)
      0

theorem nb074_fresh_172 :
    (nb074_alpha_dummy_037) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb074_fresh_173 (x : Var) :
    (nb074_alpha_dummy_038 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb074_fresh_174 :
    (nb074_alpha_dummy_077) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_046))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_046))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb074_fresh_175 (x : Var) :
    (nb074_alpha_dummy_078 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_078] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb074_fresh_176 :
    (nb074_alpha_dummy_119) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_088))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_119] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_088))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb074_fresh_177 (x : Var) :
    (nb074_alpha_dummy_120 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_120] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb074_fresh_178 :
    (nb074_alpha_dummy_155) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_124))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_155] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_124))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb074_fresh_179 (x : Var) :
    (nb074_alpha_dummy_156 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_156] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb074_fresh_180 :
    (nb074_alpha_dummy_025) ∉
      (((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_020))
            (Class.cv (nb074_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv)
      0

theorem nb074_fresh_181 (x : Var) :
    (nb074_alpha_dummy_026 x) ∉
      (((syn_cnin (Class.cv (nb074_alpha_dummy_023 x))
            (Class.cv (nb074_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_023 x))
            (Class.cv (nb074_alpha_dummy_024 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb074_alpha_dummy_023 x))
            (Class.cv (nb074_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_023 x))
            (Class.cv (nb074_alpha_dummy_024 x)))).fv)
      0

theorem nb074_fresh_182 :
    (nb074_alpha_dummy_065) ∉
      (((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_060))
            (Class.cv (nb074_alpha_dummy_061)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_065] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv)
      0

theorem nb074_fresh_183 (x : Var) :
    (nb074_alpha_dummy_066 x) ∉
      (((syn_cnin (Class.cv (nb074_alpha_dummy_063 x))
            (Class.cv (nb074_alpha_dummy_064 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_063 x))
            (Class.cv (nb074_alpha_dummy_064 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_066] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb074_alpha_dummy_063 x))
            (Class.cv (nb074_alpha_dummy_064 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_063 x))
            (Class.cv (nb074_alpha_dummy_064 x)))).fv)
      0

theorem nb074_fresh_184 :
    (nb074_alpha_dummy_107) ∉
      (((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_102))
            (Class.cv (nb074_alpha_dummy_103)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_107] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv)
      0

theorem nb074_fresh_185 (x : Var) :
    (nb074_alpha_dummy_108 x) ∉
      (((syn_cnin (Class.cv (nb074_alpha_dummy_105 x))
            (Class.cv (nb074_alpha_dummy_106 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_105 x))
            (Class.cv (nb074_alpha_dummy_106 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_108] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb074_alpha_dummy_105 x))
            (Class.cv (nb074_alpha_dummy_106 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_105 x))
            (Class.cv (nb074_alpha_dummy_106 x)))).fv)
      0

theorem nb074_fresh_186 :
    (nb074_alpha_dummy_143) ∉
      (((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_138))
            (Class.cv (nb074_alpha_dummy_139)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_143] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv)
      0

theorem nb074_fresh_187 (x : Var) :
    (nb074_alpha_dummy_144 x) ∉
      (((syn_cnin (Class.cv (nb074_alpha_dummy_141 x))
            (Class.cv (nb074_alpha_dummy_142 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_141 x))
            (Class.cv (nb074_alpha_dummy_142 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_144] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb074_alpha_dummy_141 x))
            (Class.cv (nb074_alpha_dummy_142 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_141 x))
            (Class.cv (nb074_alpha_dummy_142 x)))).fv)
      0

theorem nb074_fresh_188 :
    (nb074_alpha_dummy_039) ∉
      (((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv)
      0

theorem nb074_fresh_189 (x : Var) :
    (nb074_alpha_dummy_040 x) ∉
      (((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv)
      0

theorem nb074_fresh_190 :
    (nb074_alpha_dummy_079) ∉
      (((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_079] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv)
      0

theorem nb074_fresh_191 (x : Var) :
    (nb074_alpha_dummy_080 x) ∉
      (((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_080] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv)
      0

theorem nb074_fresh_192 :
    (nb074_alpha_dummy_121) ∉
      (((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_121] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv)
      0

theorem nb074_fresh_193 (x : Var) :
    (nb074_alpha_dummy_122 x) ∉
      (((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_122] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv)
      0

theorem nb074_fresh_194 :
    (nb074_alpha_dummy_157) ∉
      (((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_157] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv)
      0

theorem nb074_fresh_195 (x : Var) :
    (nb074_alpha_dummy_158 x) ∉
      (((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_158] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv)
      0

theorem nb074_fresh_196 :
    (nb074_alpha_dummy_001) ∉
      (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cdm (Class.cv (nb074_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_001] using
    freshVar_not_mem
      (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cdm (Class.cv (nb074_alpha_dummy_000)))).fv)
      0

theorem nb074_fresh_197 :
    (nb074_alpha_dummy_003) ∉
      (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ({(nb074_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb074_alpha_dummy_000)) (syn_cvv))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_001))
              (syn_cdm (Class.cv (nb074_alpha_dummy_000)))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_003] using
    freshVar_not_mem
      (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ({(nb074_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb074_alpha_dummy_000)) (syn_cvv))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_001))
              (syn_cdm (Class.cv (nb074_alpha_dummy_000)))))).fv)
      0

theorem nb074_fresh_198 :
    (nb074_alpha_dummy_085) ∉
      (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000))
            (Class.cv (nb074_alpha_dummy_081)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_085] using
    freshVar_not_mem
      (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000))
            (Class.cv (nb074_alpha_dummy_081)))).fv)
      0

theorem nb074_fresh_199 (x : Var) :
    (nb074_alpha_dummy_086 x) ∉
      (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪ ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x)
            (Class.cv (nb074_alpha_dummy_083 x)))).fv) :=
  by
  simpa only [nb074_alpha_dummy_086] using
    freshVar_not_mem
      (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪ ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x)
            (Class.cv (nb074_alpha_dummy_083 x)))).fv)
      0

theorem nb074_fresh_200 (x : Var) :
    (nb074_alpha_dummy_002 x) ∉
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv x))).fv) :=
  by
  simpa only [nb074_alpha_dummy_002] using
    freshVar_not_mem (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv x))).fv)
      0

theorem nb074_fresh_201 (x : Var) :
    (nb074_alpha_dummy_004 x) ∉
      (({ x } : Finset Var) ∪ ({(nb074_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_002 x)) (syn_cdm (Class.cv x))))).fv) :=
  by
  simpa only [nb074_alpha_dummy_004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({(nb074_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_002 x)) (syn_cdm (Class.cv x))))).fv)
      0

theorem nb074_fresh_202 : (nb074_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb074_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb074_support_mem_0000 :
    (nb074_alpha_dummy_000) ∈
      (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ({(nb074_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb074_alpha_dummy_000)) (syn_cvv))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_001))
              (syn_cdm (Class.cv (nb074_alpha_dummy_000)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0001 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({(nb074_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_002 x)) (syn_cdm (Class.cv x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0002 :
    (nb074_alpha_dummy_001) ∈
      (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ({(nb074_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb074_alpha_dummy_000)) (syn_cvv))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_001))
              (syn_cdm (Class.cv (nb074_alpha_dummy_000)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0003 (x : Var) :
    (nb074_alpha_dummy_002 x) ∈
      (({ x } : Finset Var) ∪ ({(nb074_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
            (Wff.classEq (Class.cv (nb074_alpha_dummy_002 x)) (syn_cdm (Class.cv x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0004 :
    (nb074_alpha_dummy_000) ∈
      (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cdm (Class.cv (nb074_alpha_dummy_000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0005 (x : Var) :
    x ∈ (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0006 :
    (nb074_alpha_dummy_000) ∈
      (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0007 :
    (nb074_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_005)
              (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_005)
              (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_005) from (by
          unfold nb074_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_006) from (by
            unfold nb074_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0008 (x : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0009 (x : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x)
              (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_007 x)
              (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb074_alpha_dummy_007 x) from (by
          unfold nb074_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb074_alpha_dummy_008 x) from (by
            unfold nb074_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0010 :
    (nb074_alpha_dummy_000) ∈
      (((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_005) from (by
          unfold nb074_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_006) from (by
            unfold nb074_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0011 (x : Var) :
    x ∈
      (((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb074_alpha_dummy_007 x) from (by
          unfold nb074_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb074_alpha_dummy_008 x) from (by
            unfold nb074_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0012 :
    (nb074_alpha_dummy_006) ∈ (((Class.cv (nb074_alpha_dummy_006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0013 (x : Var) :
    (nb074_alpha_dummy_008 x) ∈ (((Class.cv (nb074_alpha_dummy_008 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0014 :
    (nb074_alpha_dummy_013) ∈
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_013))).fv) :=
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

theorem nb074_support_mem_0015 (x : Var) :
    (nb074_alpha_dummy_015 x) ∈
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_015 x))).fv) :=
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

theorem nb074_support_mem_0016 :
    (nb074_alpha_dummy_013) ∈
      (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0017 (x : Var) :
    (nb074_alpha_dummy_015 x) ∈
      (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0018 :
    (nb074_alpha_dummy_020) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_020))
            (Class.cv (nb074_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0019 (x : Var) :
    (nb074_alpha_dummy_023 x) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_023 x))
            (Class.cv (nb074_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_023 x))
            (Class.cv (nb074_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0020 :
    (nb074_alpha_dummy_020) ∈
      (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0021 (x : Var) :
    (nb074_alpha_dummy_023 x) ∈
      (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0022 :
    (nb074_alpha_dummy_021) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_020))
            (Class.cv (nb074_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0023 (x : Var) :
    (nb074_alpha_dummy_024 x) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_023 x))
            (Class.cv (nb074_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_023 x))
            (Class.cv (nb074_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0024 :
    (nb074_alpha_dummy_021) ∈
      (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0025 (x : Var) :
    (nb074_alpha_dummy_024 x) ∈
      (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0026 :
    (nb074_alpha_dummy_020) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0027 (x : Var) :
    (nb074_alpha_dummy_023 x) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0028 :
    (nb074_alpha_dummy_020) ∈
      (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0029 (x : Var) :
    (nb074_alpha_dummy_023 x) ∈
      (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_023 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0030 :
    (nb074_alpha_dummy_021) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0031 (x : Var) :
    (nb074_alpha_dummy_024 x) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0032 :
    (nb074_alpha_dummy_021) ∈
      (((Class.cv (nb074_alpha_dummy_021))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0033 (x : Var) :
    (nb074_alpha_dummy_024 x) ∈
      (((Class.cv (nb074_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0034 :
    (nb074_alpha_dummy_001) ∈
      (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0035 :
    (nb074_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_005)
              (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_005)
              (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_001) ≠ (nb074_alpha_dummy_005) from (by
          unfold nb074_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_001) ≠ (nb074_alpha_dummy_006) from (by
            unfold nb074_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0036 (x : Var) :
    (nb074_alpha_dummy_002 x) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0037 (x : Var) :
    (nb074_alpha_dummy_002 x) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x)
              (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_007 x)
              (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_002 x) ≠ (nb074_alpha_dummy_007 x) from (by
          unfold nb074_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_002 x) ≠ (nb074_alpha_dummy_008 x) from (by
            unfold nb074_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0038 :
    (nb074_alpha_dummy_001) ∈
      (((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_001) ≠ (nb074_alpha_dummy_005) from (by
          unfold nb074_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_001) ≠ (nb074_alpha_dummy_006) from (by
            unfold nb074_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0039 (x : Var) :
    (nb074_alpha_dummy_002 x) ∈
      (((Class.cab (nb074_alpha_dummy_007 x)
            (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x)
            (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_002 x) ≠ (nb074_alpha_dummy_007 x) from (by
          unfold nb074_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_002 x) ≠ (nb074_alpha_dummy_008 x) from (by
            unfold nb074_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0040 :
    (nb074_alpha_dummy_006) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0041 (x : Var) :
    (nb074_alpha_dummy_008 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0042 :
    (nb074_alpha_dummy_006) ∈
      (((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0043 (x : Var) :
    (nb074_alpha_dummy_008 x) ∈
      (((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0044 :
    (nb074_alpha_dummy_042) ∈
      (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0045 :
    (nb074_alpha_dummy_042) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_045)
              (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_045)
              (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_045) from (by
          unfold nb074_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_046) from (by
            unfold nb074_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0046 (x : Var) :
    (nb074_alpha_dummy_044 x) ∈
      (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0047 (x : Var) :
    (nb074_alpha_dummy_044 x) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x)
              (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_047 x)
              (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_047 x) from (by
          unfold nb074_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_048 x) from (by
            unfold nb074_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0048 :
    (nb074_alpha_dummy_042) ∈
      (((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_045) from (by
          unfold nb074_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_046) from (by
            unfold nb074_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0049 (x : Var) :
    (nb074_alpha_dummy_044 x) ∈
      (((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_047 x) from (by
          unfold nb074_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_048 x) from (by
            unfold nb074_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0050 :
    (nb074_alpha_dummy_046) ∈ (((Class.cv (nb074_alpha_dummy_046))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0051 (x : Var) :
    (nb074_alpha_dummy_048 x) ∈ (((Class.cv (nb074_alpha_dummy_048 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0052 :
    (nb074_alpha_dummy_053) ∈
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_053)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_053)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_053))).fv) :=
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

theorem nb074_support_mem_0053 (x : Var) :
    (nb074_alpha_dummy_055 x) ∈
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_055 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_055 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_055 x))).fv) :=
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

theorem nb074_support_mem_0054 :
    (nb074_alpha_dummy_053) ∈
      (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0055 (x : Var) :
    (nb074_alpha_dummy_055 x) ∈
      (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0056 :
    (nb074_alpha_dummy_060) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_060))
            (Class.cv (nb074_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0057 (x : Var) :
    (nb074_alpha_dummy_063 x) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_063 x))
            (Class.cv (nb074_alpha_dummy_064 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_063 x))
            (Class.cv (nb074_alpha_dummy_064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0058 :
    (nb074_alpha_dummy_060) ∈
      (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0059 (x : Var) :
    (nb074_alpha_dummy_063 x) ∈
      (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0060 :
    (nb074_alpha_dummy_061) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_060))
            (Class.cv (nb074_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0061 (x : Var) :
    (nb074_alpha_dummy_064 x) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_063 x))
            (Class.cv (nb074_alpha_dummy_064 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_063 x))
            (Class.cv (nb074_alpha_dummy_064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0062 :
    (nb074_alpha_dummy_061) ∈
      (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0063 (x : Var) :
    (nb074_alpha_dummy_064 x) ∈
      (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0064 :
    (nb074_alpha_dummy_060) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0065 (x : Var) :
    (nb074_alpha_dummy_063 x) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_063 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0066 :
    (nb074_alpha_dummy_060) ∈
      (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_060))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0067 (x : Var) :
    (nb074_alpha_dummy_063 x) ∈
      (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_063 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0068 :
    (nb074_alpha_dummy_061) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0069 (x : Var) :
    (nb074_alpha_dummy_064 x) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_063 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0070 :
    (nb074_alpha_dummy_061) ∈
      (((Class.cv (nb074_alpha_dummy_061))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0071 (x : Var) :
    (nb074_alpha_dummy_064 x) ∈
      (((Class.cv (nb074_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0072 :
    (nb074_alpha_dummy_041) ∈
      (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0073 :
    (nb074_alpha_dummy_041) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_045)
              (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_045)
              (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_041) ≠ (nb074_alpha_dummy_045) from (by
          unfold nb074_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_041) ≠ (nb074_alpha_dummy_046) from (by
            unfold nb074_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0074 (x : Var) :
    (nb074_alpha_dummy_043 x) ∈
      (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C074C001Part004`. -/


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

theorem nb074_support_mem_0075 (x : Var) :
    (nb074_alpha_dummy_043 x) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x)
              (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_047 x)
              (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_043 x) ≠ (nb074_alpha_dummy_047 x) from (by
          unfold nb074_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_043 x) ≠ (nb074_alpha_dummy_048 x) from (by
            unfold nb074_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0076 :
    (nb074_alpha_dummy_041) ∈
      (((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045)
            (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_041) ≠ (nb074_alpha_dummy_045) from (by
          unfold nb074_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_041) ≠ (nb074_alpha_dummy_046) from (by
            unfold nb074_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0077 (x : Var) :
    (nb074_alpha_dummy_043 x) ∈
      (((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x)
            (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_043 x) ≠ (nb074_alpha_dummy_047 x) from (by
          unfold nb074_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_043 x) ≠ (nb074_alpha_dummy_048 x) from (by
            unfold nb074_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0078 :
    (nb074_alpha_dummy_046) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_046))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0079 (x : Var) :
    (nb074_alpha_dummy_048 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0080 :
    (nb074_alpha_dummy_046) ∈
      (((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0081 (x : Var) :
    (nb074_alpha_dummy_048 x) ∈
      (((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0082 :
    (nb074_alpha_dummy_081) ∈
      (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000))
            (Class.cv (nb074_alpha_dummy_081)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0083 (x : Var) :
    (nb074_alpha_dummy_083 x) ∈
      (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪ ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x)
            (Class.cv (nb074_alpha_dummy_083 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0084 :
    (nb074_alpha_dummy_082) ∈
      (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000))
            (Class.cv (nb074_alpha_dummy_081)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0085 (x : Var) :
    (nb074_alpha_dummy_084 x) ∈
      (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪ ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x)
            (Class.cv (nb074_alpha_dummy_083 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0086 :
    (nb074_alpha_dummy_081) ∈
      (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0087 :
    (nb074_alpha_dummy_081) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_087)
              (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_088)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_087)
              (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_087) from (by
          unfold nb074_alpha_dummy_087;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_088) from (by
            unfold nb074_alpha_dummy_088;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0088 (x : Var) :
    (nb074_alpha_dummy_083 x) ∈
      (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0089 (x : Var) :
    (nb074_alpha_dummy_083 x) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x)
              (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_089 x)
              (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_089 x) from (by
          unfold nb074_alpha_dummy_089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_090 x) from (by
            unfold nb074_alpha_dummy_090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0090 :
    (nb074_alpha_dummy_081) ∈
      (((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_087) from (by
          unfold nb074_alpha_dummy_087;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_088) from (by
            unfold nb074_alpha_dummy_088;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0091 (x : Var) :
    (nb074_alpha_dummy_083 x) ∈
      (((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_089 x) from (by
          unfold nb074_alpha_dummy_089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_090 x) from (by
            unfold nb074_alpha_dummy_090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0092 :
    (nb074_alpha_dummy_088) ∈ (((Class.cv (nb074_alpha_dummy_088))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0093 (x : Var) :
    (nb074_alpha_dummy_090 x) ∈ (((Class.cv (nb074_alpha_dummy_090 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0094 :
    (nb074_alpha_dummy_095) ∈
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_095)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_095)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_095))).fv) :=
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

theorem nb074_support_mem_0095 (x : Var) :
    (nb074_alpha_dummy_097 x) ∈
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_097 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_097 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_097 x))).fv) :=
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

theorem nb074_support_mem_0096 :
    (nb074_alpha_dummy_095) ∈
      (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0097 (x : Var) :
    (nb074_alpha_dummy_097 x) ∈
      (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0098 :
    (nb074_alpha_dummy_102) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_102))
            (Class.cv (nb074_alpha_dummy_103)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0099 (x : Var) :
    (nb074_alpha_dummy_105 x) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_105 x))
            (Class.cv (nb074_alpha_dummy_106 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_105 x))
            (Class.cv (nb074_alpha_dummy_106 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0100 :
    (nb074_alpha_dummy_102) ∈
      (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0101 (x : Var) :
    (nb074_alpha_dummy_105 x) ∈
      (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0102 :
    (nb074_alpha_dummy_103) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_102))
            (Class.cv (nb074_alpha_dummy_103)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0103 (x : Var) :
    (nb074_alpha_dummy_106 x) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_105 x))
            (Class.cv (nb074_alpha_dummy_106 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_105 x))
            (Class.cv (nb074_alpha_dummy_106 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0104 :
    (nb074_alpha_dummy_103) ∈
      (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0105 (x : Var) :
    (nb074_alpha_dummy_106 x) ∈
      (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0106 :
    (nb074_alpha_dummy_102) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_102)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_103)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0107 (x : Var) :
    (nb074_alpha_dummy_105 x) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_105 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_106 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0108 :
    (nb074_alpha_dummy_102) ∈
      (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_102))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0109 (x : Var) :
    (nb074_alpha_dummy_105 x) ∈
      (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_105 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0110 :
    (nb074_alpha_dummy_103) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_102)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_103)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0111 (x : Var) :
    (nb074_alpha_dummy_106 x) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_105 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_106 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0112 :
    (nb074_alpha_dummy_103) ∈
      (((Class.cv (nb074_alpha_dummy_103))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0113 (x : Var) :
    (nb074_alpha_dummy_106 x) ∈
      (((Class.cv (nb074_alpha_dummy_106 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0114 :
    (nb074_alpha_dummy_082) ∈
      (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0115 :
    (nb074_alpha_dummy_082) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_087)
              (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_088)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_087)
              (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_087) from (by
          unfold nb074_alpha_dummy_087;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_088) from (by
            unfold nb074_alpha_dummy_088;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0116 (x : Var) :
    (nb074_alpha_dummy_084 x) ∈
      (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0117 (x : Var) :
    (nb074_alpha_dummy_084 x) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x)
              (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_089 x)
              (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_089 x) from (by
          unfold nb074_alpha_dummy_089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_090 x) from (by
            unfold nb074_alpha_dummy_090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0118 :
    (nb074_alpha_dummy_082) ∈
      (((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_087) from (by
          unfold nb074_alpha_dummy_087;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_088) from (by
            unfold nb074_alpha_dummy_088;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0119 (x : Var) :
    (nb074_alpha_dummy_084 x) ∈
      (((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_089 x) from (by
          unfold nb074_alpha_dummy_089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_090 x) from (by
            unfold nb074_alpha_dummy_090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0120 :
    (nb074_alpha_dummy_088) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_088))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0121 (x : Var) :
    (nb074_alpha_dummy_090 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0122 :
    (nb074_alpha_dummy_088) ∈
      (((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0123 (x : Var) :
    (nb074_alpha_dummy_090 x) ∈
      (((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0124 :
    (nb074_alpha_dummy_082) ∈
      (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0125 :
    (nb074_alpha_dummy_082) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_123)
              (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_124)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_123)
              (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_123) from (by
          unfold nb074_alpha_dummy_123;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_124) from (by
            unfold nb074_alpha_dummy_124;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0126 (x : Var) :
    (nb074_alpha_dummy_084 x) ∈
      (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0127 (x : Var) :
    (nb074_alpha_dummy_084 x) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x)
              (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_125 x)
              (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_125 x) from (by
          unfold nb074_alpha_dummy_125;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_126 x) from (by
            unfold nb074_alpha_dummy_126;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0128 :
    (nb074_alpha_dummy_082) ∈
      (((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_123) from (by
          unfold nb074_alpha_dummy_123;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_124) from (by
            unfold nb074_alpha_dummy_124;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0129 (x : Var) :
    (nb074_alpha_dummy_084 x) ∈
      (((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv ∪
        ((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_125 x) from (by
          unfold nb074_alpha_dummy_125;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_126 x) from (by
            unfold nb074_alpha_dummy_126;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0130 :
    (nb074_alpha_dummy_124) ∈ (((Class.cv (nb074_alpha_dummy_124))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0131 (x : Var) :
    (nb074_alpha_dummy_126 x) ∈ (((Class.cv (nb074_alpha_dummy_126 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0132 :
    (nb074_alpha_dummy_131) ∈
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_131)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_131)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_131))).fv) :=
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

theorem nb074_support_mem_0133 (x : Var) :
    (nb074_alpha_dummy_133 x) ∈
      (((Wff.classMem (Class.cv (nb074_alpha_dummy_133 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb074_alpha_dummy_133 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb074_alpha_dummy_133 x))).fv) :=
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

theorem nb074_support_mem_0134 :
    (nb074_alpha_dummy_131) ∈
      (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0135 (x : Var) :
    (nb074_alpha_dummy_133 x) ∈
      (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0136 :
    (nb074_alpha_dummy_138) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_138))
            (Class.cv (nb074_alpha_dummy_139)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0137 (x : Var) :
    (nb074_alpha_dummy_141 x) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_141 x))
            (Class.cv (nb074_alpha_dummy_142 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_141 x))
            (Class.cv (nb074_alpha_dummy_142 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0138 :
    (nb074_alpha_dummy_138) ∈
      (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0139 (x : Var) :
    (nb074_alpha_dummy_141 x) ∈
      (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0140 :
    (nb074_alpha_dummy_139) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_138))
            (Class.cv (nb074_alpha_dummy_139)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0141 (x : Var) :
    (nb074_alpha_dummy_142 x) ∈
      (((syn_cnin (Class.cv (nb074_alpha_dummy_141 x))
            (Class.cv (nb074_alpha_dummy_142 x)))).fv ∪
        ((syn_cnin (Class.cv (nb074_alpha_dummy_141 x))
            (Class.cv (nb074_alpha_dummy_142 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0142 :
    (nb074_alpha_dummy_139) ∈
      (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0143 (x : Var) :
    (nb074_alpha_dummy_142 x) ∈
      (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0144 :
    (nb074_alpha_dummy_138) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_138)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_139)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0145 (x : Var) :
    (nb074_alpha_dummy_141 x) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_141 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_142 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0146 :
    (nb074_alpha_dummy_138) ∈
      (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_138))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0147 (x : Var) :
    (nb074_alpha_dummy_141 x) ∈
      (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_141 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0148 :
    (nb074_alpha_dummy_139) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_138)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_139)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0149 (x : Var) :
    (nb074_alpha_dummy_142 x) ∈
      (((syn_ccompl (Class.cv (nb074_alpha_dummy_141 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb074_alpha_dummy_142 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0150 :
    (nb074_alpha_dummy_139) ∈
      (((Class.cv (nb074_alpha_dummy_139))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0151 (x : Var) :
    (nb074_alpha_dummy_142 x) ∈
      (((Class.cv (nb074_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0152 :
    (nb074_alpha_dummy_081) ∈
      (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0153 :
    (nb074_alpha_dummy_081) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_123)
              (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_124)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_123)
              (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_123) from (by
          unfold nb074_alpha_dummy_123;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_124) from (by
            unfold nb074_alpha_dummy_124;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0154 (x : Var) :
    (nb074_alpha_dummy_083 x) ∈
      (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0155 (x : Var) :
    (nb074_alpha_dummy_083 x) ∈
      (((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x)
              (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb074_alpha_dummy_125 x)
              (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_125 x) from (by
          unfold nb074_alpha_dummy_125;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_126 x) from (by
            unfold nb074_alpha_dummy_126;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0156 :
    (nb074_alpha_dummy_081) ∈
      (((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_123) from (by
          unfold nb074_alpha_dummy_123;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_124) from (by
            unfold nb074_alpha_dummy_124;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0157 (x : Var) :
    (nb074_alpha_dummy_083 x) ∈
      (((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_125 x) from (by
          unfold nb074_alpha_dummy_125;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_126 x) from (by
            unfold nb074_alpha_dummy_126;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0158 :
    (nb074_alpha_dummy_124) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_124))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0159 (x : Var) :
    (nb074_alpha_dummy_126 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0160 :
    (nb074_alpha_dummy_124) ∈
      (((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0161 (x : Var) :
    (nb074_alpha_dummy_126 x) ∈
      (((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv ∪
        ((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0162 :
    (nb074_alpha_dummy_000) ∈
      (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0163 (x : Var) :
    x ∈ (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0164 :
    (nb074_alpha_dummy_000) ∈
      (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000))
            (Class.cv (nb074_alpha_dummy_081)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0165 (x : Var) :
    x ∈
      (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪ ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x)
            (Class.cv (nb074_alpha_dummy_083 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0166 :
    (nb074_alpha_dummy_000) ∈ (((Class.cv (nb074_alpha_dummy_000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0167 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
