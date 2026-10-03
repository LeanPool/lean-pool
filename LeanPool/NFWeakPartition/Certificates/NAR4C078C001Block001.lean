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

/-! Certificates from `NAR4C078C001Part001`. -/


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
noncomputable def nb078_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb078_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb078_alpha_dummy_002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

@[expose]
noncomputable def nb078_alpha_dummy_003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

@[expose]
noncomputable def nb078_alpha_dummy_004 : Var :=
  (freshVar ((∅ : Finset Var)) 4)

@[expose]
noncomputable def nb078_alpha_dummy_005 : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
          (syn_ccom (Class.cv (nb078_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_006 (f : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_007 : Var :=
  (freshVar (((syn_ccom (Class.cv (nb078_alpha_dummy_000))
          (syn_ccnv (Class.cv (nb078_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_008 (f : Var) : Var :=
  (freshVar (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_009 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_010 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_011 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_012 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_013 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_014 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_015 : Var :=
  (freshVar
    (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪
      ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_000))) (Class.cv (nb078_alpha_dummy_011)))
            (syn_wbr (Class.cv (nb078_alpha_dummy_011)) (Class.cv (nb078_alpha_dummy_000))
              (Class.cv (nb078_alpha_dummy_010)))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_016 (f : Var) : Var :=
  (freshVar (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪
        ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa
            (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f))
              (Class.cv (nb078_alpha_dummy_014 f)))
            (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f)
              (Class.cv (nb078_alpha_dummy_013 f)))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_017 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_018 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_019 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_013 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_020 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_013 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_021 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cphi (Class.cv (nb078_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_022 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_023 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_017)
          (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
              (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_017)
          (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
              (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_024 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_019 f)
          (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_019 f)
          (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_025 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_018))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_026 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_018))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_027 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_020 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_028 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_020 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_029 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_025)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_025)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_025))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_030 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_027 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_027 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_027 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_031 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_032 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_033 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_034 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_035 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_036 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_037 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_032))
          (Class.cv (nb078_alpha_dummy_033)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_038 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_035 f))
          (Class.cv (nb078_alpha_dummy_036 f)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_035 f)) (Class.cv (nb078_alpha_dummy_036 f)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_039 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_040 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_036 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_041 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_032)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_033)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_042 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_035 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_036 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_043 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_032))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_044 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_035 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_045 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_033))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_046 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_036 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_036 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_047 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_017)
          (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_017)
          (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_048 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_019 f)
          (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_019 f)
          (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_049 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_018))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_050 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_051 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_052 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_053 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_054 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_055 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_014 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_056 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_014 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_057 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_058 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_059 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_053)
          (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
              (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_053)
          (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
              (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_060 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_055 f)
          (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_055 f)
          (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_061 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_054))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_062 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_054))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_063 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_056 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_064 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_056 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_065 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_061)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_061)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_061))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_066 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_063 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_063 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_063 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_067 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_068 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_069 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_070 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_071 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_072 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_073 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_068))
          (Class.cv (nb078_alpha_dummy_069)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_074 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_071 f))
          (Class.cv (nb078_alpha_dummy_072 f)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_071 f)) (Class.cv (nb078_alpha_dummy_072 f)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_075 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_076 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_072 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_077 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_068)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_069)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_078 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_071 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_072 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_079 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_068))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_080 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_071 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_081 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_069))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_082 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_072 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_072 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_083 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_053)
          (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_053)
          (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_084 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_055 f)
          (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_055 f)
          (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_085 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_054))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_086 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_087 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_088 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_089 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_090 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_091 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_092 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_093 : Var :=
  (freshVar
    (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000))
          (Class.cv (nb078_alpha_dummy_089)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_094 (f : Var) : Var :=
  (freshVar (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪
        ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f)
          (Class.cv (nb078_alpha_dummy_091 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_095 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_096 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_097 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_092 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_098 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_092 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_099 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_100 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_101 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_095)
          (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
              (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_095)
          (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
              (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_102 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_097 f)
          (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_097 f)
          (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_103 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_096))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_104 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_096))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_105 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_098 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_106 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_098 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_107 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_103)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_103)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_103))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_108 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_105 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_105 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_105 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_109 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_110 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_111 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_112 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_113 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_114 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_115 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_110))
          (Class.cv (nb078_alpha_dummy_111)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_116 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_113 f))
          (Class.cv (nb078_alpha_dummy_114 f)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_113 f)) (Class.cv (nb078_alpha_dummy_114 f)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_117 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_118 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_114 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_119 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_110)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_111)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_120 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_113 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_114 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_121 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_110))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_122 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_113 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_123 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_111))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_124 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_114 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_114 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_125 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_095)
          (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_095)
          (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_126 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_097 f)
          (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_097 f)
          (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_127 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_096))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_128 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_129 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_130 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_131 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_132 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_133 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_091 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_134 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_091 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_135 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_136 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_137 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_131)
          (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
              (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_131)
          (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
              (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_138 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_133 f)
          (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_133 f)
          (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_139 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_132))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_140 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_132))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_141 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_134 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_142 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_134 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_143 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_139)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_139)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_139))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_144 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_141 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_141 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_141 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_145 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_146 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_147 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_148 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_149 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part002`. -/


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
noncomputable def nb078_alpha_dummy_150 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_151 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_146))
          (Class.cv (nb078_alpha_dummy_147)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_152 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_149 f))
          (Class.cv (nb078_alpha_dummy_150 f)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_149 f)) (Class.cv (nb078_alpha_dummy_150 f)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_153 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_154 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_150 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_155 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_146)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_147)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_156 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_149 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_150 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_157 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_146))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_158 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_149 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_159 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_147))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_160 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_150 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_150 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_161 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_131)
          (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_131)
          (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_162 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_133 f)
          (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_133 f)
          (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_163 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_132))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_164 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_165 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_166 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_167 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_168 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_169 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_013 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_170 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_013 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_171 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_172 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_173 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_167)
          (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
              (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_167)
          (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
              (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_174 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_169 f)
          (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_169 f)
          (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_175 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_168))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_176 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_168))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_177 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_170 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_178 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_170 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_179 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_175)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_175)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_175))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_180 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_177 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_177 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_177 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_181 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_182 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_183 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_184 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_185 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_186 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_187 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_182))
          (Class.cv (nb078_alpha_dummy_183)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_188 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_185 f))
          (Class.cv (nb078_alpha_dummy_186 f)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_185 f)) (Class.cv (nb078_alpha_dummy_186 f)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_189 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_190 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_186 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_191 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_182)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_183)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_192 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_185 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_186 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_193 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_182))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_194 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_185 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_195 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_183))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_196 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_186 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_186 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_197 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_167)
          (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_167)
          (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_198 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_169 f)
          (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_169 f)
          (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_199 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_168))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_200 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_201 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_202 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_203 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_204 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_205 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_206 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_207 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_208 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_209 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_205 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_210 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_205 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_211 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_208)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_212 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_213 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_207)
          (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
              (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_207)
          (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
              (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_214 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_209 f)
          (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_209 f)
          (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_215 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_208))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_216 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_208))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_217 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_210 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_218 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_210 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_219 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_215)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_215)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_215))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_220 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_217 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_217 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_217 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_221 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_222 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_223 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_224 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_225 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_226 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_227 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_222))
          (Class.cv (nb078_alpha_dummy_223)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_228 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_225 f))
          (Class.cv (nb078_alpha_dummy_226 f)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_225 f)) (Class.cv (nb078_alpha_dummy_226 f)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_229 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_230 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_226 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_231 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_222)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_223)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_232 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_225 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_226 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_233 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_222))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_234 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_225 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_235 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_223))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_236 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_226 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_226 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_237 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_207)
          (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_207)
          (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_238 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_209 f)
          (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_209 f)
          (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_239 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_208))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_240 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_241 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_242 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_243 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_244 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_245 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_246 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_247 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_248 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_249 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_245 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_250 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_245 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_251 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cphi (Class.cv (nb078_alpha_dummy_248)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_252 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_253 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_247)
          (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
              (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_247)
          (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
              (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_254 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_249 f)
          (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_249 f)
          (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
              (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_255 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_248))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_256 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_248))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_257 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_250 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_258 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_250 f))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_259 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_255)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_255)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_255))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_260 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_257 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_257 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_257 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_261 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_262 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_263 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_264 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_265 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_266 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_267 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_262))
          (Class.cv (nb078_alpha_dummy_263)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_268 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_265 f))
          (Class.cv (nb078_alpha_dummy_266 f)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_265 f)) (Class.cv (nb078_alpha_dummy_266 f)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_269 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_270 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_266 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_271 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_262)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_263)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_272 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_265 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_266 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_273 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_262))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_274 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_265 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_275 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_263))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_276 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_266 f))).fv ∪
      ((Class.cv (nb078_alpha_dummy_266 f))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_277 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_247)
          (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_247)
          (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_278 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_249 f)
          (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_249 f)
          (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_279 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_248))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_280 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_281 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_282 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_283 : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin
          (syn_ccom (Class.cv (nb078_alpha_dummy_001))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_284 (g : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_285 : Var :=
  (freshVar (((syn_ccom (Class.cv (nb078_alpha_dummy_001))
          (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_286 (g : Var) : Var :=
  (freshVar (((syn_ccom (Class.cv g) (syn_ccnv (Class.cv g)))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_287 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv ∪
      ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_288 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv ∪
      ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_289 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv ∪
      ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_290 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_291 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_292 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_293 : Var :=
  (freshVar
    (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪
      ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_289)))
            (syn_wbr (Class.cv (nb078_alpha_dummy_289)) (Class.cv (nb078_alpha_dummy_001))
              (Class.cv (nb078_alpha_dummy_288)))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_294 (g : Var) : Var :=
  (freshVar (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪
        ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa
            (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g))
              (Class.cv (nb078_alpha_dummy_292 g)))
            (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g)
              (Class.cv (nb078_alpha_dummy_291 g)))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_295 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_296 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_297 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_291 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_298 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_291 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_299 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cphi (Class.cv (nb078_alpha_dummy_296)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part003`. -/


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
noncomputable def nb078_alpha_dummy_300 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_301 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_295)
          (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
              (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_295)
          (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
              (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_302 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_297 g)
          (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_297 g)
          (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_303 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_296))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_304 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_296))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_305 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_298 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_306 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_298 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_307 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_303)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_303)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_303))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_308 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_305 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_305 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_305 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_309 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_310 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_311 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_312 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_313 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_314 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_315 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_310))
          (Class.cv (nb078_alpha_dummy_311)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_316 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_313 g))
          (Class.cv (nb078_alpha_dummy_314 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_313 g)) (Class.cv (nb078_alpha_dummy_314 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_317 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_318 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_314 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_319 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_310)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_311)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_320 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_313 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_314 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_321 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_310))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_322 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_313 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_323 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_311))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_324 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_314 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_314 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_325 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_295)
          (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_295)
          (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_326 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_297 g)
          (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_297 g)
          (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_327 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_296))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_328 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_329 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_330 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_331 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_332 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_333 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_292 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_334 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_292 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_335 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cphi (Class.cv (nb078_alpha_dummy_332)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_336 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_337 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_331)
          (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
              (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_331)
          (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
              (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_338 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_333 g)
          (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_333 g)
          (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_339 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_332))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_340 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_332))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_341 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_334 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_342 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_334 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_343 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_339)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_339)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_339))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_344 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_341 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_341 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_341 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_345 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_346 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_347 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_348 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_349 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_350 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_351 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_346))
          (Class.cv (nb078_alpha_dummy_347)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_352 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_349 g))
          (Class.cv (nb078_alpha_dummy_350 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_349 g)) (Class.cv (nb078_alpha_dummy_350 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_353 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_354 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_350 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_355 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_346)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_347)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_356 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_349 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_350 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_357 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_346))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_358 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_349 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_359 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_347))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_360 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_350 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_350 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_361 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_331)
          (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_331)
          (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_362 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_333 g)
          (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_333 g)
          (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_363 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_332))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_364 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_365 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_366 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_367 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_368 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_369 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_370 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_371 : Var :=
  (freshVar
    (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001))
          (Class.cv (nb078_alpha_dummy_367)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_372 (g : Var) : Var :=
  (freshVar (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪
        ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g)
          (Class.cv (nb078_alpha_dummy_369 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_373 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_374 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_375 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_370 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_376 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_370 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_377 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cphi (Class.cv (nb078_alpha_dummy_374)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_378 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_379 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_373)
          (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
              (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_373)
          (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
              (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_380 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_375 g)
          (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_375 g)
          (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_381 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_374))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_382 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_374))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_383 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_376 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_384 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_376 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_385 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_381)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_381)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_381))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_386 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_383 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_383 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_383 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_387 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_388 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_389 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_390 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_391 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_392 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_393 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_388))
          (Class.cv (nb078_alpha_dummy_389)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_394 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_391 g))
          (Class.cv (nb078_alpha_dummy_392 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_391 g)) (Class.cv (nb078_alpha_dummy_392 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_395 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_396 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_392 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_397 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_388)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_389)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_398 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_391 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_392 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_399 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_388))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_400 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_391 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_401 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_389))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_402 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_392 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_392 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_403 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_373)
          (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_373)
          (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_404 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_375 g)
          (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_375 g)
          (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_405 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_374))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_406 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_407 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_408 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_409 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_410 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_411 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_369 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_412 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_369 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_413 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cphi (Class.cv (nb078_alpha_dummy_410)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_414 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_415 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_409)
          (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
              (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_409)
          (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
              (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_416 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_411 g)
          (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_411 g)
          (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_417 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_410))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_418 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_410))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_419 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_412 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_420 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_412 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_421 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_417)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_417)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_417))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_422 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_419 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_419 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_419 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_423 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_424 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_425 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_426 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_427 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_428 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_429 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_424))
          (Class.cv (nb078_alpha_dummy_425)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_430 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_427 g))
          (Class.cv (nb078_alpha_dummy_428 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_427 g)) (Class.cv (nb078_alpha_dummy_428 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_431 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_432 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_428 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_433 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_424)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_425)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_434 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_427 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_428 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_435 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_424))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_436 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_427 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_437 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_425))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_438 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_428 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_428 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_439 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_409)
          (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_409)
          (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_440 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_411 g)
          (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_411 g)
          (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_441 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_410))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_442 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_443 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_444 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_445 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_446 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_447 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_291 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_448 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_291 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_449 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cphi (Class.cv (nb078_alpha_dummy_446)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part004`. -/


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
noncomputable def nb078_alpha_dummy_450 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_451 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_445)
          (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
              (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_445)
          (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
              (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_452 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_447 g)
          (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_447 g)
          (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_453 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_446))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_454 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_446))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_455 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_448 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_456 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_448 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_457 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_453)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_453)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_453))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_458 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_455 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_455 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_455 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_459 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_460 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_461 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_462 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_463 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_464 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_465 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_460))
          (Class.cv (nb078_alpha_dummy_461)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_466 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_463 g))
          (Class.cv (nb078_alpha_dummy_464 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_463 g)) (Class.cv (nb078_alpha_dummy_464 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_467 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_468 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_464 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_469 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_460)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_461)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_470 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_463 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_464 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_471 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_460))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_472 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_463 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_473 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_461))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_474 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_464 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_464 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_475 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_445)
          (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_445)
          (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_476 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_447 g)
          (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_447 g)
          (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_477 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_446))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_478 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_479 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_480 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_481 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_482 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_483 (g : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_484 (g : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_485 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_486 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_487 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_483 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_488 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_483 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_489 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cphi (Class.cv (nb078_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_490 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_491 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_485)
          (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
              (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_485)
          (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
              (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_492 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_487 g)
          (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_487 g)
          (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_493 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_486))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_494 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_486))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_495 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_488 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_496 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_488 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_497 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_493)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_493)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_493))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_498 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_495 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_495 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_495 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_499 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_500 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_501 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_502 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_503 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_504 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_505 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_500))
          (Class.cv (nb078_alpha_dummy_501)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_506 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_503 g))
          (Class.cv (nb078_alpha_dummy_504 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_503 g)) (Class.cv (nb078_alpha_dummy_504 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_507 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_508 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_504 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_509 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_500)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_501)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_510 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_503 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_504 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_511 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_500))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_512 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_503 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_513 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_501))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_514 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_504 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_504 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_515 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_485)
          (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_485)
          (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_516 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_487 g)
          (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_487 g)
          (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_517 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_486))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_518 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_519 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_520 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_521 : Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001)))
          (Class.cv (nb078_alpha_dummy_003)))).fv ∪
      ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001)))
          (Class.cv (nb078_alpha_dummy_003)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_522 (x : Var) (g : Var) : Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv ∪
      ((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_523 : Var :=
  (freshVar (((syn_crn (Class.cv (nb078_alpha_dummy_001)))).fv ∪
      ((Class.cv (nb078_alpha_dummy_003))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_524 (x : Var) (g : Var) : Var :=
  (freshVar (((syn_crn (Class.cv g))).fv ∪ ((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_525 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_526 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_527 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_528 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_529 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_530 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_531 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_527 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_532 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_527 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_533 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cphi (Class.cv (nb078_alpha_dummy_530)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_534 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_535 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_529)
          (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
              (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_529)
          (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
              (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_536 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_531 g)
          (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_531 g)
          (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_537 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_530))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_538 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_530))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_539 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_532 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_540 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_532 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_541 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_537)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_537)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_537))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_542 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_539 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_539 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_539 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_543 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_544 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_545 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_546 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_547 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_548 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_549 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_544))
          (Class.cv (nb078_alpha_dummy_545)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_550 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_547 g))
          (Class.cv (nb078_alpha_dummy_548 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_547 g)) (Class.cv (nb078_alpha_dummy_548 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_551 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_552 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_548 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_553 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_544)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_545)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_554 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_547 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_548 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_555 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_544))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_556 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_547 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_557 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_545))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_558 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_548 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_548 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_559 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_529)
          (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_529)
          (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_560 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_531 g)
          (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_531 g)
          (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_561 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_530))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_562 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_563 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_564 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_565 : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
            (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
            (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_566 (g : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))
          (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))
          (syn_cid))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_567 : Var :=
  (freshVar (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
          (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_568 (g : Var) : Var :=
  (freshVar (((syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))).fv ∪
      ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_569 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_570 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_571 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_572 (g : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_573 (g : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_574 (g : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_575 : Var :=
  (freshVar
    (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪
      ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))
              (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
              (Class.cv (nb078_alpha_dummy_570)))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_576 (g : Var) : Var :=
  (freshVar (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪
        ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa
            (syn_wbr (Class.cv (nb078_alpha_dummy_572 g))
              (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g)))
            (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g))
              (Class.cv (nb078_alpha_dummy_573 g)))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_577 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_578 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_579 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_573 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_580 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_573 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_581 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cphi (Class.cv (nb078_alpha_dummy_578)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_582 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_583 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_577)
          (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
              (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_577)
          (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
              (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_584 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_579 g)
          (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_579 g)
          (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_585 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_578))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_586 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_578))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_587 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_580 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_588 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_580 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_589 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_585)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_585)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_585))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_590 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_587 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_587 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_587 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_591 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_592 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_593 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_594 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_595 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_596 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_597 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_592))
          (Class.cv (nb078_alpha_dummy_593)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_598 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_595 g))
          (Class.cv (nb078_alpha_dummy_596 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_595 g)) (Class.cv (nb078_alpha_dummy_596 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_599 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part005`. -/


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
noncomputable def nb078_alpha_dummy_600 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_596 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_601 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_592)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_593)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_602 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_595 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_596 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_603 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_592))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_604 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_595 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_605 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_593))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_606 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_596 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_596 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_607 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_577)
          (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_577)
          (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_608 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_579 g)
          (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_579 g)
          (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_609 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_578))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_610 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_611 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_612 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_613 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_614 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_615 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_574 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_616 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_574 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_617 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cphi (Class.cv (nb078_alpha_dummy_614)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_618 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_619 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_613)
          (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
              (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_613)
          (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
              (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_620 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_615 g)
          (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_615 g)
          (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_621 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_614))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_622 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_614))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_623 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_616 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_624 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_616 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_625 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_621)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_621)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_621))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_626 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_623 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_623 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_623 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_627 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_628 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_629 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_630 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_631 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_632 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_633 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_628))
          (Class.cv (nb078_alpha_dummy_629)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_634 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_631 g))
          (Class.cv (nb078_alpha_dummy_632 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_631 g)) (Class.cv (nb078_alpha_dummy_632 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_635 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_636 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_632 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_637 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_628)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_629)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_638 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_631 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_632 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_639 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_628))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_640 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_631 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_641 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_629))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_642 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_632 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_632 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_643 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_613)
          (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_613)
          (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_644 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_615 g)
          (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_615 g)
          (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_645 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_614))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_646 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_647 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_648 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_649 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_650 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_651 (g : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_652 (g : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_653 : Var :=
  (freshVar
    (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb078_alpha_dummy_650)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
          (Class.cv (nb078_alpha_dummy_649)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_654 (g : Var) : Var :=
  (freshVar (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪
        ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g))
          (Class.cv (nb078_alpha_dummy_651 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_655 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_656 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_657 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_652 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_658 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_652 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_659 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cphi (Class.cv (nb078_alpha_dummy_656)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_660 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_661 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_655)
          (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
              (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_655)
          (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
              (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_662 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_657 g)
          (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_657 g)
          (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_663 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_656))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_664 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_656))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_665 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_658 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_666 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_658 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_667 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_663)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_663)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_663))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_668 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_665 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_665 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_665 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_669 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_670 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_671 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_672 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_673 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_674 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_675 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_670))
          (Class.cv (nb078_alpha_dummy_671)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_676 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_673 g))
          (Class.cv (nb078_alpha_dummy_674 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_673 g)) (Class.cv (nb078_alpha_dummy_674 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_677 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_678 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_674 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_679 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_670)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_671)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_680 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_673 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_674 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_681 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_670))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_682 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_673 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_683 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_671))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_684 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_674 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_674 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_685 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_655)
          (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_655)
          (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_686 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_657 g)
          (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_657 g)
          (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_687 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_656))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_688 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_689 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_690 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_691 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_692 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_693 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_651 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_694 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_651 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_695 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cphi (Class.cv (nb078_alpha_dummy_692)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_696 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_697 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_691)
          (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
              (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_691)
          (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
              (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_698 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_693 g)
          (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_693 g)
          (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_699 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_692))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_700 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_692))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_701 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_694 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_702 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_694 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_703 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_699)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_699)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_699))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_704 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_701 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_701 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_701 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_705 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_706 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_707 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_708 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_709 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_710 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_711 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_706))
          (Class.cv (nb078_alpha_dummy_707)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_712 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_709 g))
          (Class.cv (nb078_alpha_dummy_710 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_709 g)) (Class.cv (nb078_alpha_dummy_710 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_713 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_714 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_710 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_715 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_706)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_707)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_716 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_709 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_710 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_717 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_706))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_718 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_709 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_719 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_707))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_720 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_710 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_710 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_721 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_691)
          (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_691)
          (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_722 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_693 g)
          (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_693 g)
          (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_723 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_692))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_724 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_725 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_726 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_727 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_728 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_729 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_573 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_730 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_573 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_731 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cphi (Class.cv (nb078_alpha_dummy_728)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_732 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_733 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_727)
          (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
              (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_727)
          (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
              (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_734 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_729 g)
          (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_729 g)
          (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
              (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_735 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_728))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_736 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_728))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_737 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_730 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_738 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_730 g))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_739 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_735)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_735)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_735))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_740 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_737 g)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_737 g)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_737 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_741 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_742 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_743 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_744 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_745 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_746 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_747 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_742))
          (Class.cv (nb078_alpha_dummy_743)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_748 (g : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_745 g))
          (Class.cv (nb078_alpha_dummy_746 g)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_745 g)) (Class.cv (nb078_alpha_dummy_746 g)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_749 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part006`. -/


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
noncomputable def nb078_alpha_dummy_750 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_746 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_751 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_742)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_743)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_752 (g : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_745 g)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_746 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_753 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_742))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_754 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_745 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_755 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_743))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_756 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_746 g))).fv ∪
      ((Class.cv (nb078_alpha_dummy_746 g))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_757 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_727)
          (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_727)
          (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_758 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_729 g)
          (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_729 g)
          (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_759 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_728))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_760 (g : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_761 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_762 (g : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_763 : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv ∪ ((syn_cnin
          (syn_ccom (Class.cv (nb078_alpha_dummy_002))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_764 (h : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_765 : Var :=
  (freshVar (((syn_ccom (Class.cv (nb078_alpha_dummy_002))
          (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_766 (h : Var) : Var :=
  (freshVar (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_767 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv ∪
      ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_768 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv ∪
      ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_769 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv ∪
      ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_770 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_771 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_772 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_773 : Var :=
  (freshVar
    (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪
      ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_769)))
            (syn_wbr (Class.cv (nb078_alpha_dummy_769)) (Class.cv (nb078_alpha_dummy_002))
              (Class.cv (nb078_alpha_dummy_768)))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_774 (h : Var) : Var :=
  (freshVar (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪
        ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa
            (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h))
              (Class.cv (nb078_alpha_dummy_772 h)))
            (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h)
              (Class.cv (nb078_alpha_dummy_771 h)))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_775 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_776 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_777 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_771 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_778 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_771 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_779 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cphi (Class.cv (nb078_alpha_dummy_776)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_780 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_781 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_775)
          (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
              (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_775)
          (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
              (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_782 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_777 h)
          (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_777 h)
          (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_783 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_776))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_784 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_776))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_785 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_778 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_786 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_778 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_787 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_783)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_783)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_783))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_788 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_785 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_785 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_785 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_789 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_790 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_791 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_792 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_793 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_794 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_795 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_790))
          (Class.cv (nb078_alpha_dummy_791)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_796 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_793 h))
          (Class.cv (nb078_alpha_dummy_794 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_793 h)) (Class.cv (nb078_alpha_dummy_794 h)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_797 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_798 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_794 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_799 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_790)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_791)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_800 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_793 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_794 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_801 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_790))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_802 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_793 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_803 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_791))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_804 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_794 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_794 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_805 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_775)
          (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_775)
          (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_806 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_777 h)
          (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_777 h)
          (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_807 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_776))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_808 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_809 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_810 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_811 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_812 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_813 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_772 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_814 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_772 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_815 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cphi (Class.cv (nb078_alpha_dummy_812)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_816 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_817 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_811)
          (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
              (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_811)
          (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
              (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_818 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_813 h)
          (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_813 h)
          (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_819 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_812))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_820 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_812))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_821 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_814 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_822 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_814 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_823 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_819)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_819)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_819))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_824 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_821 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_821 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_821 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_825 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_826 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_827 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_828 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_829 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_830 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_831 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_826))
          (Class.cv (nb078_alpha_dummy_827)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_832 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_829 h))
          (Class.cv (nb078_alpha_dummy_830 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_829 h)) (Class.cv (nb078_alpha_dummy_830 h)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_833 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_834 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_830 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_835 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_826)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_827)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_836 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_829 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_830 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_837 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_826))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_838 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_829 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_839 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_827))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_840 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_830 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_830 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_841 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_811)
          (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811)
          (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_842 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_813 h)
          (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h)
          (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_843 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_812))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_844 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_845 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_846 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_847 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_848 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_849 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_850 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_851 : Var :=
  (freshVar
    (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002))
          (Class.cv (nb078_alpha_dummy_847)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_852 (h : Var) : Var :=
  (freshVar (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪
        ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h)
          (Class.cv (nb078_alpha_dummy_849 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_853 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_854 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_855 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_850 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_856 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_850 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_857 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cphi (Class.cv (nb078_alpha_dummy_854)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_858 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_859 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_853)
          (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
              (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_853)
          (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
              (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_860 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_855 h)
          (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_855 h)
          (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_861 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_854))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_862 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_854))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_863 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_856 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_864 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_856 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_865 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_861)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_861)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_861))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_866 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_863 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_863 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_863 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_867 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_868 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_869 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_870 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_871 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_872 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_873 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_868))
          (Class.cv (nb078_alpha_dummy_869)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_874 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_871 h))
          (Class.cv (nb078_alpha_dummy_872 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_871 h)) (Class.cv (nb078_alpha_dummy_872 h)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_875 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_876 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_872 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_877 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_868)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_869)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_878 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_871 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_872 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_879 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_868))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_880 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_871 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_881 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_869))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_882 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_872 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_872 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_883 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_853)
          (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853)
          (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_884 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_855 h)
          (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h)
          (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_885 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_854))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_886 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_887 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_888 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_889 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_890 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_891 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_849 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_892 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_849 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_893 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cphi (Class.cv (nb078_alpha_dummy_890)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_894 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_895 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_889)
          (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
              (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_889)
          (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
              (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_896 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_891 h)
          (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_891 h)
          (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_897 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_890))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_898 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_890))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_899 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_892 h))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
