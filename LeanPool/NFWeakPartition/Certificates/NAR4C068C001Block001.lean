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

/-! Certificates from `NAR4C068C001Part001`. -/


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
noncomputable def nb068_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb068_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb068_alpha_dummy_002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

@[expose]
noncomputable def nb068_alpha_dummy_003 : Var :=
  (freshVar
    (({(nb068_alpha_dummy_001)} : Finset Var) ∪ ({(nb068_alpha_dummy_002)} : Finset Var) ∪
      ((syn_wex (nb068_alpha_dummy_000)
          (syn_wf1o (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_001))
            (Class.cv (nb068_alpha_dummy_002))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_004 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ((syn_wex f (syn_wf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_005 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_006 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_007 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_008 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_009 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cphi (Class.cv (nb068_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_010 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_011 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_005)
          (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
              (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_005)
          (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
              (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_012 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_007 x y)
          (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
              (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
              (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_013 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_006))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_014 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_006))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_015 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_008 x y))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_008 x y))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_013)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_013)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_013))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_018 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_015 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_015 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_015 x y))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_019 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_020 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_021 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_022 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_023 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_025 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_020))
          (Class.cv (nb068_alpha_dummy_021)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_026 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y))
          (Class.cv (nb068_alpha_dummy_024 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y))
          (Class.cv (nb068_alpha_dummy_024 x y)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_027 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_028 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪
      ((Class.cv (nb068_alpha_dummy_024 x y))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_029 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_020)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_030 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_023 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_024 x y)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_031 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_020))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪
      ((Class.cv (nb068_alpha_dummy_023 x y))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_033 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_021))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_034 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_024 x y))).fv ∪
      ((Class.cv (nb068_alpha_dummy_024 x y))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_035 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_005)
          (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_005)
          (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_036 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_007 x y)
          (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_007 x y)
          (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_037 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_006))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_038 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_039 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_040 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_041 : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv (nb068_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
          (syn_ccom (Class.cv (nb068_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_042 (f : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_043 : Var :=
  (freshVar (((syn_ccom (Class.cv (nb068_alpha_dummy_000))
          (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_044 (f : Var) : Var :=
  (freshVar (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_045 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_046 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_047 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_048 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_049 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_050 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_051 : Var :=
  (freshVar
    (({(nb068_alpha_dummy_045)} : Finset Var) ∪ ({(nb068_alpha_dummy_046)} : Finset Var) ∪
      ((syn_wex (nb068_alpha_dummy_047) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_045))
              (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_047)))
            (syn_wbr (Class.cv (nb068_alpha_dummy_047)) (Class.cv (nb068_alpha_dummy_000))
              (Class.cv (nb068_alpha_dummy_046)))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_052 (f : Var) : Var :=
  (freshVar (({(nb068_alpha_dummy_048 f)} : Finset Var) ∪
        ({(nb068_alpha_dummy_049 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_050 f) (syn_wa
            (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f))
              (Class.cv (nb068_alpha_dummy_050 f)))
            (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f)
              (Class.cv (nb068_alpha_dummy_049 f)))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_053 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_054 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_055 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_049 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_056 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_049 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_057 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cphi (Class.cv (nb068_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_058 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_059 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_053)
          (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
              (syn_cphi (Class.cv (nb068_alpha_dummy_054))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_053)
          (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
              (syn_cphi (Class.cv (nb068_alpha_dummy_054))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_060 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_055 f)
          (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_055 f)
          (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_061 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_054))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_062 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_054))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_063 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_056 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_064 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_056 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_065 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_061)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_061))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_066 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_063 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_063 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_067 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_068 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_069 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_070 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_071 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_072 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_073 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_068))
          (Class.cv (nb068_alpha_dummy_069)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_074 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_071 f))
          (Class.cv (nb068_alpha_dummy_072 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_075 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_076 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_072 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_077 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_068)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_069)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_078 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_071 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_072 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_079 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_068))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_080 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_071 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_081 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_069))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_082 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_072 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_072 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_083 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_053)
          (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_053)
          (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_084 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_055 f)
          (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_055 f)
          (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_085 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_054))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_086 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_087 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_088 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_089 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_090 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_091 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_050 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_092 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_050 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_093 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cphi (Class.cv (nb068_alpha_dummy_090)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_094 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_095 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_089)
          (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
              (syn_cphi (Class.cv (nb068_alpha_dummy_090))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_089)
          (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
              (syn_cphi (Class.cv (nb068_alpha_dummy_090))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_096 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_091 f)
          (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_091 f)
          (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_097 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_090))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_098 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_090))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_099 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_092 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_100 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_092 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_101 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_097)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_097)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_097))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_102 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_099 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_099 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_099 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_103 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_104 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_105 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_106 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_107 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_108 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_109 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_104))
          (Class.cv (nb068_alpha_dummy_105)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_110 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_107 f))
          (Class.cv (nb068_alpha_dummy_108 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_107 f)) (Class.cv (nb068_alpha_dummy_108 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_111 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_112 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_108 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_113 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_104)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_105)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_114 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_107 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_108 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_115 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_104))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_116 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_107 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_117 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_105))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_118 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_108 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_108 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_119 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_089)
          (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_089)
          (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_120 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_091 f)
          (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_091 f)
          (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_121 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_090))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_122 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_123 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_124 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_125 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_126 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_000))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_127 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_128 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_129 : Var :=
  (freshVar
    (({(nb068_alpha_dummy_125)} : Finset Var) ∪ ({(nb068_alpha_dummy_126)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000))
          (Class.cv (nb068_alpha_dummy_125)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_130 (f : Var) : Var :=
  (freshVar (({(nb068_alpha_dummy_127 f)} : Finset Var) ∪
        ({(nb068_alpha_dummy_128 f)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f)
          (Class.cv (nb068_alpha_dummy_127 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_131 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_132 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_133 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_128 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_134 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_128 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_135 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cphi (Class.cv (nb068_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_136 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_137 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_131)
          (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
              (syn_cphi (Class.cv (nb068_alpha_dummy_132))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_131)
          (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
              (syn_cphi (Class.cv (nb068_alpha_dummy_132))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_138 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_133 f)
          (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_133 f)
          (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_139 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_132))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_140 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_132))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_141 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_134 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_142 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_134 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_143 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_139))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_144 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_141 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_145 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_146 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_147 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_148 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_149 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part002`. -/


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
noncomputable def nb068_alpha_dummy_150 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_151 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_146))
          (Class.cv (nb068_alpha_dummy_147)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_152 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_149 f))
          (Class.cv (nb068_alpha_dummy_150 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_153 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_154 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_150 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_155 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_146)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_147)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_156 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_149 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_150 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_157 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_146))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_158 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_149 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_159 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_147))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_160 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_150 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_150 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_161 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_131)
          (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_131)
          (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_162 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_133 f)
          (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_133 f)
          (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_163 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_132))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_164 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_165 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_166 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_167 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_168 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_169 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_127 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_170 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_127 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_171 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cphi (Class.cv (nb068_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_172 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_173 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_167)
          (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
              (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_167)
          (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
              (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_174 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_169 f)
          (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_169 f)
          (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_175 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_168))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_176 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_168))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_177 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_170 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_178 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_170 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_179 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_175))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_180 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_177 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_181 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_182 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_183 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_184 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_185 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_186 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_187 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_182))
          (Class.cv (nb068_alpha_dummy_183)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_188 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_185 f))
          (Class.cv (nb068_alpha_dummy_186 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_185 f)) (Class.cv (nb068_alpha_dummy_186 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_189 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_190 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_186 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_191 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_182)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_183)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_192 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_185 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_186 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_193 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_182))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_194 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_185 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_195 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_183))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_196 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_186 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_186 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_197 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_167)
          (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_167)
          (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_198 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_169 f)
          (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_169 f)
          (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_199 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_168))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_200 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_201 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_202 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_203 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_204 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_205 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_049 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_206 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_049 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_207 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cphi (Class.cv (nb068_alpha_dummy_204)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_208 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_209 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_203)
          (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
              (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_203)
          (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
              (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_210 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_205 f)
          (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_205 f)
          (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_211 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_204))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_212 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_204))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_213 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_206 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_214 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_206 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_215 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_211)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_211)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_211))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_216 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_213 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_213 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_213 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_217 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_218 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_219 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_220 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_221 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_222 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_223 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_218))
          (Class.cv (nb068_alpha_dummy_219)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_224 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_221 f))
          (Class.cv (nb068_alpha_dummy_222 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_221 f)) (Class.cv (nb068_alpha_dummy_222 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_225 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_226 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_222 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_227 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_218)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_219)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_228 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_221 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_222 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_229 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_218))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_230 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_221 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_231 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_219))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_232 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_222 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_222 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_233 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_203)
          (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_203)
          (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_234 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_205 f)
          (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_205 f)
          (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_235 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_204))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_236 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_237 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_238 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_239 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_240 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_241 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_242 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_243 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_244 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_245 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_241 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_246 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_241 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_247 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cphi (Class.cv (nb068_alpha_dummy_244)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_248 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_249 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_243)
          (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
              (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_243)
          (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
              (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_250 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_245 f)
          (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_245 f)
          (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_251 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_244))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_252 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_244))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_253 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_246 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_254 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_246 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_255 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_251)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_251)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_251))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_256 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_253 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_253 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_253 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_257 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_258 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_259 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_260 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_261 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_262 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_263 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_258))
          (Class.cv (nb068_alpha_dummy_259)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_264 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_261 f))
          (Class.cv (nb068_alpha_dummy_262 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_265 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_266 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_262 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_267 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_258)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_259)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_268 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_261 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_262 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_269 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_258))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_270 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_261 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_271 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_259))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_272 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_262 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_262 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_273 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_243)
          (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_243)
          (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_274 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_245 f)
          (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_245 f)
          (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_275 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_244))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_276 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_277 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_278 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_279 : Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
          (Class.cv (nb068_alpha_dummy_002)))).fv ∪
      ((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
          (Class.cv (nb068_alpha_dummy_002)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_280 (y : Var) (f : Var) : Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv ∪
      ((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_281 : Var :=
  (freshVar (((syn_crn (Class.cv (nb068_alpha_dummy_000)))).fv ∪
      ((Class.cv (nb068_alpha_dummy_002))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_282 (y : Var) (f : Var) : Var :=
  (freshVar (((syn_crn (Class.cv f))).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_283 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_284 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_285 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_286 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_287 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_288 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_289 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_285 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_290 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_285 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_291 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cphi (Class.cv (nb068_alpha_dummy_288)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_292 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_293 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_287)
          (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
              (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_287)
          (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
              (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_294 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_289 f)
          (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_289 f)
          (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_295 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_288))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_296 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_288))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_297 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_290 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_298 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_290 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_299 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_295)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_295))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part003`. -/


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
noncomputable def nb068_alpha_dummy_300 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_297 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_297 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_301 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_302 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_303 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_304 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_305 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_306 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_307 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_302))
          (Class.cv (nb068_alpha_dummy_303)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_308 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_305 f))
          (Class.cv (nb068_alpha_dummy_306 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_309 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_310 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_306 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_311 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_302)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_303)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_312 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_305 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_306 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_313 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_302))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_314 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_305 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_315 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_303))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_316 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_306 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_306 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_317 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_287)
          (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_287)
          (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_318 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_289 f)
          (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_289 f)
          (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_319 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_288))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_320 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_321 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_322 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_323 : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
            (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
            (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_324 (f : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
          (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
          (syn_cid))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_325 : Var :=
  (freshVar (((syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
          (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_326 (f : Var) : Var :=
  (freshVar (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪
      ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_327 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_328 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_329 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_330 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_331 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_332 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_333 : Var :=
  (freshVar
    (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪
      ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327))
              (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))
              (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329))
              (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
              (Class.cv (nb068_alpha_dummy_328)))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_334 (f : Var) : Var :=
  (freshVar (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪
        ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa
            (syn_wbr (Class.cv (nb068_alpha_dummy_330 f))
              (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f)))
            (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f))
              (Class.cv (nb068_alpha_dummy_331 f)))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_335 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_336 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_337 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_331 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_338 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_331 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_339 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cphi (Class.cv (nb068_alpha_dummy_336)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_340 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_341 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_335)
          (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
              (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_335)
          (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
              (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_342 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_337 f)
          (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_337 f)
          (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_343 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_336))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_344 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_336))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_345 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_338 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_346 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_338 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_347 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_343)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_343)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_343))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_348 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_345 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_345 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_345 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_349 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_350 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_351 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_352 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_353 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_354 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_355 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_350))
          (Class.cv (nb068_alpha_dummy_351)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_356 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_353 f))
          (Class.cv (nb068_alpha_dummy_354 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_353 f)) (Class.cv (nb068_alpha_dummy_354 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_357 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_358 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_354 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_359 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_350)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_351)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_360 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_353 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_354 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_361 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_350))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_362 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_353 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_363 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_351))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_364 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_354 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_354 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_365 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_335)
          (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_335)
          (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_366 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_337 f)
          (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_337 f)
          (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_367 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_336))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_368 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_369 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_370 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_371 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_372 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_373 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_332 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_374 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_332 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_375 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cphi (Class.cv (nb068_alpha_dummy_372)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_376 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_377 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_371)
          (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
              (syn_cphi (Class.cv (nb068_alpha_dummy_372))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_371)
          (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
              (syn_cphi (Class.cv (nb068_alpha_dummy_372))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_378 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_373 f)
          (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_373 f)
          (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_379 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_372))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_380 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_372))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_381 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_374 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_382 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_374 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_383 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_379)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_379))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_384 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_381 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_381 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_385 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_386 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_387 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_388 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_389 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_390 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_391 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_386))
          (Class.cv (nb068_alpha_dummy_387)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_392 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_389 f))
          (Class.cv (nb068_alpha_dummy_390 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_389 f)) (Class.cv (nb068_alpha_dummy_390 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_393 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_394 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_390 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_395 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_386)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_387)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_396 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_389 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_390 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_397 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_386))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_398 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_389 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_399 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_387))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_400 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_390 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_390 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_401 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_371)
          (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_371)
          (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_402 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_373 f)
          (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_373 f)
          (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_403 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_372))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_404 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_405 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_406 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_407 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_408 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_409 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_410 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_411 : Var :=
  (freshVar
    (({(nb068_alpha_dummy_407)} : Finset Var) ∪ ({(nb068_alpha_dummy_408)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb068_alpha_dummy_408)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
          (Class.cv (nb068_alpha_dummy_407)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_412 (f : Var) : Var :=
  (freshVar (({(nb068_alpha_dummy_409 f)} : Finset Var) ∪
        ({(nb068_alpha_dummy_410 f)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb068_alpha_dummy_410 f)) (syn_ccnv (Class.cv f))
          (Class.cv (nb068_alpha_dummy_409 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_413 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_414 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_415 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_410 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_416 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_410 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_417 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cphi (Class.cv (nb068_alpha_dummy_414)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_418 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_419 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_413)
          (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
              (syn_cphi (Class.cv (nb068_alpha_dummy_414))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_413)
          (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
              (syn_cphi (Class.cv (nb068_alpha_dummy_414))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_420 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_415 f)
          (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_415 f)
          (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_421 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_414))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_422 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_414))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_423 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_416 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_424 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_416 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_425 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_421)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_421))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_426 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_423 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_423 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_427 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_428 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_429 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_430 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_431 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_432 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_433 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_428))
          (Class.cv (nb068_alpha_dummy_429)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_434 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_431 f))
          (Class.cv (nb068_alpha_dummy_432 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_431 f)) (Class.cv (nb068_alpha_dummy_432 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_435 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_436 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_432 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_437 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_428)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_429)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_438 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_431 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_432 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_439 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_428))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_440 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_431 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_441 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_429))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_442 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_432 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_432 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_443 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_413)
          (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_413)
          (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_444 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_415 f)
          (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_415 f)
          (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_445 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_414))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_446 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_447 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_448 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_449 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part004`. -/


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
noncomputable def nb068_alpha_dummy_450 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_451 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_409 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_452 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_409 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_453 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cphi (Class.cv (nb068_alpha_dummy_450)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_454 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_455 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_449)
          (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
              (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_449)
          (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
              (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_456 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_451 f)
          (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_451 f)
          (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_457 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_450))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_458 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_450))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_459 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_452 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_460 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_452 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_461 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_457)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_457)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_457))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_462 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_459 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_459 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_459 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_463 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_464 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_465 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_466 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_467 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_468 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_469 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_464))
          (Class.cv (nb068_alpha_dummy_465)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_470 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_467 f))
          (Class.cv (nb068_alpha_dummy_468 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_467 f)) (Class.cv (nb068_alpha_dummy_468 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_471 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_472 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_468 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_473 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_464)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_465)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_474 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_467 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_468 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_475 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_464))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_476 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_467 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_477 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_465))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_478 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_468 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_468 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_479 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_449)
          (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_449)
          (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_480 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_451 f)
          (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_451 f)
          (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_481 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_450))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_482 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_483 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_484 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_485 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_486 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_487 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_331 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_488 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_331 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_489 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cphi (Class.cv (nb068_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_490 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_491 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_485)
          (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
              (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_485)
          (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
              (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_492 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_487 f)
          (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv ∪
      ((Class.cab (nb068_alpha_dummy_487 f)
          (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
              (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_493 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_486))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_494 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_486))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_495 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_488 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_496 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_488 f))).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_497 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_493)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_493)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_493))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_498 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_495 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb068_alpha_dummy_495 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb068_alpha_dummy_495 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_499 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_500 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_501 : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_502 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_503 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb068_alpha_dummy_504 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb068_alpha_dummy_505 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_500))
          (Class.cv (nb068_alpha_dummy_501)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_506 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_503 f))
          (Class.cv (nb068_alpha_dummy_504 f)))).fv ∪
      ((syn_cnin (Class.cv (nb068_alpha_dummy_503 f)) (Class.cv (nb068_alpha_dummy_504 f)))).fv)
    0)

@[expose]
noncomputable def nb068_alpha_dummy_507 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_508 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_504 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_509 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_500)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_501)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_510 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_503 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb068_alpha_dummy_504 f)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_511 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_500))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_512 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_503 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_513 : Var :=
  (freshVar
    (((Class.cv (nb068_alpha_dummy_501))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_514 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068_alpha_dummy_504 f))).fv ∪
      ((Class.cv (nb068_alpha_dummy_504 f))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_515 : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_485)
          (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_485)
          (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_516 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068_alpha_dummy_487 f)
          (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_487 f)
          (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_517 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_486))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_518 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_519 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv) 0)

@[expose]
noncomputable def nb068_alpha_dummy_520 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv ∪
      ((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv) 0)

theorem nb068_fresh_000 :
    (nb068_alpha_dummy_011) ∉
      (((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))).fv)
      0

theorem nb068_fresh_001 :
    (nb068_alpha_dummy_035) ∉
      (((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_002 (x : Var) (y : Var) :
    (nb068_alpha_dummy_012 x y) ∉
      (((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))))).fv)
      0

theorem nb068_fresh_003 (x : Var) (y : Var) :
    (nb068_alpha_dummy_036 x y) ∉
      (((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_004 :
    (nb068_alpha_dummy_059) ∉
      (((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cphi (Class.cv (nb068_alpha_dummy_054))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cphi (Class.cv (nb068_alpha_dummy_054))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_059] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cphi (Class.cv (nb068_alpha_dummy_054))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cphi (Class.cv (nb068_alpha_dummy_054))))))).fv)
      0

theorem nb068_fresh_005 :
    (nb068_alpha_dummy_083) ∉
      (((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_083] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_006 (f : Var) :
    (nb068_alpha_dummy_060 f) ∉
      (((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_060] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))))).fv)
      0

theorem nb068_fresh_007 (f : Var) :
    (nb068_alpha_dummy_084 f) ∉
      (((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_084] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_008 :
    (nb068_alpha_dummy_095) ∉
      (((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cphi (Class.cv (nb068_alpha_dummy_090))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cphi (Class.cv (nb068_alpha_dummy_090))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_095] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cphi (Class.cv (nb068_alpha_dummy_090))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cphi (Class.cv (nb068_alpha_dummy_090))))))).fv)
      0

theorem nb068_fresh_009 :
    (nb068_alpha_dummy_119) ∉
      (((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_119] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_010 (f : Var) :
    (nb068_alpha_dummy_096 f) ∉
      (((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_096] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))))).fv)
      0

theorem nb068_fresh_011 (f : Var) :
    (nb068_alpha_dummy_120 f) ∉
      (((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_120] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_012 :
    (nb068_alpha_dummy_137) ∉
      (((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cphi (Class.cv (nb068_alpha_dummy_132))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cphi (Class.cv (nb068_alpha_dummy_132))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_137] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cphi (Class.cv (nb068_alpha_dummy_132))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cphi (Class.cv (nb068_alpha_dummy_132))))))).fv)
      0

theorem nb068_fresh_013 :
    (nb068_alpha_dummy_161) ∉
      (((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_161] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_014 (f : Var) :
    (nb068_alpha_dummy_138 f) ∉
      (((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_138] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))))).fv)
      0

theorem nb068_fresh_015 (f : Var) :
    (nb068_alpha_dummy_162 f) ∉
      (((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_162] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_016 :
    (nb068_alpha_dummy_197) ∉
      (((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_197] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_017 :
    (nb068_alpha_dummy_173) ∉
      (((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_173] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv)
      0

theorem nb068_fresh_018 (f : Var) :
    (nb068_alpha_dummy_198 f) ∉
      (((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_198] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_019 (f : Var) :
    (nb068_alpha_dummy_174 f) ∉
      (((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_174] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv)
      0

theorem nb068_fresh_020 :
    (nb068_alpha_dummy_233) ∉
      (((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_233] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_021 :
    (nb068_alpha_dummy_209) ∉
      (((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_209] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv)
      0

theorem nb068_fresh_022 (f : Var) :
    (nb068_alpha_dummy_234 f) ∉
      (((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_234] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_023 (f : Var) :
    (nb068_alpha_dummy_210 f) ∉
      (((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_210] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv)
      0

theorem nb068_fresh_024 :
    (nb068_alpha_dummy_273) ∉
      (((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_273] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_025 :
    (nb068_alpha_dummy_249) ∉
      (((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_249] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_243)
            (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv)
      0

theorem nb068_fresh_026 (f : Var) :
    (nb068_alpha_dummy_274 f) ∉
      (((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_274] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_027 (f : Var) :
    (nb068_alpha_dummy_250 f) ∉
      (((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_250] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_245 f)
            (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv)
      0

theorem nb068_fresh_028 :
    (nb068_alpha_dummy_317) ∉
      (((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_317] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_029 :
    (nb068_alpha_dummy_293) ∉
      (((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_293] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv)
      0

theorem nb068_fresh_030 (f : Var) :
    (nb068_alpha_dummy_318 f) ∉
      (((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_318] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_031 (f : Var) :
    (nb068_alpha_dummy_294 f) ∉
      (((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_294] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv)
      0

theorem nb068_fresh_032 :
    (nb068_alpha_dummy_341) ∉
      (((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_341] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv)
      0

theorem nb068_fresh_033 :
    (nb068_alpha_dummy_365) ∉
      (((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_365] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_335)
            (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_034 (f : Var) :
    (nb068_alpha_dummy_342 f) ∉
      (((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_342] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv)
      0

theorem nb068_fresh_035 (f : Var) :
    (nb068_alpha_dummy_366 f) ∉
      (((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_366] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_337 f)
            (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_036 :
    (nb068_alpha_dummy_377) ∉
      (((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cphi (Class.cv (nb068_alpha_dummy_372))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cphi (Class.cv (nb068_alpha_dummy_372))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_377] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cphi (Class.cv (nb068_alpha_dummy_372))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cphi (Class.cv (nb068_alpha_dummy_372))))))).fv)
      0

theorem nb068_fresh_037 :
    (nb068_alpha_dummy_401) ∉
      (((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_401] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_371)
            (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_038 (f : Var) :
    (nb068_alpha_dummy_378 f) ∉
      (((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_378] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))))).fv)
      0

theorem nb068_fresh_039 (f : Var) :
    (nb068_alpha_dummy_402 f) ∉
      (((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_402] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_373 f)
            (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_040 :
    (nb068_alpha_dummy_419) ∉
      (((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cphi (Class.cv (nb068_alpha_dummy_414))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cphi (Class.cv (nb068_alpha_dummy_414))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_419] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cphi (Class.cv (nb068_alpha_dummy_414))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cphi (Class.cv (nb068_alpha_dummy_414))))))).fv)
      0

theorem nb068_fresh_041 :
    (nb068_alpha_dummy_443) ∉
      (((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_443] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_413)
            (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                  (syn_csn (syn_c0c))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part005`. -/


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

theorem nb068_fresh_042 (f : Var) :
    (nb068_alpha_dummy_420 f) ∉
      (((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_420] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv)
      0

theorem nb068_fresh_043 (f : Var) :
    (nb068_alpha_dummy_444 f) ∉
      (((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_444] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_415 f)
            (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_044 :
    (nb068_alpha_dummy_479) ∉
      (((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_479] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_045 :
    (nb068_alpha_dummy_455) ∉
      (((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_455] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_449)
            (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv)
      0

theorem nb068_fresh_046 (f : Var) :
    (nb068_alpha_dummy_480 f) ∉
      (((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_480] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_047 (f : Var) :
    (nb068_alpha_dummy_456 f) ∉
      (((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_456] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_451 f)
            (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv)
      0

theorem nb068_fresh_048 :
    (nb068_alpha_dummy_515) ∉
      (((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_515] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_049 :
    (nb068_alpha_dummy_491) ∉
      (((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_491] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv)
      0

theorem nb068_fresh_050 (f : Var) :
    (nb068_alpha_dummy_516 f) ∉
      (((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_516] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb068_fresh_051 (f : Var) :
    (nb068_alpha_dummy_492 f) ∉
      (((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_492] using
    freshVar_not_mem
      (((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv)
      0

theorem nb068_fresh_052 :
    (nb068_alpha_dummy_125) ∉ (((Class.cv (nb068_alpha_dummy_000))).fv) := by
  simpa only [nb068_alpha_dummy_125] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_000))).fv) 0

theorem nb068_fresh_053 :
    (nb068_alpha_dummy_126) ∉ (((Class.cv (nb068_alpha_dummy_000))).fv) := by
  simpa only [nb068_alpha_dummy_126] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_000))).fv) 1

theorem nb068_distinct_054 : (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_126) := by
  simpa only [nb068_alpha_dummy_125, nb068_alpha_dummy_126] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_055 :
    (nb068_alpha_dummy_045) ∉
      (((Class.cv (nb068_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv)
      0

theorem nb068_fresh_056 :
    (nb068_alpha_dummy_046) ∉
      (((Class.cv (nb068_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv)
      1

theorem nb068_fresh_057 :
    (nb068_alpha_dummy_047) ∉
      (((Class.cv (nb068_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_047] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv)
      2

theorem nb068_distinct_058 : (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_046) := by
  simpa only [nb068_alpha_dummy_045, nb068_alpha_dummy_046] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_059 : (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_047) := by
  simpa only [nb068_alpha_dummy_045, nb068_alpha_dummy_047] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_060 : (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_047) := by
  simpa only [nb068_alpha_dummy_046, nb068_alpha_dummy_047] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_061 :
    (nb068_alpha_dummy_283) ∉
      (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb068_alpha_dummy_283] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0

theorem nb068_fresh_062 :
    (nb068_alpha_dummy_284) ∉
      (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb068_alpha_dummy_284] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1

theorem nb068_distinct_063 : (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_284) := by
  simpa only [nb068_alpha_dummy_283, nb068_alpha_dummy_284] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_fresh_064 :
    (nb068_alpha_dummy_005) ∉
      (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) :=
  by
  simpa only [nb068_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv)
      0

theorem nb068_fresh_065 :
    (nb068_alpha_dummy_006) ∉
      (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) :=
  by
  simpa only [nb068_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv)
      1

theorem nb068_distinct_066 : (nb068_alpha_dummy_005) ≠ (nb068_alpha_dummy_006) := by
  simpa only [nb068_alpha_dummy_005, nb068_alpha_dummy_006] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_067 :
    (nb068_alpha_dummy_013) ∉ (((Class.cv (nb068_alpha_dummy_006))).fv) := by
  simpa only [nb068_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_006))).fv) 0

theorem nb068_fresh_068 :
    (nb068_alpha_dummy_014) ∉ (((Class.cv (nb068_alpha_dummy_006))).fv) := by
  simpa only [nb068_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_006))).fv) 1

theorem nb068_distinct_069 : (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_014) := by
  simpa only [nb068_alpha_dummy_013, nb068_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_070 (x : Var) (y : Var) :
    (nb068_alpha_dummy_015 x y) ∉ (((Class.cv (nb068_alpha_dummy_008 x y))).fv) := by
  simpa only [nb068_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_008 x y))).fv) 0

theorem nb068_fresh_071 (x : Var) (y : Var) :
    (nb068_alpha_dummy_016 x y) ∉ (((Class.cv (nb068_alpha_dummy_008 x y))).fv) := by
  simpa only [nb068_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_008 x y))).fv) 1

theorem nb068_distinct_072 (x : Var) (y : Var) :
    (nb068_alpha_dummy_015 x y) ≠ (nb068_alpha_dummy_016 x y) := by
  simpa only [nb068_alpha_dummy_015, nb068_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_008 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_073 :
    (nb068_alpha_dummy_019) ∉
      (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_074 :
    (nb068_alpha_dummy_020) ∉
      (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_075 :
    (nb068_alpha_dummy_021) ∉
      (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_076 : (nb068_alpha_dummy_019) ≠ (nb068_alpha_dummy_020) := by
  simpa only [nb068_alpha_dummy_019, nb068_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_077 : (nb068_alpha_dummy_019) ≠ (nb068_alpha_dummy_021) := by
  simpa only [nb068_alpha_dummy_019, nb068_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_078 : (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_021) := by
  simpa only [nb068_alpha_dummy_020, nb068_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_079 (x : Var) (y : Var) :
    (nb068_alpha_dummy_022 x y) ∉
      (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_080 (x : Var) (y : Var) :
    (nb068_alpha_dummy_023 x y) ∉
      (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_081 (x : Var) (y : Var) :
    (nb068_alpha_dummy_024 x y) ∉
      (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_082 (x : Var) (y : Var) :
    (nb068_alpha_dummy_022 x y) ≠ (nb068_alpha_dummy_023 x y) := by
  simpa only [nb068_alpha_dummy_022, nb068_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_distinct_083 (x : Var) (y : Var) :
    (nb068_alpha_dummy_022 x y) ≠ (nb068_alpha_dummy_024 x y) := by
  simpa only [nb068_alpha_dummy_022, nb068_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb068_distinct_084 (x : Var) (y : Var) :
    (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_024 x y) := by
  simpa only [nb068_alpha_dummy_023, nb068_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb068_fresh_085 :
    (nb068_alpha_dummy_031) ∉
      (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_020))).fv) :=
  by
  simpa only [nb068_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_020))).fv)
      0

theorem nb068_fresh_086 :
    (nb068_alpha_dummy_027) ∉
      (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) :=
  by
  simpa only [nb068_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv)
      0

theorem nb068_fresh_087 :
    (nb068_alpha_dummy_033) ∉
      (((Class.cv (nb068_alpha_dummy_021))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) :=
  by
  simpa only [nb068_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_021))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv)
      0

theorem nb068_fresh_088 (x : Var) (y : Var) :
    (nb068_alpha_dummy_032 x y) ∉
      (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb068_alpha_dummy_023 x y))).fv) :=
  by
  simpa only [nb068_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb068_alpha_dummy_023 x y))).fv)
      0

theorem nb068_fresh_089 (x : Var) (y : Var) :
    (nb068_alpha_dummy_028 x y) ∉
      (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb068_alpha_dummy_024 x y))).fv) :=
  by
  simpa only [nb068_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb068_alpha_dummy_024 x y))).fv)
      0

theorem nb068_fresh_090 (x : Var) (y : Var) :
    (nb068_alpha_dummy_034 x y) ∉
      (((Class.cv (nb068_alpha_dummy_024 x y))).fv ∪
        ((Class.cv (nb068_alpha_dummy_024 x y))).fv) :=
  by
  simpa only [nb068_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_024 x y))).fv ∪
        ((Class.cv (nb068_alpha_dummy_024 x y))).fv)
      0

theorem nb068_fresh_091 :
    (nb068_alpha_dummy_053) ∉
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) :=
  by
  simpa only [nb068_alpha_dummy_053] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv)
      0

theorem nb068_fresh_092 :
    (nb068_alpha_dummy_054) ∉
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) :=
  by
  simpa only [nb068_alpha_dummy_054] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv)
      1

theorem nb068_distinct_093 : (nb068_alpha_dummy_053) ≠ (nb068_alpha_dummy_054) := by
  simpa only [nb068_alpha_dummy_053, nb068_alpha_dummy_054] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_094 :
    (nb068_alpha_dummy_089) ∉
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) :=
  by
  simpa only [nb068_alpha_dummy_089] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv)
      0

theorem nb068_fresh_095 :
    (nb068_alpha_dummy_090) ∉
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) :=
  by
  simpa only [nb068_alpha_dummy_090] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv)
      1

theorem nb068_distinct_096 : (nb068_alpha_dummy_089) ≠ (nb068_alpha_dummy_090) := by
  simpa only [nb068_alpha_dummy_089, nb068_alpha_dummy_090] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_097 :
    (nb068_alpha_dummy_203) ∉
      (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) :=
  by
  simpa only [nb068_alpha_dummy_203] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv)
      0

theorem nb068_fresh_098 :
    (nb068_alpha_dummy_204) ∉
      (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) :=
  by
  simpa only [nb068_alpha_dummy_204] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv)
      1

theorem nb068_distinct_099 : (nb068_alpha_dummy_203) ≠ (nb068_alpha_dummy_204) := by
  simpa only [nb068_alpha_dummy_203, nb068_alpha_dummy_204] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_100 (f : Var) :
    (nb068_alpha_dummy_055 f) ∉
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_055] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv)
      0

theorem nb068_fresh_101 (f : Var) :
    (nb068_alpha_dummy_056 f) ∉
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_056] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv)
      1

theorem nb068_distinct_102 (f : Var) :
    (nb068_alpha_dummy_055 f) ≠ (nb068_alpha_dummy_056 f) := by
  simpa only [nb068_alpha_dummy_055, nb068_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_049 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_103 (f : Var) :
    (nb068_alpha_dummy_091 f) ∉
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_091] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv)
      0

theorem nb068_fresh_104 (f : Var) :
    (nb068_alpha_dummy_092 f) ∉
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_092] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv)
      1

theorem nb068_distinct_105 (f : Var) :
    (nb068_alpha_dummy_091 f) ≠ (nb068_alpha_dummy_092 f) := by
  simpa only [nb068_alpha_dummy_091, nb068_alpha_dummy_092] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_050 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_106 (f : Var) :
    (nb068_alpha_dummy_205 f) ∉
      (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_205] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv)
      0

theorem nb068_fresh_107 (f : Var) :
    (nb068_alpha_dummy_206 f) ∉
      (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_206] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv)
      1

theorem nb068_distinct_108 (f : Var) :
    (nb068_alpha_dummy_205 f) ≠ (nb068_alpha_dummy_206 f) := by
  simpa only [nb068_alpha_dummy_205, nb068_alpha_dummy_206] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_049 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_109 :
    (nb068_alpha_dummy_061) ∉ (((Class.cv (nb068_alpha_dummy_054))).fv) := by
  simpa only [nb068_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_054))).fv) 0

theorem nb068_fresh_110 :
    (nb068_alpha_dummy_062) ∉ (((Class.cv (nb068_alpha_dummy_054))).fv) := by
  simpa only [nb068_alpha_dummy_062] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_054))).fv) 1

theorem nb068_distinct_111 : (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_062) := by
  simpa only [nb068_alpha_dummy_061, nb068_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_054))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_112 (f : Var) :
    (nb068_alpha_dummy_063 f) ∉ (((Class.cv (nb068_alpha_dummy_056 f))).fv) := by
  simpa only [nb068_alpha_dummy_063] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_056 f))).fv) 0

theorem nb068_fresh_113 (f : Var) :
    (nb068_alpha_dummy_064 f) ∉ (((Class.cv (nb068_alpha_dummy_056 f))).fv) := by
  simpa only [nb068_alpha_dummy_064] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_056 f))).fv) 1

theorem nb068_distinct_114 (f : Var) :
    (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_064 f) := by
  simpa only [nb068_alpha_dummy_063, nb068_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_056 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_115 :
    (nb068_alpha_dummy_067) ∉
      (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_067] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_116 :
    (nb068_alpha_dummy_068) ∉
      (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_068] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_117 :
    (nb068_alpha_dummy_069) ∉
      (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_069] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_118 : (nb068_alpha_dummy_067) ≠ (nb068_alpha_dummy_068) := by
  simpa only [nb068_alpha_dummy_067, nb068_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_119 : (nb068_alpha_dummy_067) ≠ (nb068_alpha_dummy_069) := by
  simpa only [nb068_alpha_dummy_067, nb068_alpha_dummy_069] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_120 : (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_069) := by
  simpa only [nb068_alpha_dummy_068, nb068_alpha_dummy_069] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_121 (f : Var) :
    (nb068_alpha_dummy_070 f) ∉
      (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_070] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_122 (f : Var) :
    (nb068_alpha_dummy_071 f) ∉
      (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_071] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_123 (f : Var) :
    (nb068_alpha_dummy_072 f) ∉
      (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_072] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_124 (f : Var) :
    (nb068_alpha_dummy_070 f) ≠ (nb068_alpha_dummy_071 f) := by
  simpa only [nb068_alpha_dummy_070, nb068_alpha_dummy_071] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_125 (f : Var) :
    (nb068_alpha_dummy_070 f) ≠ (nb068_alpha_dummy_072 f) := by
  simpa only [nb068_alpha_dummy_070, nb068_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_126 (f : Var) :
    (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_072 f) := by
  simpa only [nb068_alpha_dummy_071, nb068_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_127 :
    (nb068_alpha_dummy_079) ∉
      (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_068))).fv) :=
  by
  simpa only [nb068_alpha_dummy_079] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_068))).fv)
      0

theorem nb068_fresh_128 :
    (nb068_alpha_dummy_075) ∉
      (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) :=
  by
  simpa only [nb068_alpha_dummy_075] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv)
      0

theorem nb068_fresh_129 :
    (nb068_alpha_dummy_081) ∉
      (((Class.cv (nb068_alpha_dummy_069))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) :=
  by
  simpa only [nb068_alpha_dummy_081] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_069))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv)
      0

theorem nb068_fresh_130 (f : Var) :
    (nb068_alpha_dummy_080 f) ∉
      (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_071 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_080] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_071 f))).fv)
      0

theorem nb068_fresh_131 (f : Var) :
    (nb068_alpha_dummy_076 f) ∉
      (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_076] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv)
      0

theorem nb068_fresh_132 (f : Var) :
    (nb068_alpha_dummy_082 f) ∉
      (((Class.cv (nb068_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_082] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv)
      0

theorem nb068_fresh_133 :
    (nb068_alpha_dummy_097) ∉ (((Class.cv (nb068_alpha_dummy_090))).fv) := by
  simpa only [nb068_alpha_dummy_097] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_090))).fv) 0

theorem nb068_fresh_134 :
    (nb068_alpha_dummy_098) ∉ (((Class.cv (nb068_alpha_dummy_090))).fv) := by
  simpa only [nb068_alpha_dummy_098] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_090))).fv) 1

theorem nb068_distinct_135 : (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_098) := by
  simpa only [nb068_alpha_dummy_097, nb068_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_090))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_136 (f : Var) :
    (nb068_alpha_dummy_099 f) ∉ (((Class.cv (nb068_alpha_dummy_092 f))).fv) := by
  simpa only [nb068_alpha_dummy_099] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_092 f))).fv) 0

theorem nb068_fresh_137 (f : Var) :
    (nb068_alpha_dummy_100 f) ∉ (((Class.cv (nb068_alpha_dummy_092 f))).fv) := by
  simpa only [nb068_alpha_dummy_100] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_092 f))).fv) 1

theorem nb068_distinct_138 (f : Var) :
    (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_100 f) := by
  simpa only [nb068_alpha_dummy_099, nb068_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_092 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_139 :
    (nb068_alpha_dummy_103) ∉
      (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_103] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_140 :
    (nb068_alpha_dummy_104) ∉
      (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_104] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_141 :
    (nb068_alpha_dummy_105) ∉
      (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_105] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_142 : (nb068_alpha_dummy_103) ≠ (nb068_alpha_dummy_104) := by
  simpa only [nb068_alpha_dummy_103, nb068_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_143 : (nb068_alpha_dummy_103) ≠ (nb068_alpha_dummy_105) := by
  simpa only [nb068_alpha_dummy_103, nb068_alpha_dummy_105] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_144 : (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_105) := by
  simpa only [nb068_alpha_dummy_104, nb068_alpha_dummy_105] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_145 (f : Var) :
    (nb068_alpha_dummy_106 f) ∉
      (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_106] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_146 (f : Var) :
    (nb068_alpha_dummy_107 f) ∉
      (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_107] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_147 (f : Var) :
    (nb068_alpha_dummy_108 f) ∉
      (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_108] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_148 (f : Var) :
    (nb068_alpha_dummy_106 f) ≠ (nb068_alpha_dummy_107 f) := by
  simpa only [nb068_alpha_dummy_106, nb068_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_149 (f : Var) :
    (nb068_alpha_dummy_106 f) ≠ (nb068_alpha_dummy_108 f) := by
  simpa only [nb068_alpha_dummy_106, nb068_alpha_dummy_108] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_150 (f : Var) :
    (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_108 f) := by
  simpa only [nb068_alpha_dummy_107, nb068_alpha_dummy_108] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_151 :
    (nb068_alpha_dummy_115) ∉
      (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_104))).fv) :=
  by
  simpa only [nb068_alpha_dummy_115] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_104))).fv)
      0

theorem nb068_fresh_152 :
    (nb068_alpha_dummy_111) ∉
      (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) :=
  by
  simpa only [nb068_alpha_dummy_111] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv)
      0

theorem nb068_fresh_153 :
    (nb068_alpha_dummy_117) ∉
      (((Class.cv (nb068_alpha_dummy_105))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) :=
  by
  simpa only [nb068_alpha_dummy_117] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_105))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv)
      0

theorem nb068_fresh_154 (f : Var) :
    (nb068_alpha_dummy_116 f) ∉
      (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_107 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_116] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_107 f))).fv)
      0

theorem nb068_fresh_155 (f : Var) :
    (nb068_alpha_dummy_112 f) ∉
      (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_112] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv)
      0

theorem nb068_fresh_156 (f : Var) :
    (nb068_alpha_dummy_118 f) ∉
      (((Class.cv (nb068_alpha_dummy_108 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_118] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_108 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv)
      0

theorem nb068_fresh_157 :
    (nb068_alpha_dummy_131) ∉
      (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) :=
  by
  simpa only [nb068_alpha_dummy_131] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv)
      0

theorem nb068_fresh_158 :
    (nb068_alpha_dummy_132) ∉
      (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) :=
  by
  simpa only [nb068_alpha_dummy_132] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv)
      1

theorem nb068_distinct_159 : (nb068_alpha_dummy_131) ≠ (nb068_alpha_dummy_132) := by
  simpa only [nb068_alpha_dummy_131, nb068_alpha_dummy_132] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_160 :
    (nb068_alpha_dummy_167) ∉
      (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) :=
  by
  simpa only [nb068_alpha_dummy_167] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv)
      0

theorem nb068_fresh_161 :
    (nb068_alpha_dummy_168) ∉
      (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) :=
  by
  simpa only [nb068_alpha_dummy_168] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv)
      1

theorem nb068_distinct_162 : (nb068_alpha_dummy_167) ≠ (nb068_alpha_dummy_168) := by
  simpa only [nb068_alpha_dummy_167, nb068_alpha_dummy_168] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_163 (f : Var) :
    (nb068_alpha_dummy_133 f) ∉
      (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_133] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv)
      0

theorem nb068_fresh_164 (f : Var) :
    (nb068_alpha_dummy_134 f) ∉
      (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_134] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv)
      1

theorem nb068_distinct_165 (f : Var) :
    (nb068_alpha_dummy_133 f) ≠ (nb068_alpha_dummy_134 f) := by
  simpa only [nb068_alpha_dummy_133, nb068_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_128 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_166 (f : Var) :
    (nb068_alpha_dummy_169 f) ∉
      (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_169] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv)
      0

theorem nb068_fresh_167 (f : Var) :
    (nb068_alpha_dummy_170 f) ∉
      (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_170] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv)
      1

theorem nb068_distinct_168 (f : Var) :
    (nb068_alpha_dummy_169 f) ≠ (nb068_alpha_dummy_170 f) := by
  simpa only [nb068_alpha_dummy_169, nb068_alpha_dummy_170] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_127 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_169 :
    (nb068_alpha_dummy_139) ∉ (((Class.cv (nb068_alpha_dummy_132))).fv) := by
  simpa only [nb068_alpha_dummy_139] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_132))).fv) 0

theorem nb068_fresh_170 :
    (nb068_alpha_dummy_140) ∉ (((Class.cv (nb068_alpha_dummy_132))).fv) := by
  simpa only [nb068_alpha_dummy_140] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_132))).fv) 1

theorem nb068_distinct_171 : (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_140) := by
  simpa only [nb068_alpha_dummy_139, nb068_alpha_dummy_140] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_132))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_172 (f : Var) :
    (nb068_alpha_dummy_141 f) ∉ (((Class.cv (nb068_alpha_dummy_134 f))).fv) := by
  simpa only [nb068_alpha_dummy_141] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_134 f))).fv) 0

theorem nb068_fresh_173 (f : Var) :
    (nb068_alpha_dummy_142 f) ∉ (((Class.cv (nb068_alpha_dummy_134 f))).fv) := by
  simpa only [nb068_alpha_dummy_142] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_134 f))).fv) 1

theorem nb068_distinct_174 (f : Var) :
    (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_142 f) := by
  simpa only [nb068_alpha_dummy_141, nb068_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_134 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_175 :
    (nb068_alpha_dummy_145) ∉
      (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_145] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_176 :
    (nb068_alpha_dummy_146) ∉
      (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_146] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_177 :
    (nb068_alpha_dummy_147) ∉
      (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_147] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_178 : (nb068_alpha_dummy_145) ≠ (nb068_alpha_dummy_146) := by
  simpa only [nb068_alpha_dummy_145, nb068_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_179 : (nb068_alpha_dummy_145) ≠ (nb068_alpha_dummy_147) := by
  simpa only [nb068_alpha_dummy_145, nb068_alpha_dummy_147] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_180 : (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_147) := by
  simpa only [nb068_alpha_dummy_146, nb068_alpha_dummy_147] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_181 (f : Var) :
    (nb068_alpha_dummy_148 f) ∉
      (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_148] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_182 (f : Var) :
    (nb068_alpha_dummy_149 f) ∉
      (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_149] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_183 (f : Var) :
    (nb068_alpha_dummy_150 f) ∉
      (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_150] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_184 (f : Var) :
    (nb068_alpha_dummy_148 f) ≠ (nb068_alpha_dummy_149 f) := by
  simpa only [nb068_alpha_dummy_148, nb068_alpha_dummy_149] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_185 (f : Var) :
    (nb068_alpha_dummy_148 f) ≠ (nb068_alpha_dummy_150 f) := by
  simpa only [nb068_alpha_dummy_148, nb068_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_186 (f : Var) :
    (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_150 f) := by
  simpa only [nb068_alpha_dummy_149, nb068_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_187 :
    (nb068_alpha_dummy_157) ∉
      (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_146))).fv) :=
  by
  simpa only [nb068_alpha_dummy_157] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_146))).fv)
      0

theorem nb068_fresh_188 :
    (nb068_alpha_dummy_153) ∉
      (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) :=
  by
  simpa only [nb068_alpha_dummy_153] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv)
      0

theorem nb068_fresh_189 :
    (nb068_alpha_dummy_159) ∉
      (((Class.cv (nb068_alpha_dummy_147))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) :=
  by
  simpa only [nb068_alpha_dummy_159] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_147))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv)
      0

theorem nb068_fresh_190 (f : Var) :
    (nb068_alpha_dummy_158 f) ∉
      (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_149 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_158] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_149 f))).fv)
      0

theorem nb068_fresh_191 (f : Var) :
    (nb068_alpha_dummy_154 f) ∉
      (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_154] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
