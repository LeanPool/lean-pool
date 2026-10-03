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

/-! Certificates from `NAR4C061C001Part001`. -/


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
noncomputable def nb061_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb061_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb061_alpha_dummy_002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

@[expose]
noncomputable def nb061_alpha_dummy_003 : Var :=
  (freshVar
    (({(nb061_alpha_dummy_001)} : Finset Var) ∪ ({(nb061_alpha_dummy_000)} : Finset Var) ∪
      ((syn_wral (nb061_alpha_dummy_002) (Class.cv (nb061_alpha_dummy_000))
          (syn_wbr (Class.cv (nb061_alpha_dummy_002)) (Class.cv (nb061_alpha_dummy_001))
            (Class.cv (nb061_alpha_dummy_002))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_004 (x : Var) (r : Var) (a : Var) : Var :=
  (freshVar (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪
      ((syn_wral x (Class.cv a) (syn_wbr (Class.cv x) (Class.cv r) (Class.cv x)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_005 : Var :=
  (freshVar
    (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_006 : Var :=
  (freshVar
    (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_007 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_008 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_009 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cphi (Class.cv (nb061_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_010 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_011 : Var :=
  (freshVar (((Class.cab (nb061_alpha_dummy_005)
          (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
              (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv ∪
      ((Class.cab (nb061_alpha_dummy_005)
          (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
              (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_012 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb061_alpha_dummy_007 r a)
          (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
              (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv ∪
      ((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
              (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_013 : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_006))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_014 : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_006))).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_015 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_008 r a))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_016 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_008 r a))).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb061_alpha_dummy_013)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb061_alpha_dummy_013)) (syn_c1c))).fv ∪
      ((Class.cv (nb061_alpha_dummy_013))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_018 (r : Var) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb061_alpha_dummy_015 r a)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb061_alpha_dummy_015 r a)) (syn_c1c))).fv ∪
      ((Class.cv (nb061_alpha_dummy_015 r a))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_019 : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_020 : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_021 : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb061_alpha_dummy_022 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_023 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_024 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb061_alpha_dummy_025 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb061_alpha_dummy_020))
          (Class.cv (nb061_alpha_dummy_021)))).fv ∪
      ((syn_cnin (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_026 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a))
          (Class.cv (nb061_alpha_dummy_024 r a)))).fv ∪
      ((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a))
          (Class.cv (nb061_alpha_dummy_024 r a)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_027 : Var :=
  (freshVar
    (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_028 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪
      ((Class.cv (nb061_alpha_dummy_024 r a))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_029 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb061_alpha_dummy_020)))).fv ∪
      ((syn_ccompl (Class.cv (nb061_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_030 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb061_alpha_dummy_023 r a)))).fv ∪
      ((syn_ccompl (Class.cv (nb061_alpha_dummy_024 r a)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_031 : Var :=
  (freshVar
    (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_020))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_032 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪
      ((Class.cv (nb061_alpha_dummy_023 r a))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_033 : Var :=
  (freshVar
    (((Class.cv (nb061_alpha_dummy_021))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_034 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_024 r a))).fv ∪
      ((Class.cv (nb061_alpha_dummy_024 r a))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_035 : Var :=
  (freshVar (((Class.cab (nb061_alpha_dummy_005)
          (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_005)
          (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_036 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb061_alpha_dummy_007 r a)
          (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
              (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_007 r a)
          (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
              (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_037 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_006))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_038 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_039 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb061_alpha_dummy_006)))).fv ∪
      ((syn_cphi (Class.cv (nb061_alpha_dummy_006)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_040 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))).fv ∪
      ((syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_041 : Var :=
  (freshVar
    (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_042 : Var :=
  (freshVar
    (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_043 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_044 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_045 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cphi (Class.cv (nb061_alpha_dummy_042)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_046 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb061_alpha_dummy_043 x)
            (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_047 : Var :=
  (freshVar (((Class.cab (nb061_alpha_dummy_041)
          (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
              (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv ∪
      ((Class.cab (nb061_alpha_dummy_041)
          (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
              (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_048 (x : Var) : Var :=
  (freshVar (((Class.cab (nb061_alpha_dummy_043 x)
          (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
              (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv ∪
      ((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
              (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_049 : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_042))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_050 : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_042))).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_051 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_044 x))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_052 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_044 x))).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_053 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb061_alpha_dummy_049)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb061_alpha_dummy_049)) (syn_c1c))).fv ∪
      ((Class.cv (nb061_alpha_dummy_049))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_054 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb061_alpha_dummy_051 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb061_alpha_dummy_051 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb061_alpha_dummy_051 x))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_055 : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_056 : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_057 : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb061_alpha_dummy_058 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_059 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb061_alpha_dummy_060 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb061_alpha_dummy_061 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb061_alpha_dummy_056))
          (Class.cv (nb061_alpha_dummy_057)))).fv ∪
      ((syn_cnin (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_062 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb061_alpha_dummy_059 x))
          (Class.cv (nb061_alpha_dummy_060 x)))).fv ∪
      ((syn_cnin (Class.cv (nb061_alpha_dummy_059 x)) (Class.cv (nb061_alpha_dummy_060 x)))).fv)
    0)

@[expose]
noncomputable def nb061_alpha_dummy_063 : Var :=
  (freshVar
    (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_064 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪
      ((Class.cv (nb061_alpha_dummy_060 x))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_065 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb061_alpha_dummy_056)))).fv ∪
      ((syn_ccompl (Class.cv (nb061_alpha_dummy_057)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_066 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb061_alpha_dummy_059 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb061_alpha_dummy_060 x)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_067 : Var :=
  (freshVar
    (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_056))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_068 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪
      ((Class.cv (nb061_alpha_dummy_059 x))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_069 : Var :=
  (freshVar
    (((Class.cv (nb061_alpha_dummy_057))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_070 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061_alpha_dummy_060 x))).fv ∪
      ((Class.cv (nb061_alpha_dummy_060 x))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_071 : Var :=
  (freshVar (((Class.cab (nb061_alpha_dummy_041)
          (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
              (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_041)
          (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
              (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_072 (x : Var) : Var :=
  (freshVar (((Class.cab (nb061_alpha_dummy_043 x)
          (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
              (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_043 x)
          (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
              (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_073 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_042))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_074 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_075 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb061_alpha_dummy_042)))).fv ∪
      ((syn_cphi (Class.cv (nb061_alpha_dummy_042)))).fv) 0)

@[expose]
noncomputable def nb061_alpha_dummy_076 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))).fv ∪
      ((syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))).fv) 0)

theorem nb061_fresh_000 :
    (nb061_alpha_dummy_035) ∉
      (((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb061_fresh_001 :
    (nb061_alpha_dummy_011) ∉
      (((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv)
      0

theorem nb061_fresh_002 (r : Var) (a : Var) :
    (nb061_alpha_dummy_036 r a) ∉
      (((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb061_fresh_003 (r : Var) (a : Var) :
    (nb061_alpha_dummy_012 r a) ∉
      (((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv)
      0

theorem nb061_fresh_004 :
    (nb061_alpha_dummy_047) ∉
      (((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_047] using
    freshVar_not_mem
      (((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv)
      0

theorem nb061_fresh_005 :
    (nb061_alpha_dummy_071) ∉
      (((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb061_fresh_006 (x : Var) :
    (nb061_alpha_dummy_048 x) ∉
      (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_048] using
    freshVar_not_mem
      (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv)
      0

theorem nb061_fresh_007 (x : Var) :
    (nb061_alpha_dummy_072 x) ∉
      (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_043 x)
            (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_043 x)
            (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb061_fresh_008 :
    (nb061_alpha_dummy_005) ∉
      (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) :=
  by
  simpa only [nb061_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv)
      0

theorem nb061_fresh_009 :
    (nb061_alpha_dummy_006) ∉
      (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) :=
  by
  simpa only [nb061_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv)
      1

theorem nb061_distinct_010 : (nb061_alpha_dummy_005) ≠ (nb061_alpha_dummy_006) := by
  simpa only [nb061_alpha_dummy_005, nb061_alpha_dummy_006] using
    (freshVar_injective
      (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb061_fresh_011 :
    (nb061_alpha_dummy_041) ∉
      (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) :=
  by
  simpa only [nb061_alpha_dummy_041] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv)
      0

theorem nb061_fresh_012 :
    (nb061_alpha_dummy_042) ∉
      (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) :=
  by
  simpa only [nb061_alpha_dummy_042] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv)
      1

theorem nb061_distinct_013 : (nb061_alpha_dummy_041) ≠ (nb061_alpha_dummy_042) := by
  simpa only [nb061_alpha_dummy_041, nb061_alpha_dummy_042] using
    (freshVar_injective
      (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb061_fresh_014 :
    (nb061_alpha_dummy_013) ∉ (((Class.cv (nb061_alpha_dummy_006))).fv) := by
  simpa only [nb061_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_006))).fv) 0

theorem nb061_fresh_015 :
    (nb061_alpha_dummy_014) ∉ (((Class.cv (nb061_alpha_dummy_006))).fv) := by
  simpa only [nb061_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_006))).fv) 1

theorem nb061_distinct_016 : (nb061_alpha_dummy_013) ≠ (nb061_alpha_dummy_014) := by
  simpa only [nb061_alpha_dummy_013, nb061_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_017 (r : Var) (a : Var) :
    (nb061_alpha_dummy_015 r a) ∉ (((Class.cv (nb061_alpha_dummy_008 r a))).fv) := by
  simpa only [nb061_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_008 r a))).fv) 0

theorem nb061_fresh_018 (r : Var) (a : Var) :
    (nb061_alpha_dummy_016 r a) ∉ (((Class.cv (nb061_alpha_dummy_008 r a))).fv) := by
  simpa only [nb061_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_008 r a))).fv) 1

theorem nb061_distinct_019 (r : Var) (a : Var) :
    (nb061_alpha_dummy_015 r a) ≠ (nb061_alpha_dummy_016 r a) := by
  simpa only [nb061_alpha_dummy_015, nb061_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_008 r a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb061_fresh_020 :
    (nb061_alpha_dummy_019) ∉
      (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0

theorem nb061_fresh_021 :
    (nb061_alpha_dummy_020) ∉
      (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1

theorem nb061_fresh_022 :
    (nb061_alpha_dummy_021) ∉
      (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2

theorem nb061_distinct_023 : (nb061_alpha_dummy_019) ≠ (nb061_alpha_dummy_020) := by
  simpa only [nb061_alpha_dummy_019, nb061_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb061_distinct_024 : (nb061_alpha_dummy_019) ≠ (nb061_alpha_dummy_021) := by
  simpa only [nb061_alpha_dummy_019, nb061_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb061_distinct_025 : (nb061_alpha_dummy_020) ≠ (nb061_alpha_dummy_021) := by
  simpa only [nb061_alpha_dummy_020, nb061_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb061_fresh_026 (r : Var) (a : Var) :
    (nb061_alpha_dummy_022 r a) ∉
      (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 0

theorem nb061_fresh_027 (r : Var) (a : Var) :
    (nb061_alpha_dummy_023 r a) ∉
      (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 1

theorem nb061_fresh_028 (r : Var) (a : Var) :
    (nb061_alpha_dummy_024 r a) ∉
      (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 2

theorem nb061_distinct_029 (r : Var) (a : Var) :
    (nb061_alpha_dummy_022 r a) ≠ (nb061_alpha_dummy_023 r a) := by
  simpa only [nb061_alpha_dummy_022, nb061_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb061_distinct_030 (r : Var) (a : Var) :
    (nb061_alpha_dummy_022 r a) ≠ (nb061_alpha_dummy_024 r a) := by
  simpa only [nb061_alpha_dummy_022, nb061_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb061_distinct_031 (r : Var) (a : Var) :
    (nb061_alpha_dummy_023 r a) ≠ (nb061_alpha_dummy_024 r a) := by
  simpa only [nb061_alpha_dummy_023, nb061_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb061_fresh_032 :
    (nb061_alpha_dummy_031) ∉
      (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_020))).fv) :=
  by
  simpa only [nb061_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_020))).fv)
      0

theorem nb061_fresh_033 :
    (nb061_alpha_dummy_027) ∉
      (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) :=
  by
  simpa only [nb061_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv)
      0

theorem nb061_fresh_034 :
    (nb061_alpha_dummy_033) ∉
      (((Class.cv (nb061_alpha_dummy_021))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) :=
  by
  simpa only [nb061_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_021))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv)
      0

theorem nb061_fresh_035 (r : Var) (a : Var) :
    (nb061_alpha_dummy_032 r a) ∉
      (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪
        ((Class.cv (nb061_alpha_dummy_023 r a))).fv) :=
  by
  simpa only [nb061_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪
        ((Class.cv (nb061_alpha_dummy_023 r a))).fv)
      0

theorem nb061_fresh_036 (r : Var) (a : Var) :
    (nb061_alpha_dummy_028 r a) ∉
      (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪
        ((Class.cv (nb061_alpha_dummy_024 r a))).fv) :=
  by
  simpa only [nb061_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪
        ((Class.cv (nb061_alpha_dummy_024 r a))).fv)
      0

theorem nb061_fresh_037 (r : Var) (a : Var) :
    (nb061_alpha_dummy_034 r a) ∉
      (((Class.cv (nb061_alpha_dummy_024 r a))).fv ∪
        ((Class.cv (nb061_alpha_dummy_024 r a))).fv) :=
  by
  simpa only [nb061_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_024 r a))).fv ∪
        ((Class.cv (nb061_alpha_dummy_024 r a))).fv)
      0

theorem nb061_fresh_038 :
    (nb061_alpha_dummy_049) ∉ (((Class.cv (nb061_alpha_dummy_042))).fv) := by
  simpa only [nb061_alpha_dummy_049] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_042))).fv) 0

theorem nb061_fresh_039 :
    (nb061_alpha_dummy_050) ∉ (((Class.cv (nb061_alpha_dummy_042))).fv) := by
  simpa only [nb061_alpha_dummy_050] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_042))).fv) 1

theorem nb061_distinct_040 : (nb061_alpha_dummy_049) ≠ (nb061_alpha_dummy_050) := by
  simpa only [nb061_alpha_dummy_049, nb061_alpha_dummy_050] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_042))).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_041 (x : Var) :
    (nb061_alpha_dummy_051 x) ∉ (((Class.cv (nb061_alpha_dummy_044 x))).fv) := by
  simpa only [nb061_alpha_dummy_051] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_044 x))).fv) 0

theorem nb061_fresh_042 (x : Var) :
    (nb061_alpha_dummy_052 x) ∉ (((Class.cv (nb061_alpha_dummy_044 x))).fv) := by
  simpa only [nb061_alpha_dummy_052] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_044 x))).fv) 1

theorem nb061_distinct_043 (x : Var) :
    (nb061_alpha_dummy_051 x) ≠ (nb061_alpha_dummy_052 x) := by
  simpa only [nb061_alpha_dummy_051, nb061_alpha_dummy_052] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_044 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb061_fresh_044 :
    (nb061_alpha_dummy_055) ∉
      (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_055] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 0

theorem nb061_fresh_045 :
    (nb061_alpha_dummy_056) ∉
      (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_056] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 1

theorem nb061_fresh_046 :
    (nb061_alpha_dummy_057) ∉
      (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_057] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 2

theorem nb061_distinct_047 : (nb061_alpha_dummy_055) ≠ (nb061_alpha_dummy_056) := by
  simpa only [nb061_alpha_dummy_055, nb061_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb061_distinct_048 : (nb061_alpha_dummy_055) ≠ (nb061_alpha_dummy_057) := by
  simpa only [nb061_alpha_dummy_055, nb061_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb061_distinct_049 : (nb061_alpha_dummy_056) ≠ (nb061_alpha_dummy_057) := by
  simpa only [nb061_alpha_dummy_056, nb061_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb061_fresh_050 (x : Var) :
    (nb061_alpha_dummy_058 x) ∉
      (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb061_fresh_051 (x : Var) :
    (nb061_alpha_dummy_059 x) ∉
      (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb061_fresh_052 (x : Var) :
    (nb061_alpha_dummy_060 x) ∉
      (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb061_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb061_distinct_053 (x : Var) :
    (nb061_alpha_dummy_058 x) ≠ (nb061_alpha_dummy_059 x) := by
  simpa only [nb061_alpha_dummy_058, nb061_alpha_dummy_059] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb061_distinct_054 (x : Var) :
    (nb061_alpha_dummy_058 x) ≠ (nb061_alpha_dummy_060 x) := by
  simpa only [nb061_alpha_dummy_058, nb061_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb061_distinct_055 (x : Var) :
    (nb061_alpha_dummy_059 x) ≠ (nb061_alpha_dummy_060 x) := by
  simpa only [nb061_alpha_dummy_059, nb061_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb061_fresh_056 :
    (nb061_alpha_dummy_067) ∉
      (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_056))).fv) :=
  by
  simpa only [nb061_alpha_dummy_067] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_056))).fv)
      0

theorem nb061_fresh_057 :
    (nb061_alpha_dummy_063) ∉
      (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) :=
  by
  simpa only [nb061_alpha_dummy_063] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv)
      0

theorem nb061_fresh_058 :
    (nb061_alpha_dummy_069) ∉
      (((Class.cv (nb061_alpha_dummy_057))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) :=
  by
  simpa only [nb061_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_057))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv)
      0

theorem nb061_fresh_059 (x : Var) :
    (nb061_alpha_dummy_068 x) ∉
      (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_059 x))).fv) :=
  by
  simpa only [nb061_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_059 x))).fv)
      0

theorem nb061_fresh_060 (x : Var) :
    (nb061_alpha_dummy_064 x) ∉
      (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv) :=
  by
  simpa only [nb061_alpha_dummy_064] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv)
      0

theorem nb061_fresh_061 (x : Var) :
    (nb061_alpha_dummy_070 x) ∉
      (((Class.cv (nb061_alpha_dummy_060 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv) :=
  by
  simpa only [nb061_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb061_alpha_dummy_060 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv)
      0

theorem nb061_fresh_062 (r : Var) (a : Var) :
    (nb061_alpha_dummy_007 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb061_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb061_fresh_063 (r : Var) (a : Var) :
    (nb061_alpha_dummy_008 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb061_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb061_distinct_064 (r : Var) (a : Var) :
    (nb061_alpha_dummy_007 r a) ≠ (nb061_alpha_dummy_008 r a) := by
  simpa only [nb061_alpha_dummy_007, nb061_alpha_dummy_008] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_065 (x : Var) :
    (nb061_alpha_dummy_043 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb061_alpha_dummy_043] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 0

theorem nb061_fresh_066 (x : Var) :
    (nb061_alpha_dummy_044 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb061_alpha_dummy_044] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 1

theorem nb061_distinct_067 (x : Var) :
    (nb061_alpha_dummy_043 x) ≠ (nb061_alpha_dummy_044 x) := by
  simpa only [nb061_alpha_dummy_043, nb061_alpha_dummy_044] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_068 :
    (nb061_alpha_dummy_017) ∉
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_013))).fv) :=
  by
  simpa only [nb061_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_013))).fv)
      0

theorem nb061_fresh_069 (r : Var) (a : Var) :
    (nb061_alpha_dummy_018 r a) ∉
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_015 r a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_015 r a)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_015 r a))).fv) :=
  by
  simpa only [nb061_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_015 r a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_015 r a)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_015 r a))).fv)
      0

theorem nb061_fresh_070 :
    (nb061_alpha_dummy_053) ∉
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_049)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_049)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_049))).fv) :=
  by
  simpa only [nb061_alpha_dummy_053] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_049)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_049)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_049))).fv)
      0

theorem nb061_fresh_071 (x : Var) :
    (nb061_alpha_dummy_054 x) ∉
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_051 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_051 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_051 x))).fv) :=
  by
  simpa only [nb061_alpha_dummy_054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_051 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_051 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_051 x))).fv)
      0

theorem nb061_fresh_072 :
    (nb061_alpha_dummy_009) ∉
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_005)
              (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_005)
              (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_005)
              (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_005)
              (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C061C001Part002`. -/


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

theorem nb061_fresh_073 (r : Var) (a : Var) :
    (nb061_alpha_dummy_010 r a) ∉
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_007 r a)
              (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_007 r a)
              (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_007 r a)
              (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_007 r a)
              (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb061_fresh_074 :
    (nb061_alpha_dummy_045) ∉
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_041)
              (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_042)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_041)
              (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_045] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_041)
              (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_042)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_041)
              (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb061_fresh_075 (x : Var) :
    (nb061_alpha_dummy_046 x) ∉
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_043 x)
              (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_043 x)
              (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_046] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_043 x)
              (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_043 x)
              (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb061_fresh_076 :
    (nb061_alpha_dummy_029) ∉
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_021)))).fv)
      0

theorem nb061_fresh_077 (r : Var) (a : Var) :
    (nb061_alpha_dummy_030 r a) ∉
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_023 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_024 r a)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_023 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_024 r a)))).fv)
      0

theorem nb061_fresh_078 :
    (nb061_alpha_dummy_065) ∉
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_056)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_057)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_065] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_056)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_057)))).fv)
      0

theorem nb061_fresh_079 (x : Var) :
    (nb061_alpha_dummy_066 x) ∉
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_059 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_060 x)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_066] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_059 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_060 x)))).fv)
      0

theorem nb061_fresh_080 :
    (nb061_alpha_dummy_037) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb061_fresh_081 (r : Var) (a : Var) :
    (nb061_alpha_dummy_038 r a) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb061_fresh_082 :
    (nb061_alpha_dummy_073) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_042))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_073] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_042))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb061_fresh_083 (x : Var) :
    (nb061_alpha_dummy_074 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_074] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb061_fresh_084 :
    (nb061_alpha_dummy_025) ∉
      (((syn_cnin (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_020))
            (Class.cv (nb061_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021)))).fv)
      0

theorem nb061_fresh_085 (r : Var) (a : Var) :
    (nb061_alpha_dummy_026 r a) ∉
      (((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a))
            (Class.cv (nb061_alpha_dummy_024 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a))
            (Class.cv (nb061_alpha_dummy_024 r a)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a))
            (Class.cv (nb061_alpha_dummy_024 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a))
            (Class.cv (nb061_alpha_dummy_024 r a)))).fv)
      0

theorem nb061_fresh_086 :
    (nb061_alpha_dummy_061) ∉
      (((syn_cnin (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_056))
            (Class.cv (nb061_alpha_dummy_057)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_061] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057)))).fv)
      0

theorem nb061_fresh_087 (x : Var) :
    (nb061_alpha_dummy_062 x) ∉
      (((syn_cnin (Class.cv (nb061_alpha_dummy_059 x))
            (Class.cv (nb061_alpha_dummy_060 x)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_059 x))
            (Class.cv (nb061_alpha_dummy_060 x)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_062] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb061_alpha_dummy_059 x))
            (Class.cv (nb061_alpha_dummy_060 x)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_059 x))
            (Class.cv (nb061_alpha_dummy_060 x)))).fv)
      0

theorem nb061_fresh_088 :
    (nb061_alpha_dummy_039) ∉
      (((syn_cphi (Class.cv (nb061_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_006)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb061_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_006)))).fv)
      0

theorem nb061_fresh_089 (r : Var) (a : Var) :
    (nb061_alpha_dummy_040 r a) ∉
      (((syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))).fv)
      0

theorem nb061_fresh_090 :
    (nb061_alpha_dummy_075) ∉
      (((syn_cphi (Class.cv (nb061_alpha_dummy_042)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_042)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_075] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb061_alpha_dummy_042)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_042)))).fv)
      0

theorem nb061_fresh_091 (x : Var) :
    (nb061_alpha_dummy_076 x) ∉
      (((syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_076] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))).fv)
      0

theorem nb061_fresh_092 :
    (nb061_alpha_dummy_003) ∉
      (({(nb061_alpha_dummy_001)} : Finset Var) ∪ ({(nb061_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb061_alpha_dummy_002) (Class.cv (nb061_alpha_dummy_000))
            (syn_wbr (Class.cv (nb061_alpha_dummy_002)) (Class.cv (nb061_alpha_dummy_001))
              (Class.cv (nb061_alpha_dummy_002))))).fv) :=
  by
  simpa only [nb061_alpha_dummy_003] using
    freshVar_not_mem
      (({(nb061_alpha_dummy_001)} : Finset Var) ∪ ({(nb061_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb061_alpha_dummy_002) (Class.cv (nb061_alpha_dummy_000))
            (syn_wbr (Class.cv (nb061_alpha_dummy_002)) (Class.cv (nb061_alpha_dummy_001))
              (Class.cv (nb061_alpha_dummy_002))))).fv)
      0

theorem nb061_fresh_093 (x : Var) (r : Var) (a : Var) :
    (nb061_alpha_dummy_004 x r a) ∉
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
            (syn_wbr (Class.cv x) (Class.cv r) (Class.cv x)))).fv) :=
  by
  simpa only [nb061_alpha_dummy_004] using
    freshVar_not_mem
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪
        ((syn_wral x (Class.cv a) (syn_wbr (Class.cv x) (Class.cv r) (Class.cv x)))).fv)
      0

theorem nb061_fresh_094 : (nb061_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb061_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb061_fresh_095 : (nb061_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb061_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb061_fresh_096 : (nb061_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb061_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb061_distinct_097 : (nb061_alpha_dummy_000) ≠ (nb061_alpha_dummy_001) := by
  simpa only [nb061_alpha_dummy_000, nb061_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb061_distinct_098 : (nb061_alpha_dummy_000) ≠ (nb061_alpha_dummy_002) := by
  simpa only [nb061_alpha_dummy_000, nb061_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb061_distinct_099 : (nb061_alpha_dummy_001) ≠ (nb061_alpha_dummy_002) := by
  simpa only [nb061_alpha_dummy_001, nb061_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb061_support_mem_0000 :
    (nb061_alpha_dummy_001) ∈
      (({(nb061_alpha_dummy_001)} : Finset Var) ∪ ({(nb061_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb061_alpha_dummy_002) (Class.cv (nb061_alpha_dummy_000))
            (syn_wbr (Class.cv (nb061_alpha_dummy_002)) (Class.cv (nb061_alpha_dummy_001))
              (Class.cv (nb061_alpha_dummy_002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0001 (x : Var) (r : Var) (a : Var) :
    r ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
            (syn_wbr (Class.cv x) (Class.cv r) (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0002 :
    (nb061_alpha_dummy_000) ∈
      (({(nb061_alpha_dummy_001)} : Finset Var) ∪ ({(nb061_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb061_alpha_dummy_002) (Class.cv (nb061_alpha_dummy_000))
            (syn_wbr (Class.cv (nb061_alpha_dummy_002)) (Class.cv (nb061_alpha_dummy_001))
              (Class.cv (nb061_alpha_dummy_002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0003 (x : Var) (r : Var) (a : Var) :
    a ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
            (syn_wbr (Class.cv x) (Class.cv r) (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0004 :
    (nb061_alpha_dummy_001) ∈
      (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0005 :
    (nb061_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_005)
              (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_005)
              (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0006 (r : Var) (a : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0007 (r : Var) (a : Var) :
    r ∈
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_007 r a)
              (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_007 r a)
              (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0008 :
    (nb061_alpha_dummy_001) ∈
      (((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0009 (r : Var) (a : Var) :
    r ∈
      (((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0010 :
    (nb061_alpha_dummy_006) ∈ (((Class.cv (nb061_alpha_dummy_006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0011 (r : Var) (a : Var) :
    (nb061_alpha_dummy_008 r a) ∈ (((Class.cv (nb061_alpha_dummy_008 r a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0012 :
    (nb061_alpha_dummy_013) ∈
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_013))).fv) :=
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

theorem nb061_support_mem_0013 (r : Var) (a : Var) :
    (nb061_alpha_dummy_015 r a) ∈
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_015 r a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_015 r a)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_015 r a))).fv) :=
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

theorem nb061_support_mem_0014 :
    (nb061_alpha_dummy_013) ∈
      (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0015 (r : Var) (a : Var) :
    (nb061_alpha_dummy_015 r a) ∈
      (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0016 :
    (nb061_alpha_dummy_020) ∈
      (((syn_cnin (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_020))
            (Class.cv (nb061_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0017 (r : Var) (a : Var) :
    (nb061_alpha_dummy_023 r a) ∈
      (((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a))
            (Class.cv (nb061_alpha_dummy_024 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a))
            (Class.cv (nb061_alpha_dummy_024 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0018 :
    (nb061_alpha_dummy_020) ∈
      (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0019 (r : Var) (a : Var) :
    (nb061_alpha_dummy_023 r a) ∈
      (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪
        ((Class.cv (nb061_alpha_dummy_024 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0020 :
    (nb061_alpha_dummy_021) ∈
      (((syn_cnin (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_020))
            (Class.cv (nb061_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0021 (r : Var) (a : Var) :
    (nb061_alpha_dummy_024 r a) ∈
      (((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a))
            (Class.cv (nb061_alpha_dummy_024 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a))
            (Class.cv (nb061_alpha_dummy_024 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0022 :
    (nb061_alpha_dummy_021) ∈
      (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0023 (r : Var) (a : Var) :
    (nb061_alpha_dummy_024 r a) ∈
      (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪
        ((Class.cv (nb061_alpha_dummy_024 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0024 :
    (nb061_alpha_dummy_020) ∈
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0025 (r : Var) (a : Var) :
    (nb061_alpha_dummy_023 r a) ∈
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_023 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_024 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0026 :
    (nb061_alpha_dummy_020) ∈
      (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0027 (r : Var) (a : Var) :
    (nb061_alpha_dummy_023 r a) ∈
      (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪
        ((Class.cv (nb061_alpha_dummy_023 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0028 :
    (nb061_alpha_dummy_021) ∈
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0029 (r : Var) (a : Var) :
    (nb061_alpha_dummy_024 r a) ∈
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_023 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_024 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0030 :
    (nb061_alpha_dummy_021) ∈
      (((Class.cv (nb061_alpha_dummy_021))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0031 (r : Var) (a : Var) :
    (nb061_alpha_dummy_024 r a) ∈
      (((Class.cv (nb061_alpha_dummy_024 r a))).fv ∪
        ((Class.cv (nb061_alpha_dummy_024 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0032 :
    (nb061_alpha_dummy_000) ∈
      (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0033 :
    (nb061_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_005)
              (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_005)
              (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0034 (r : Var) (a : Var) :
    a ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0035 (r : Var) (a : Var) :
    a ∈
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_007 r a)
              (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_007 r a)
              (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0036 :
    (nb061_alpha_dummy_000) ∈
      (((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_005)
            (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0037 (r : Var) (a : Var) :
    a ∈
      (((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_007 r a)
            (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0038 :
    (nb061_alpha_dummy_006) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0039 (r : Var) (a : Var) :
    (nb061_alpha_dummy_008 r a) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0040 :
    (nb061_alpha_dummy_006) ∈
      (((syn_cphi (Class.cv (nb061_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0041 (r : Var) (a : Var) :
    (nb061_alpha_dummy_008 r a) ∈
      (((syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0042 :
    (nb061_alpha_dummy_002) ∈
      (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0043 :
    (nb061_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_041)
              (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_042)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_041)
              (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0044 (x : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0045 (x : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb061_alpha_dummy_043 x)
              (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                  (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb061_alpha_dummy_043 x)
              (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                  (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0046 :
    (nb061_alpha_dummy_002) ∈
      (((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0047 (x : Var) :
    x ∈
      (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv ∪
        ((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0048 :
    (nb061_alpha_dummy_042) ∈ (((Class.cv (nb061_alpha_dummy_042))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0049 (x : Var) :
    (nb061_alpha_dummy_044 x) ∈ (((Class.cv (nb061_alpha_dummy_044 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0050 :
    (nb061_alpha_dummy_049) ∈
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_049)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_049)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_049))).fv) :=
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

theorem nb061_support_mem_0051 (x : Var) :
    (nb061_alpha_dummy_051 x) ∈
      (((Wff.classMem (Class.cv (nb061_alpha_dummy_051 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb061_alpha_dummy_051 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb061_alpha_dummy_051 x))).fv) :=
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

theorem nb061_support_mem_0052 :
    (nb061_alpha_dummy_049) ∈
      (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0053 (x : Var) :
    (nb061_alpha_dummy_051 x) ∈
      (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0054 :
    (nb061_alpha_dummy_056) ∈
      (((syn_cnin (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_056))
            (Class.cv (nb061_alpha_dummy_057)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0055 (x : Var) :
    (nb061_alpha_dummy_059 x) ∈
      (((syn_cnin (Class.cv (nb061_alpha_dummy_059 x))
            (Class.cv (nb061_alpha_dummy_060 x)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_059 x))
            (Class.cv (nb061_alpha_dummy_060 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0056 :
    (nb061_alpha_dummy_056) ∈
      (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0057 (x : Var) :
    (nb061_alpha_dummy_059 x) ∈
      (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0058 :
    (nb061_alpha_dummy_057) ∈
      (((syn_cnin (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_056))
            (Class.cv (nb061_alpha_dummy_057)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0059 (x : Var) :
    (nb061_alpha_dummy_060 x) ∈
      (((syn_cnin (Class.cv (nb061_alpha_dummy_059 x))
            (Class.cv (nb061_alpha_dummy_060 x)))).fv ∪
        ((syn_cnin (Class.cv (nb061_alpha_dummy_059 x))
            (Class.cv (nb061_alpha_dummy_060 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0060 :
    (nb061_alpha_dummy_057) ∈
      (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0061 (x : Var) :
    (nb061_alpha_dummy_060 x) ∈
      (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0062 :
    (nb061_alpha_dummy_056) ∈
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_056)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_057)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0063 (x : Var) :
    (nb061_alpha_dummy_059 x) ∈
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_059 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_060 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0064 :
    (nb061_alpha_dummy_056) ∈
      (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_056))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0065 (x : Var) :
    (nb061_alpha_dummy_059 x) ∈
      (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_059 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0066 :
    (nb061_alpha_dummy_057) ∈
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_056)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_057)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0067 (x : Var) :
    (nb061_alpha_dummy_060 x) ∈
      (((syn_ccompl (Class.cv (nb061_alpha_dummy_059 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb061_alpha_dummy_060 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0068 :
    (nb061_alpha_dummy_057) ∈
      (((Class.cv (nb061_alpha_dummy_057))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0069 (x : Var) :
    (nb061_alpha_dummy_060 x) ∈
      (((Class.cv (nb061_alpha_dummy_060 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0070 :
    (nb061_alpha_dummy_002) ∈
      (((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_041)
            (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0071 (x : Var) :
    x ∈
      (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_043 x)
            (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
                (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0072 :
    (nb061_alpha_dummy_042) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_042))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0073 (x : Var) :
    (nb061_alpha_dummy_044 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0074 :
    (nb061_alpha_dummy_042) ∈
      (((syn_cphi (Class.cv (nb061_alpha_dummy_042)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_042)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0075 (x : Var) :
    (nb061_alpha_dummy_044 x) ∈
      (((syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))).fv ∪
        ((syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
