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

/-! Certificates from `NAR4C062C001Part001`. -/


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
noncomputable def nb062_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb062_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb062_alpha_dummy_002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

@[expose]
noncomputable def nb062_alpha_dummy_003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

@[expose]
noncomputable def nb062_alpha_dummy_004 : Var :=
  (freshVar
    (({(nb062_alpha_dummy_001)} : Finset Var) ∪ ({(nb062_alpha_dummy_000)} : Finset Var) ∪
      ((syn_wral (nb062_alpha_dummy_002) (Class.cv (nb062_alpha_dummy_000))
          (syn_wral (nb062_alpha_dummy_003) (Class.cv (nb062_alpha_dummy_000)) (Wff.imp (syn_wa
                (syn_wbr (Class.cv (nb062_alpha_dummy_002))
                  (Class.cv (nb062_alpha_dummy_001)) (Class.cv (nb062_alpha_dummy_003)))
                (syn_wbr (Class.cv (nb062_alpha_dummy_003))
                  (Class.cv (nb062_alpha_dummy_001)) (Class.cv (nb062_alpha_dummy_002))))
              (Wff.objEq (nb062_alpha_dummy_002) (nb062_alpha_dummy_003)))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_005 (x : Var) (y : Var) (r : Var) (a : Var) : Var :=
  (freshVar (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
          (syn_wral y (Class.cv a) (Wff.imp
              (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y))
                (syn_wbr (Class.cv y) (Class.cv r) (Class.cv x))) (Wff.objEq x y))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_006 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_001))).fv ∪ ((Class.cv (nb062_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_007 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_001))).fv ∪ ((Class.cv (nb062_alpha_dummy_000))).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_008 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_009 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_010 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cphi (Class.cv (nb062_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_011 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_012 : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_006)
          (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
              (syn_cphi (Class.cv (nb062_alpha_dummy_007))))))).fv ∪
      ((Class.cab (nb062_alpha_dummy_006)
          (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
              (syn_cphi (Class.cv (nb062_alpha_dummy_007))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_013 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_008 r a)
          (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
              (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))))).fv ∪
      ((Class.cab (nb062_alpha_dummy_008 r a) (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
              (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_014 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_007))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_015 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_007))).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_016 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_009 r a))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_017 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_009 r a))).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_018 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062_alpha_dummy_014)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb062_alpha_dummy_014)) (syn_c1c))).fv ∪
      ((Class.cv (nb062_alpha_dummy_014))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_019 (r : Var) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062_alpha_dummy_016 r a)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb062_alpha_dummy_016 r a)) (syn_c1c))).fv ∪
      ((Class.cv (nb062_alpha_dummy_016 r a))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_020 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_021 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_022 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb062_alpha_dummy_023 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_024 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_025 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb062_alpha_dummy_026 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb062_alpha_dummy_021))
          (Class.cv (nb062_alpha_dummy_022)))).fv ∪
      ((syn_cnin (Class.cv (nb062_alpha_dummy_021)) (Class.cv (nb062_alpha_dummy_022)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_027 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb062_alpha_dummy_024 r a))
          (Class.cv (nb062_alpha_dummy_025 r a)))).fv ∪
      ((syn_cnin (Class.cv (nb062_alpha_dummy_024 r a))
          (Class.cv (nb062_alpha_dummy_025 r a)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_028 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_021))).fv ∪ ((Class.cv (nb062_alpha_dummy_022))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_029 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_024 r a))).fv ∪
      ((Class.cv (nb062_alpha_dummy_025 r a))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_030 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb062_alpha_dummy_021)))).fv ∪
      ((syn_ccompl (Class.cv (nb062_alpha_dummy_022)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_031 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb062_alpha_dummy_024 r a)))).fv ∪
      ((syn_ccompl (Class.cv (nb062_alpha_dummy_025 r a)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_032 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_021))).fv ∪ ((Class.cv (nb062_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_033 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_024 r a))).fv ∪
      ((Class.cv (nb062_alpha_dummy_024 r a))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_034 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_022))).fv ∪ ((Class.cv (nb062_alpha_dummy_022))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_035 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_025 r a))).fv ∪
      ((Class.cv (nb062_alpha_dummy_025 r a))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_036 : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_006)
          (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_006)
          (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_037 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_008 r a)
          (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_008 r a)
          (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_038 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_007))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_039 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_040 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb062_alpha_dummy_007)))).fv ∪
      ((syn_cphi (Class.cv (nb062_alpha_dummy_007)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_041 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))).fv ∪
      ((syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_042 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_002))).fv ∪ ((Class.cv (nb062_alpha_dummy_003))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_043 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_002))).fv ∪ ((Class.cv (nb062_alpha_dummy_003))).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_044 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_046 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cphi (Class.cv (nb062_alpha_dummy_043)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_047 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_048 : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_042)
          (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
              (syn_cphi (Class.cv (nb062_alpha_dummy_043))))))).fv ∪
      ((Class.cab (nb062_alpha_dummy_042)
          (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
              (syn_cphi (Class.cv (nb062_alpha_dummy_043))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_049 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_044 x y)
          (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
              (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))))).fv ∪
      ((Class.cab (nb062_alpha_dummy_044 x y) (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
              (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_050 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_043))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_051 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_043))).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_045 x y))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_045 x y))).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062_alpha_dummy_050)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb062_alpha_dummy_050)) (syn_c1c))).fv ∪
      ((Class.cv (nb062_alpha_dummy_050))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb062_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb062_alpha_dummy_052 x y))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_056 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_057 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_058 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb062_alpha_dummy_059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb062_alpha_dummy_062 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb062_alpha_dummy_057))
          (Class.cv (nb062_alpha_dummy_058)))).fv ∪
      ((syn_cnin (Class.cv (nb062_alpha_dummy_057)) (Class.cv (nb062_alpha_dummy_058)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_063 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb062_alpha_dummy_060 x y))
          (Class.cv (nb062_alpha_dummy_061 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb062_alpha_dummy_060 x y))
          (Class.cv (nb062_alpha_dummy_061 x y)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_064 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_057))).fv ∪ ((Class.cv (nb062_alpha_dummy_058))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_060 x y))).fv ∪
      ((Class.cv (nb062_alpha_dummy_061 x y))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_066 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb062_alpha_dummy_057)))).fv ∪
      ((syn_ccompl (Class.cv (nb062_alpha_dummy_058)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_067 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb062_alpha_dummy_060 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb062_alpha_dummy_061 x y)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_068 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_057))).fv ∪ ((Class.cv (nb062_alpha_dummy_057))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_060 x y))).fv ∪
      ((Class.cv (nb062_alpha_dummy_060 x y))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_070 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_058))).fv ∪ ((Class.cv (nb062_alpha_dummy_058))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_061 x y))).fv ∪
      ((Class.cv (nb062_alpha_dummy_061 x y))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_072 : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_042)
          (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_042)
          (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_044 x y)
          (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_044 x y)
          (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_074 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_043))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_075 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_076 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb062_alpha_dummy_043)))).fv ∪
      ((syn_cphi (Class.cv (nb062_alpha_dummy_043)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_077 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_078 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_003))).fv ∪ ((Class.cv (nb062_alpha_dummy_002))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_079 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_003))).fv ∪ ((Class.cv (nb062_alpha_dummy_002))).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_080 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_081 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_082 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cphi (Class.cv (nb062_alpha_dummy_079)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_083 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_084 : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_078)
          (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
              (syn_cphi (Class.cv (nb062_alpha_dummy_079))))))).fv ∪
      ((Class.cab (nb062_alpha_dummy_078)
          (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
              (syn_cphi (Class.cv (nb062_alpha_dummy_079))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_085 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_080 x y)
          (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
              (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))))).fv ∪
      ((Class.cab (nb062_alpha_dummy_080 x y) (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
              (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_086 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_079))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_087 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_079))).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_088 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_081 x y))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_089 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_081 x y))).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_090 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062_alpha_dummy_086)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb062_alpha_dummy_086)) (syn_c1c))).fv ∪
      ((Class.cv (nb062_alpha_dummy_086))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_091 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062_alpha_dummy_088 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb062_alpha_dummy_088 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb062_alpha_dummy_088 x y))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_092 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_093 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_094 : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb062_alpha_dummy_095 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_096 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb062_alpha_dummy_097 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb062_alpha_dummy_098 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb062_alpha_dummy_093))
          (Class.cv (nb062_alpha_dummy_094)))).fv ∪
      ((syn_cnin (Class.cv (nb062_alpha_dummy_093)) (Class.cv (nb062_alpha_dummy_094)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_099 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb062_alpha_dummy_096 x y))
          (Class.cv (nb062_alpha_dummy_097 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb062_alpha_dummy_096 x y))
          (Class.cv (nb062_alpha_dummy_097 x y)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_100 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_093))).fv ∪ ((Class.cv (nb062_alpha_dummy_094))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_101 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_096 x y))).fv ∪
      ((Class.cv (nb062_alpha_dummy_097 x y))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_102 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb062_alpha_dummy_093)))).fv ∪
      ((syn_ccompl (Class.cv (nb062_alpha_dummy_094)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_103 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb062_alpha_dummy_096 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb062_alpha_dummy_097 x y)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_104 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_093))).fv ∪ ((Class.cv (nb062_alpha_dummy_093))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_105 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_096 x y))).fv ∪
      ((Class.cv (nb062_alpha_dummy_096 x y))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_106 : Var :=
  (freshVar
    (((Class.cv (nb062_alpha_dummy_094))).fv ∪ ((Class.cv (nb062_alpha_dummy_094))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_107 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062_alpha_dummy_097 x y))).fv ∪
      ((Class.cv (nb062_alpha_dummy_097 x y))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_108 : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_078)
          (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_078)
          (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_109 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb062_alpha_dummy_080 x y)
          (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_080 x y)
          (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
              (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_110 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_079))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_111 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_112 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb062_alpha_dummy_079)))).fv ∪
      ((syn_cphi (Class.cv (nb062_alpha_dummy_079)))).fv) 0)

@[expose]
noncomputable def nb062_alpha_dummy_113 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))).fv) 0)

theorem nb062_fresh_000 :
    (nb062_alpha_dummy_036) ∉
      (((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb062_fresh_001 :
    (nb062_alpha_dummy_012) ∉
      (((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cphi (Class.cv (nb062_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cphi (Class.cv (nb062_alpha_dummy_007))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cphi (Class.cv (nb062_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cphi (Class.cv (nb062_alpha_dummy_007))))))).fv)
      0

theorem nb062_fresh_002 (r : Var) (a : Var) :
    (nb062_alpha_dummy_037 r a) ∉
      (((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb062_fresh_003 (r : Var) (a : Var) :
    (nb062_alpha_dummy_013 r a) ∉
      (((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_013] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))))).fv)
      0

theorem nb062_fresh_004 :
    (nb062_alpha_dummy_048) ∉
      (((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cphi (Class.cv (nb062_alpha_dummy_043))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cphi (Class.cv (nb062_alpha_dummy_043))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_048] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cphi (Class.cv (nb062_alpha_dummy_043))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cphi (Class.cv (nb062_alpha_dummy_043))))))).fv)
      0

theorem nb062_fresh_005 :
    (nb062_alpha_dummy_072) ∉
      (((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb062_fresh_006 (x : Var) (y : Var) :
    (nb062_alpha_dummy_049 x y) ∉
      (((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_049] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))))).fv)
      0

theorem nb062_fresh_007 (x : Var) (y : Var) :
    (nb062_alpha_dummy_073 x y) ∉
      (((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb062_fresh_008 :
    (nb062_alpha_dummy_108) ∉
      (((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_108] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb062_fresh_009 :
    (nb062_alpha_dummy_084) ∉
      (((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cphi (Class.cv (nb062_alpha_dummy_079))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cphi (Class.cv (nb062_alpha_dummy_079))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_084] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cphi (Class.cv (nb062_alpha_dummy_079))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cphi (Class.cv (nb062_alpha_dummy_079))))))).fv)
      0

theorem nb062_fresh_010 (x : Var) (y : Var) :
    (nb062_alpha_dummy_109 x y) ∉
      (((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_109] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb062_fresh_011 (x : Var) (y : Var) :
    (nb062_alpha_dummy_085 x y) ∉
      (((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_085] using
    freshVar_not_mem
      (((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))))).fv)
      0

theorem nb062_fresh_012 :
    (nb062_alpha_dummy_006) ∉
      (((Class.cv (nb062_alpha_dummy_001))).fv ∪ ((Class.cv (nb062_alpha_dummy_000))).fv) :=
  by
  simpa only [nb062_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_001))).fv ∪ ((Class.cv (nb062_alpha_dummy_000))).fv)
      0

theorem nb062_fresh_013 :
    (nb062_alpha_dummy_007) ∉
      (((Class.cv (nb062_alpha_dummy_001))).fv ∪ ((Class.cv (nb062_alpha_dummy_000))).fv) :=
  by
  simpa only [nb062_alpha_dummy_007] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_001))).fv ∪ ((Class.cv (nb062_alpha_dummy_000))).fv)
      1

theorem nb062_distinct_014 : (nb062_alpha_dummy_006) ≠ (nb062_alpha_dummy_007) := by
  simpa only [nb062_alpha_dummy_006, nb062_alpha_dummy_007] using
    (freshVar_injective
      (((Class.cv (nb062_alpha_dummy_001))).fv ∪ ((Class.cv (nb062_alpha_dummy_000))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_fresh_015 :
    (nb062_alpha_dummy_042) ∉
      (((Class.cv (nb062_alpha_dummy_002))).fv ∪ ((Class.cv (nb062_alpha_dummy_003))).fv) :=
  by
  simpa only [nb062_alpha_dummy_042] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_002))).fv ∪ ((Class.cv (nb062_alpha_dummy_003))).fv)
      0

theorem nb062_fresh_016 :
    (nb062_alpha_dummy_043) ∉
      (((Class.cv (nb062_alpha_dummy_002))).fv ∪ ((Class.cv (nb062_alpha_dummy_003))).fv) :=
  by
  simpa only [nb062_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_002))).fv ∪ ((Class.cv (nb062_alpha_dummy_003))).fv)
      1

theorem nb062_distinct_017 : (nb062_alpha_dummy_042) ≠ (nb062_alpha_dummy_043) := by
  simpa only [nb062_alpha_dummy_042, nb062_alpha_dummy_043] using
    (freshVar_injective
      (((Class.cv (nb062_alpha_dummy_002))).fv ∪ ((Class.cv (nb062_alpha_dummy_003))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_fresh_018 :
    (nb062_alpha_dummy_078) ∉
      (((Class.cv (nb062_alpha_dummy_003))).fv ∪ ((Class.cv (nb062_alpha_dummy_002))).fv) :=
  by
  simpa only [nb062_alpha_dummy_078] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_003))).fv ∪ ((Class.cv (nb062_alpha_dummy_002))).fv)
      0

theorem nb062_fresh_019 :
    (nb062_alpha_dummy_079) ∉
      (((Class.cv (nb062_alpha_dummy_003))).fv ∪ ((Class.cv (nb062_alpha_dummy_002))).fv) :=
  by
  simpa only [nb062_alpha_dummy_079] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_003))).fv ∪ ((Class.cv (nb062_alpha_dummy_002))).fv)
      1

theorem nb062_distinct_020 : (nb062_alpha_dummy_078) ≠ (nb062_alpha_dummy_079) := by
  simpa only [nb062_alpha_dummy_078, nb062_alpha_dummy_079] using
    (freshVar_injective
      (((Class.cv (nb062_alpha_dummy_003))).fv ∪ ((Class.cv (nb062_alpha_dummy_002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_fresh_021 :
    (nb062_alpha_dummy_014) ∉ (((Class.cv (nb062_alpha_dummy_007))).fv) := by
  simpa only [nb062_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_007))).fv) 0

theorem nb062_fresh_022 :
    (nb062_alpha_dummy_015) ∉ (((Class.cv (nb062_alpha_dummy_007))).fv) := by
  simpa only [nb062_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_007))).fv) 1

theorem nb062_distinct_023 : (nb062_alpha_dummy_014) ≠ (nb062_alpha_dummy_015) := by
  simpa only [nb062_alpha_dummy_014, nb062_alpha_dummy_015] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_007))).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_024 (r : Var) (a : Var) :
    (nb062_alpha_dummy_016 r a) ∉ (((Class.cv (nb062_alpha_dummy_009 r a))).fv) := by
  simpa only [nb062_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_009 r a))).fv) 0

theorem nb062_fresh_025 (r : Var) (a : Var) :
    (nb062_alpha_dummy_017 r a) ∉ (((Class.cv (nb062_alpha_dummy_009 r a))).fv) := by
  simpa only [nb062_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_009 r a))).fv) 1

theorem nb062_distinct_026 (r : Var) (a : Var) :
    (nb062_alpha_dummy_016 r a) ≠ (nb062_alpha_dummy_017 r a) := by
  simpa only [nb062_alpha_dummy_016, nb062_alpha_dummy_017] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_009 r a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb062_fresh_027 :
    (nb062_alpha_dummy_020) ∉
      (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 0

theorem nb062_fresh_028 :
    (nb062_alpha_dummy_021) ∉
      (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 1

theorem nb062_fresh_029 :
    (nb062_alpha_dummy_022) ∉
      (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 2

theorem nb062_distinct_030 : (nb062_alpha_dummy_020) ≠ (nb062_alpha_dummy_021) := by
  simpa only [nb062_alpha_dummy_020, nb062_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb062_distinct_031 : (nb062_alpha_dummy_020) ≠ (nb062_alpha_dummy_022) := by
  simpa only [nb062_alpha_dummy_020, nb062_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb062_distinct_032 : (nb062_alpha_dummy_021) ≠ (nb062_alpha_dummy_022) := by
  simpa only [nb062_alpha_dummy_021, nb062_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb062_fresh_033 (r : Var) (a : Var) :
    (nb062_alpha_dummy_023 r a) ∉
      (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 0

theorem nb062_fresh_034 (r : Var) (a : Var) :
    (nb062_alpha_dummy_024 r a) ∉
      (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 1

theorem nb062_fresh_035 (r : Var) (a : Var) :
    (nb062_alpha_dummy_025 r a) ∉
      (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 2

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C062C001Part002`. -/


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

theorem nb062_distinct_036 (r : Var) (a : Var) :
    (nb062_alpha_dummy_023 r a) ≠ (nb062_alpha_dummy_024 r a) := by
  simpa only [nb062_alpha_dummy_023, nb062_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_distinct_037 (r : Var) (a : Var) :
    (nb062_alpha_dummy_023 r a) ≠ (nb062_alpha_dummy_025 r a) := by
  simpa only [nb062_alpha_dummy_023, nb062_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb062_distinct_038 (r : Var) (a : Var) :
    (nb062_alpha_dummy_024 r a) ≠ (nb062_alpha_dummy_025 r a) := by
  simpa only [nb062_alpha_dummy_024, nb062_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb062_fresh_039 :
    (nb062_alpha_dummy_032) ∉
      (((Class.cv (nb062_alpha_dummy_021))).fv ∪ ((Class.cv (nb062_alpha_dummy_021))).fv) :=
  by
  simpa only [nb062_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_021))).fv ∪ ((Class.cv (nb062_alpha_dummy_021))).fv)
      0

theorem nb062_fresh_040 :
    (nb062_alpha_dummy_028) ∉
      (((Class.cv (nb062_alpha_dummy_021))).fv ∪ ((Class.cv (nb062_alpha_dummy_022))).fv) :=
  by
  simpa only [nb062_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_021))).fv ∪ ((Class.cv (nb062_alpha_dummy_022))).fv)
      0

theorem nb062_fresh_041 :
    (nb062_alpha_dummy_034) ∉
      (((Class.cv (nb062_alpha_dummy_022))).fv ∪ ((Class.cv (nb062_alpha_dummy_022))).fv) :=
  by
  simpa only [nb062_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_022))).fv ∪ ((Class.cv (nb062_alpha_dummy_022))).fv)
      0

theorem nb062_fresh_042 (r : Var) (a : Var) :
    (nb062_alpha_dummy_033 r a) ∉
      (((Class.cv (nb062_alpha_dummy_024 r a))).fv ∪
        ((Class.cv (nb062_alpha_dummy_024 r a))).fv) :=
  by
  simpa only [nb062_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_024 r a))).fv ∪
        ((Class.cv (nb062_alpha_dummy_024 r a))).fv)
      0

theorem nb062_fresh_043 (r : Var) (a : Var) :
    (nb062_alpha_dummy_029 r a) ∉
      (((Class.cv (nb062_alpha_dummy_024 r a))).fv ∪
        ((Class.cv (nb062_alpha_dummy_025 r a))).fv) :=
  by
  simpa only [nb062_alpha_dummy_029] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_024 r a))).fv ∪
        ((Class.cv (nb062_alpha_dummy_025 r a))).fv)
      0

theorem nb062_fresh_044 (r : Var) (a : Var) :
    (nb062_alpha_dummy_035 r a) ∉
      (((Class.cv (nb062_alpha_dummy_025 r a))).fv ∪
        ((Class.cv (nb062_alpha_dummy_025 r a))).fv) :=
  by
  simpa only [nb062_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_025 r a))).fv ∪
        ((Class.cv (nb062_alpha_dummy_025 r a))).fv)
      0

theorem nb062_fresh_045 :
    (nb062_alpha_dummy_050) ∉ (((Class.cv (nb062_alpha_dummy_043))).fv) := by
  simpa only [nb062_alpha_dummy_050] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_043))).fv) 0

theorem nb062_fresh_046 :
    (nb062_alpha_dummy_051) ∉ (((Class.cv (nb062_alpha_dummy_043))).fv) := by
  simpa only [nb062_alpha_dummy_051] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_043))).fv) 1

theorem nb062_distinct_047 : (nb062_alpha_dummy_050) ≠ (nb062_alpha_dummy_051) := by
  simpa only [nb062_alpha_dummy_050, nb062_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_043))).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_048 (x : Var) (y : Var) :
    (nb062_alpha_dummy_052 x y) ∉ (((Class.cv (nb062_alpha_dummy_045 x y))).fv) := by
  simpa only [nb062_alpha_dummy_052] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_045 x y))).fv) 0

theorem nb062_fresh_049 (x : Var) (y : Var) :
    (nb062_alpha_dummy_053 x y) ∉ (((Class.cv (nb062_alpha_dummy_045 x y))).fv) := by
  simpa only [nb062_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_045 x y))).fv) 1

theorem nb062_distinct_050 (x : Var) (y : Var) :
    (nb062_alpha_dummy_052 x y) ≠ (nb062_alpha_dummy_053 x y) := by
  simpa only [nb062_alpha_dummy_052, nb062_alpha_dummy_053] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_045 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb062_fresh_051 :
    (nb062_alpha_dummy_056) ∉
      (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_056] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0

theorem nb062_fresh_052 :
    (nb062_alpha_dummy_057) ∉
      (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_057] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1

theorem nb062_fresh_053 :
    (nb062_alpha_dummy_058) ∉
      (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2

theorem nb062_distinct_054 : (nb062_alpha_dummy_056) ≠ (nb062_alpha_dummy_057) := by
  simpa only [nb062_alpha_dummy_056, nb062_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb062_distinct_055 : (nb062_alpha_dummy_056) ≠ (nb062_alpha_dummy_058) := by
  simpa only [nb062_alpha_dummy_056, nb062_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb062_distinct_056 : (nb062_alpha_dummy_057) ≠ (nb062_alpha_dummy_058) := by
  simpa only [nb062_alpha_dummy_057, nb062_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb062_fresh_057 (x : Var) (y : Var) :
    (nb062_alpha_dummy_059 x y) ∉
      (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb062_fresh_058 (x : Var) (y : Var) :
    (nb062_alpha_dummy_060 x y) ∉
      (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb062_fresh_059 (x : Var) (y : Var) :
    (nb062_alpha_dummy_061 x y) ∉
      (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb062_distinct_060 (x : Var) (y : Var) :
    (nb062_alpha_dummy_059 x y) ≠ (nb062_alpha_dummy_060 x y) := by
  simpa only [nb062_alpha_dummy_059, nb062_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_distinct_061 (x : Var) (y : Var) :
    (nb062_alpha_dummy_059 x y) ≠ (nb062_alpha_dummy_061 x y) := by
  simpa only [nb062_alpha_dummy_059, nb062_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb062_distinct_062 (x : Var) (y : Var) :
    (nb062_alpha_dummy_060 x y) ≠ (nb062_alpha_dummy_061 x y) := by
  simpa only [nb062_alpha_dummy_060, nb062_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb062_fresh_063 :
    (nb062_alpha_dummy_068) ∉
      (((Class.cv (nb062_alpha_dummy_057))).fv ∪ ((Class.cv (nb062_alpha_dummy_057))).fv) :=
  by
  simpa only [nb062_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_057))).fv ∪ ((Class.cv (nb062_alpha_dummy_057))).fv)
      0

theorem nb062_fresh_064 :
    (nb062_alpha_dummy_064) ∉
      (((Class.cv (nb062_alpha_dummy_057))).fv ∪ ((Class.cv (nb062_alpha_dummy_058))).fv) :=
  by
  simpa only [nb062_alpha_dummy_064] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_057))).fv ∪ ((Class.cv (nb062_alpha_dummy_058))).fv)
      0

theorem nb062_fresh_065 :
    (nb062_alpha_dummy_070) ∉
      (((Class.cv (nb062_alpha_dummy_058))).fv ∪ ((Class.cv (nb062_alpha_dummy_058))).fv) :=
  by
  simpa only [nb062_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_058))).fv ∪ ((Class.cv (nb062_alpha_dummy_058))).fv)
      0

theorem nb062_fresh_066 (x : Var) (y : Var) :
    (nb062_alpha_dummy_069 x y) ∉
      (((Class.cv (nb062_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_060 x y))).fv) :=
  by
  simpa only [nb062_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_060 x y))).fv)
      0

theorem nb062_fresh_067 (x : Var) (y : Var) :
    (nb062_alpha_dummy_065 x y) ∉
      (((Class.cv (nb062_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_061 x y))).fv) :=
  by
  simpa only [nb062_alpha_dummy_065] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_061 x y))).fv)
      0

theorem nb062_fresh_068 (x : Var) (y : Var) :
    (nb062_alpha_dummy_071 x y) ∉
      (((Class.cv (nb062_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_061 x y))).fv) :=
  by
  simpa only [nb062_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_061 x y))).fv)
      0

theorem nb062_fresh_069 :
    (nb062_alpha_dummy_086) ∉ (((Class.cv (nb062_alpha_dummy_079))).fv) := by
  simpa only [nb062_alpha_dummy_086] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_079))).fv) 0

theorem nb062_fresh_070 :
    (nb062_alpha_dummy_087) ∉ (((Class.cv (nb062_alpha_dummy_079))).fv) := by
  simpa only [nb062_alpha_dummy_087] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_079))).fv) 1

theorem nb062_distinct_071 : (nb062_alpha_dummy_086) ≠ (nb062_alpha_dummy_087) := by
  simpa only [nb062_alpha_dummy_086, nb062_alpha_dummy_087] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_079))).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_072 (x : Var) (y : Var) :
    (nb062_alpha_dummy_088 x y) ∉ (((Class.cv (nb062_alpha_dummy_081 x y))).fv) := by
  simpa only [nb062_alpha_dummy_088] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_081 x y))).fv) 0

theorem nb062_fresh_073 (x : Var) (y : Var) :
    (nb062_alpha_dummy_089 x y) ∉ (((Class.cv (nb062_alpha_dummy_081 x y))).fv) := by
  simpa only [nb062_alpha_dummy_089] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_081 x y))).fv) 1

theorem nb062_distinct_074 (x : Var) (y : Var) :
    (nb062_alpha_dummy_088 x y) ≠ (nb062_alpha_dummy_089 x y) := by
  simpa only [nb062_alpha_dummy_088, nb062_alpha_dummy_089] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_081 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb062_fresh_075 :
    (nb062_alpha_dummy_092) ∉
      (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_092] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 0

theorem nb062_fresh_076 :
    (nb062_alpha_dummy_093) ∉
      (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_093] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 1

theorem nb062_fresh_077 :
    (nb062_alpha_dummy_094) ∉
      (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_094] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 2

theorem nb062_distinct_078 : (nb062_alpha_dummy_092) ≠ (nb062_alpha_dummy_093) := by
  simpa only [nb062_alpha_dummy_092, nb062_alpha_dummy_093] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb062_distinct_079 : (nb062_alpha_dummy_092) ≠ (nb062_alpha_dummy_094) := by
  simpa only [nb062_alpha_dummy_092, nb062_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb062_distinct_080 : (nb062_alpha_dummy_093) ≠ (nb062_alpha_dummy_094) := by
  simpa only [nb062_alpha_dummy_093, nb062_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb062_fresh_081 (x : Var) (y : Var) :
    (nb062_alpha_dummy_095 x y) ∉
      (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_095] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb062_fresh_082 (x : Var) (y : Var) :
    (nb062_alpha_dummy_096 x y) ∉
      (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_096] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb062_fresh_083 (x : Var) (y : Var) :
    (nb062_alpha_dummy_097 x y) ∉
      (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb062_alpha_dummy_097] using
    freshVar_not_mem (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb062_distinct_084 (x : Var) (y : Var) :
    (nb062_alpha_dummy_095 x y) ≠ (nb062_alpha_dummy_096 x y) := by
  simpa only [nb062_alpha_dummy_095, nb062_alpha_dummy_096] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_distinct_085 (x : Var) (y : Var) :
    (nb062_alpha_dummy_095 x y) ≠ (nb062_alpha_dummy_097 x y) := by
  simpa only [nb062_alpha_dummy_095, nb062_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb062_distinct_086 (x : Var) (y : Var) :
    (nb062_alpha_dummy_096 x y) ≠ (nb062_alpha_dummy_097 x y) := by
  simpa only [nb062_alpha_dummy_096, nb062_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb062_fresh_087 :
    (nb062_alpha_dummy_104) ∉
      (((Class.cv (nb062_alpha_dummy_093))).fv ∪ ((Class.cv (nb062_alpha_dummy_093))).fv) :=
  by
  simpa only [nb062_alpha_dummy_104] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_093))).fv ∪ ((Class.cv (nb062_alpha_dummy_093))).fv)
      0

theorem nb062_fresh_088 :
    (nb062_alpha_dummy_100) ∉
      (((Class.cv (nb062_alpha_dummy_093))).fv ∪ ((Class.cv (nb062_alpha_dummy_094))).fv) :=
  by
  simpa only [nb062_alpha_dummy_100] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_093))).fv ∪ ((Class.cv (nb062_alpha_dummy_094))).fv)
      0

theorem nb062_fresh_089 :
    (nb062_alpha_dummy_106) ∉
      (((Class.cv (nb062_alpha_dummy_094))).fv ∪ ((Class.cv (nb062_alpha_dummy_094))).fv) :=
  by
  simpa only [nb062_alpha_dummy_106] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_094))).fv ∪ ((Class.cv (nb062_alpha_dummy_094))).fv)
      0

theorem nb062_fresh_090 (x : Var) (y : Var) :
    (nb062_alpha_dummy_105 x y) ∉
      (((Class.cv (nb062_alpha_dummy_096 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_096 x y))).fv) :=
  by
  simpa only [nb062_alpha_dummy_105] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_096 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_096 x y))).fv)
      0

theorem nb062_fresh_091 (x : Var) (y : Var) :
    (nb062_alpha_dummy_101 x y) ∉
      (((Class.cv (nb062_alpha_dummy_096 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_097 x y))).fv) :=
  by
  simpa only [nb062_alpha_dummy_101] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_096 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_097 x y))).fv)
      0

theorem nb062_fresh_092 (x : Var) (y : Var) :
    (nb062_alpha_dummy_107 x y) ∉
      (((Class.cv (nb062_alpha_dummy_097 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_097 x y))).fv) :=
  by
  simpa only [nb062_alpha_dummy_107] using
    freshVar_not_mem
      (((Class.cv (nb062_alpha_dummy_097 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_097 x y))).fv)
      0

theorem nb062_fresh_093 (r : Var) (a : Var) :
    (nb062_alpha_dummy_008 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb062_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb062_fresh_094 (r : Var) (a : Var) :
    (nb062_alpha_dummy_009 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb062_alpha_dummy_009] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb062_distinct_095 (r : Var) (a : Var) :
    (nb062_alpha_dummy_008 r a) ≠ (nb062_alpha_dummy_009 r a) := by
  simpa only [nb062_alpha_dummy_008, nb062_alpha_dummy_009] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_096 (x : Var) (y : Var) :
    (nb062_alpha_dummy_044 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb062_alpha_dummy_044] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb062_fresh_097 (x : Var) (y : Var) :
    (nb062_alpha_dummy_045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb062_alpha_dummy_045] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb062_distinct_098 (x : Var) (y : Var) :
    (nb062_alpha_dummy_044 x y) ≠ (nb062_alpha_dummy_045 x y) := by
  simpa only [nb062_alpha_dummy_044, nb062_alpha_dummy_045] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_099 (x : Var) (y : Var) :
    (nb062_alpha_dummy_080 x y) ∉ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb062_alpha_dummy_080] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0

theorem nb062_fresh_100 (x : Var) (y : Var) :
    (nb062_alpha_dummy_081 x y) ∉ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb062_alpha_dummy_081] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1

theorem nb062_distinct_101 (x : Var) (y : Var) :
    (nb062_alpha_dummy_080 x y) ≠ (nb062_alpha_dummy_081 x y) := by
  simpa only [nb062_alpha_dummy_080, nb062_alpha_dummy_081] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_102 :
    (nb062_alpha_dummy_018) ∉
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_014)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_014)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_014))).fv) :=
  by
  simpa only [nb062_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_014)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_014)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_014))).fv)
      0

theorem nb062_fresh_103 (r : Var) (a : Var) :
    (nb062_alpha_dummy_019 r a) ∉
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_016 r a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_016 r a)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_016 r a))).fv) :=
  by
  simpa only [nb062_alpha_dummy_019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_016 r a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_016 r a)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_016 r a))).fv)
      0

theorem nb062_fresh_104 :
    (nb062_alpha_dummy_054) ∉
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_050))).fv) :=
  by
  simpa only [nb062_alpha_dummy_054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_050))).fv)
      0

theorem nb062_fresh_105 (x : Var) (y : Var) :
    (nb062_alpha_dummy_055 x y) ∉
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_052 x y))).fv) :=
  by
  simpa only [nb062_alpha_dummy_055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_052 x y))).fv)
      0

theorem nb062_fresh_106 :
    (nb062_alpha_dummy_090) ∉
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_086)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_086)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_086))).fv) :=
  by
  simpa only [nb062_alpha_dummy_090] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_086)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_086)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_086))).fv)
      0

theorem nb062_fresh_107 (x : Var) (y : Var) :
    (nb062_alpha_dummy_091 x y) ∉
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_088 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_088 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_088 x y))).fv) :=
  by
  simpa only [nb062_alpha_dummy_091] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_088 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_088 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_088 x y))).fv)
      0

theorem nb062_fresh_108 :
    (nb062_alpha_dummy_010) ∉
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_006)
              (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_006)
              (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_006)
              (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_006)
              (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb062_fresh_109 (r : Var) (a : Var) :
    (nb062_alpha_dummy_011 r a) ∉
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_008 r a)
              (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_008 r a)
              (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_008 r a)
              (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_008 r a)
              (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb062_fresh_110 :
    (nb062_alpha_dummy_046) ∉
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_042)
              (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_043)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_042)
              (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_046] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_042)
              (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_043)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_042)
              (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb062_fresh_111 (x : Var) (y : Var) :
    (nb062_alpha_dummy_047 x y) ∉
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_044 x y)
              (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_044 x y)
              (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_044 x y)
              (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_044 x y)
              (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb062_fresh_112 :
    (nb062_alpha_dummy_082) ∉
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_078)
              (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_079)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_078)
              (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_082] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_078)
              (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_079)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_078)
              (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb062_fresh_113 (x : Var) (y : Var) :
    (nb062_alpha_dummy_083 x y) ∉
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_080 x y)
              (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_080 x y)
              (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_083] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_080 x y)
              (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_080 x y)
              (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb062_fresh_114 :
    (nb062_alpha_dummy_030) ∉
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_021)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_022)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_021)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_022)))).fv)
      0

theorem nb062_fresh_115 (r : Var) (a : Var) :
    (nb062_alpha_dummy_031 r a) ∉
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_024 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_025 r a)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_031] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_024 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_025 r a)))).fv)
      0

theorem nb062_fresh_116 :
    (nb062_alpha_dummy_066) ∉
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_058)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_066] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_058)))).fv)
      0

theorem nb062_fresh_117 (x : Var) (y : Var) :
    (nb062_alpha_dummy_067 x y) ∉
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_061 x y)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_067] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_061 x y)))).fv)
      0

theorem nb062_fresh_118 :
    (nb062_alpha_dummy_102) ∉
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_093)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_094)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_102] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_093)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_094)))).fv)
      0

theorem nb062_fresh_119 (x : Var) (y : Var) :
    (nb062_alpha_dummy_103 x y) ∉
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_096 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_097 x y)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_103] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_096 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_097 x y)))).fv)
      0

theorem nb062_fresh_120 :
    (nb062_alpha_dummy_038) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb062_fresh_121 (r : Var) (a : Var) :
    (nb062_alpha_dummy_039 r a) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb062_fresh_122 :
    (nb062_alpha_dummy_074) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_043))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_074] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_043))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb062_fresh_123 (x : Var) (y : Var) :
    (nb062_alpha_dummy_075 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_075] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb062_fresh_124 :
    (nb062_alpha_dummy_110) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_079))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_110] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_079))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb062_fresh_125 (x : Var) (y : Var) :
    (nb062_alpha_dummy_111 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_111] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb062_fresh_126 :
    (nb062_alpha_dummy_026) ∉
      (((syn_cnin (Class.cv (nb062_alpha_dummy_021)) (Class.cv (nb062_alpha_dummy_022)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_021))
            (Class.cv (nb062_alpha_dummy_022)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb062_alpha_dummy_021)) (Class.cv (nb062_alpha_dummy_022)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_021)) (Class.cv (nb062_alpha_dummy_022)))).fv)
      0

theorem nb062_fresh_127 (r : Var) (a : Var) :
    (nb062_alpha_dummy_027 r a) ∉
      (((syn_cnin (Class.cv (nb062_alpha_dummy_024 r a))
            (Class.cv (nb062_alpha_dummy_025 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_024 r a))
            (Class.cv (nb062_alpha_dummy_025 r a)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_027] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb062_alpha_dummy_024 r a))
            (Class.cv (nb062_alpha_dummy_025 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_024 r a))
            (Class.cv (nb062_alpha_dummy_025 r a)))).fv)
      0

theorem nb062_fresh_128 :
    (nb062_alpha_dummy_062) ∉
      (((syn_cnin (Class.cv (nb062_alpha_dummy_057)) (Class.cv (nb062_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_057))
            (Class.cv (nb062_alpha_dummy_058)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_062] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb062_alpha_dummy_057)) (Class.cv (nb062_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_057)) (Class.cv (nb062_alpha_dummy_058)))).fv)
      0

theorem nb062_fresh_129 (x : Var) (y : Var) :
    (nb062_alpha_dummy_063 x y) ∉
      (((syn_cnin (Class.cv (nb062_alpha_dummy_060 x y))
            (Class.cv (nb062_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_060 x y))
            (Class.cv (nb062_alpha_dummy_061 x y)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_063] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb062_alpha_dummy_060 x y))
            (Class.cv (nb062_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_060 x y))
            (Class.cv (nb062_alpha_dummy_061 x y)))).fv)
      0

theorem nb062_fresh_130 :
    (nb062_alpha_dummy_098) ∉
      (((syn_cnin (Class.cv (nb062_alpha_dummy_093)) (Class.cv (nb062_alpha_dummy_094)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_093))
            (Class.cv (nb062_alpha_dummy_094)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_098] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb062_alpha_dummy_093)) (Class.cv (nb062_alpha_dummy_094)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_093)) (Class.cv (nb062_alpha_dummy_094)))).fv)
      0

theorem nb062_fresh_131 (x : Var) (y : Var) :
    (nb062_alpha_dummy_099 x y) ∉
      (((syn_cnin (Class.cv (nb062_alpha_dummy_096 x y))
            (Class.cv (nb062_alpha_dummy_097 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_096 x y))
            (Class.cv (nb062_alpha_dummy_097 x y)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_099] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb062_alpha_dummy_096 x y))
            (Class.cv (nb062_alpha_dummy_097 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_096 x y))
            (Class.cv (nb062_alpha_dummy_097 x y)))).fv)
      0

theorem nb062_fresh_132 :
    (nb062_alpha_dummy_040) ∉
      (((syn_cphi (Class.cv (nb062_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_007)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb062_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_007)))).fv)
      0

theorem nb062_fresh_133 (r : Var) (a : Var) :
    (nb062_alpha_dummy_041 r a) ∉
      (((syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))).fv)
      0

theorem nb062_fresh_134 :
    (nb062_alpha_dummy_076) ∉
      (((syn_cphi (Class.cv (nb062_alpha_dummy_043)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_043)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_076] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb062_alpha_dummy_043)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_043)))).fv)
      0

theorem nb062_fresh_135 (x : Var) (y : Var) :
    (nb062_alpha_dummy_077 x y) ∉
      (((syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))).fv)
      0

theorem nb062_fresh_136 :
    (nb062_alpha_dummy_112) ∉
      (((syn_cphi (Class.cv (nb062_alpha_dummy_079)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_079)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_112] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb062_alpha_dummy_079)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_079)))).fv)
      0

theorem nb062_fresh_137 (x : Var) (y : Var) :
    (nb062_alpha_dummy_113 x y) ∉
      (((syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))).fv) :=
  by
  simpa only [nb062_alpha_dummy_113] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))).fv)
      0

theorem nb062_fresh_138 :
    (nb062_alpha_dummy_004) ∉
      (({(nb062_alpha_dummy_001)} : Finset Var) ∪ ({(nb062_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb062_alpha_dummy_002) (Class.cv (nb062_alpha_dummy_000))
            (syn_wral (nb062_alpha_dummy_003) (Class.cv (nb062_alpha_dummy_000)) (Wff.imp
                (syn_wa (syn_wbr (Class.cv (nb062_alpha_dummy_002))
                    (Class.cv (nb062_alpha_dummy_001)) (Class.cv (nb062_alpha_dummy_003)))
                  (syn_wbr (Class.cv (nb062_alpha_dummy_003)) (Class.cv (nb062_alpha_dummy_001))
                    (Class.cv (nb062_alpha_dummy_002))))
                (Wff.objEq (nb062_alpha_dummy_002) (nb062_alpha_dummy_003)))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_004] using
    freshVar_not_mem
      (({(nb062_alpha_dummy_001)} : Finset Var) ∪ ({(nb062_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb062_alpha_dummy_002) (Class.cv (nb062_alpha_dummy_000))
            (syn_wral (nb062_alpha_dummy_003) (Class.cv (nb062_alpha_dummy_000)) (Wff.imp
                (syn_wa (syn_wbr (Class.cv (nb062_alpha_dummy_002))
                    (Class.cv (nb062_alpha_dummy_001)) (Class.cv (nb062_alpha_dummy_003)))
                  (syn_wbr (Class.cv (nb062_alpha_dummy_003)) (Class.cv (nb062_alpha_dummy_001))
                    (Class.cv (nb062_alpha_dummy_002))))
                (Wff.objEq (nb062_alpha_dummy_002) (nb062_alpha_dummy_003)))))).fv)
      0

theorem nb062_fresh_139 (x : Var) (y : Var) (r : Var) (a : Var) :
    (nb062_alpha_dummy_005 x y r a) ∉
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
            (syn_wral y (Class.cv a) (Wff.imp
                (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y))
                  (syn_wbr (Class.cv y) (Class.cv r) (Class.cv x))) (Wff.objEq x y))))).fv) :=
  by
  simpa only [nb062_alpha_dummy_005] using
    freshVar_not_mem
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
            (syn_wral y (Class.cv a) (Wff.imp
                (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y))
                  (syn_wbr (Class.cv y) (Class.cv r) (Class.cv x))) (Wff.objEq x y))))).fv)
      0

theorem nb062_fresh_140 : (nb062_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb062_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb062_fresh_141 : (nb062_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb062_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb062_fresh_142 : (nb062_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb062_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb062_fresh_143 : (nb062_alpha_dummy_003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb062_alpha_dummy_003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb062_distinct_144 : (nb062_alpha_dummy_000) ≠ (nb062_alpha_dummy_001) := by
  simpa only [nb062_alpha_dummy_000, nb062_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb062_distinct_145 : (nb062_alpha_dummy_000) ≠ (nb062_alpha_dummy_002) := by
  simpa only [nb062_alpha_dummy_000, nb062_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb062_distinct_146 : (nb062_alpha_dummy_000) ≠ (nb062_alpha_dummy_003) := by
  simpa only [nb062_alpha_dummy_000, nb062_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb062_distinct_147 : (nb062_alpha_dummy_001) ≠ (nb062_alpha_dummy_002) := by
  simpa only [nb062_alpha_dummy_001, nb062_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb062_distinct_148 : (nb062_alpha_dummy_001) ≠ (nb062_alpha_dummy_003) := by
  simpa only [nb062_alpha_dummy_001, nb062_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb062_distinct_149 : (nb062_alpha_dummy_002) ≠ (nb062_alpha_dummy_003) := by
  simpa only [nb062_alpha_dummy_002, nb062_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb062_support_mem_0000 :
    (nb062_alpha_dummy_001) ∈
      (({(nb062_alpha_dummy_001)} : Finset Var) ∪ ({(nb062_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb062_alpha_dummy_002) (Class.cv (nb062_alpha_dummy_000))
            (syn_wral (nb062_alpha_dummy_003) (Class.cv (nb062_alpha_dummy_000)) (Wff.imp
                (syn_wa (syn_wbr (Class.cv (nb062_alpha_dummy_002))
                    (Class.cv (nb062_alpha_dummy_001)) (Class.cv (nb062_alpha_dummy_003)))
                  (syn_wbr (Class.cv (nb062_alpha_dummy_003)) (Class.cv (nb062_alpha_dummy_001))
                    (Class.cv (nb062_alpha_dummy_002))))
                (Wff.objEq (nb062_alpha_dummy_002) (nb062_alpha_dummy_003)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0001 (x : Var) (y : Var) (r : Var) (a : Var) :
    r ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
            (syn_wral y (Class.cv a) (Wff.imp
                (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y))
                  (syn_wbr (Class.cv y) (Class.cv r) (Class.cv x))) (Wff.objEq x y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0002 :
    (nb062_alpha_dummy_000) ∈
      (({(nb062_alpha_dummy_001)} : Finset Var) ∪ ({(nb062_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb062_alpha_dummy_002) (Class.cv (nb062_alpha_dummy_000))
            (syn_wral (nb062_alpha_dummy_003) (Class.cv (nb062_alpha_dummy_000)) (Wff.imp
                (syn_wa (syn_wbr (Class.cv (nb062_alpha_dummy_002))
                    (Class.cv (nb062_alpha_dummy_001)) (Class.cv (nb062_alpha_dummy_003)))
                  (syn_wbr (Class.cv (nb062_alpha_dummy_003)) (Class.cv (nb062_alpha_dummy_001))
                    (Class.cv (nb062_alpha_dummy_002))))
                (Wff.objEq (nb062_alpha_dummy_002) (nb062_alpha_dummy_003)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0003 (x : Var) (y : Var) (r : Var) (a : Var) :
    a ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
            (syn_wral y (Class.cv a) (Wff.imp
                (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y))
                  (syn_wbr (Class.cv y) (Class.cv r) (Class.cv x))) (Wff.objEq x y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0004 :
    (nb062_alpha_dummy_001) ∈
      (((Class.cv (nb062_alpha_dummy_001))).fv ∪ ((Class.cv (nb062_alpha_dummy_000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0005 :
    (nb062_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_006)
              (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_006)
              (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0006 (r : Var) (a : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0007 (r : Var) (a : Var) :
    r ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_008 r a)
              (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_008 r a)
              (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0008 :
    (nb062_alpha_dummy_001) ∈
      (((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cphi (Class.cv (nb062_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cphi (Class.cv (nb062_alpha_dummy_007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0009 (r : Var) (a : Var) :
    r ∈
      (((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0010 :
    (nb062_alpha_dummy_007) ∈ (((Class.cv (nb062_alpha_dummy_007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0011 (r : Var) (a : Var) :
    (nb062_alpha_dummy_009 r a) ∈ (((Class.cv (nb062_alpha_dummy_009 r a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0012 :
    (nb062_alpha_dummy_014) ∈
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_014)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_014)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_014))).fv) :=
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

theorem nb062_support_mem_0013 (r : Var) (a : Var) :
    (nb062_alpha_dummy_016 r a) ∈
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_016 r a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_016 r a)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_016 r a))).fv) :=
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

theorem nb062_support_mem_0014 :
    (nb062_alpha_dummy_014) ∈
      (((Class.cv (nb062_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0015 (r : Var) (a : Var) :
    (nb062_alpha_dummy_016 r a) ∈
      (((Class.cv (nb062_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0016 :
    (nb062_alpha_dummy_021) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_021)) (Class.cv (nb062_alpha_dummy_022)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_021))
            (Class.cv (nb062_alpha_dummy_022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0017 (r : Var) (a : Var) :
    (nb062_alpha_dummy_024 r a) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_024 r a))
            (Class.cv (nb062_alpha_dummy_025 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_024 r a))
            (Class.cv (nb062_alpha_dummy_025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0018 :
    (nb062_alpha_dummy_021) ∈
      (((Class.cv (nb062_alpha_dummy_021))).fv ∪ ((Class.cv (nb062_alpha_dummy_022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0019 (r : Var) (a : Var) :
    (nb062_alpha_dummy_024 r a) ∈
      (((Class.cv (nb062_alpha_dummy_024 r a))).fv ∪
        ((Class.cv (nb062_alpha_dummy_025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0020 :
    (nb062_alpha_dummy_022) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_021)) (Class.cv (nb062_alpha_dummy_022)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_021))
            (Class.cv (nb062_alpha_dummy_022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0021 (r : Var) (a : Var) :
    (nb062_alpha_dummy_025 r a) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_024 r a))
            (Class.cv (nb062_alpha_dummy_025 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_024 r a))
            (Class.cv (nb062_alpha_dummy_025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0022 :
    (nb062_alpha_dummy_022) ∈
      (((Class.cv (nb062_alpha_dummy_021))).fv ∪ ((Class.cv (nb062_alpha_dummy_022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0023 (r : Var) (a : Var) :
    (nb062_alpha_dummy_025 r a) ∈
      (((Class.cv (nb062_alpha_dummy_024 r a))).fv ∪
        ((Class.cv (nb062_alpha_dummy_025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0024 :
    (nb062_alpha_dummy_021) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_021)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0025 (r : Var) (a : Var) :
    (nb062_alpha_dummy_024 r a) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_024 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0026 :
    (nb062_alpha_dummy_021) ∈
      (((Class.cv (nb062_alpha_dummy_021))).fv ∪ ((Class.cv (nb062_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0027 (r : Var) (a : Var) :
    (nb062_alpha_dummy_024 r a) ∈
      (((Class.cv (nb062_alpha_dummy_024 r a))).fv ∪
        ((Class.cv (nb062_alpha_dummy_024 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0028 :
    (nb062_alpha_dummy_022) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_021)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0029 (r : Var) (a : Var) :
    (nb062_alpha_dummy_025 r a) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_024 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0030 :
    (nb062_alpha_dummy_022) ∈
      (((Class.cv (nb062_alpha_dummy_022))).fv ∪ ((Class.cv (nb062_alpha_dummy_022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0031 (r : Var) (a : Var) :
    (nb062_alpha_dummy_025 r a) ∈
      (((Class.cv (nb062_alpha_dummy_025 r a))).fv ∪
        ((Class.cv (nb062_alpha_dummy_025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0032 :
    (nb062_alpha_dummy_000) ∈
      (((Class.cv (nb062_alpha_dummy_001))).fv ∪ ((Class.cv (nb062_alpha_dummy_000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0033 :
    (nb062_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_006)
              (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_006)
              (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0034 (r : Var) (a : Var) :
    a ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0035 (r : Var) (a : Var) :
    a ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_008 r a)
              (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_008 r a)
              (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C062C001Part003`. -/


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

theorem nb062_support_mem_0036 :
    (nb062_alpha_dummy_000) ∈
      (((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_006)
            (syn_wrex (nb062_alpha_dummy_007) (Class.cv (nb062_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0037 (r : Var) (a : Var) :
    a ∈
      (((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_008 r a)
            (syn_wrex (nb062_alpha_dummy_009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_008 r a))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0038 :
    (nb062_alpha_dummy_007) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0039 (r : Var) (a : Var) :
    (nb062_alpha_dummy_009 r a) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_009 r a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0040 :
    (nb062_alpha_dummy_007) ∈
      (((syn_cphi (Class.cv (nb062_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0041 (r : Var) (a : Var) :
    (nb062_alpha_dummy_009 r a) ∈
      (((syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_009 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0042 :
    (nb062_alpha_dummy_002) ∈
      (((Class.cv (nb062_alpha_dummy_002))).fv ∪ ((Class.cv (nb062_alpha_dummy_003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0043 :
    (nb062_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_042)
              (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_043)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_042)
              (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0044 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0045 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_044 x y)
              (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_044 x y)
              (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0046 :
    (nb062_alpha_dummy_002) ∈
      (((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cphi (Class.cv (nb062_alpha_dummy_043))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cphi (Class.cv (nb062_alpha_dummy_043))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0047 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0048 :
    (nb062_alpha_dummy_043) ∈ (((Class.cv (nb062_alpha_dummy_043))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0049 (x : Var) (y : Var) :
    (nb062_alpha_dummy_045 x y) ∈ (((Class.cv (nb062_alpha_dummy_045 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0050 :
    (nb062_alpha_dummy_050) ∈
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_050))).fv) :=
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

theorem nb062_support_mem_0051 (x : Var) (y : Var) :
    (nb062_alpha_dummy_052 x y) ∈
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_052 x y))).fv) :=
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

theorem nb062_support_mem_0052 :
    (nb062_alpha_dummy_050) ∈
      (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0053 (x : Var) (y : Var) :
    (nb062_alpha_dummy_052 x y) ∈
      (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0054 :
    (nb062_alpha_dummy_057) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_057)) (Class.cv (nb062_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_057))
            (Class.cv (nb062_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0055 (x : Var) (y : Var) :
    (nb062_alpha_dummy_060 x y) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_060 x y))
            (Class.cv (nb062_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_060 x y))
            (Class.cv (nb062_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0056 :
    (nb062_alpha_dummy_057) ∈
      (((Class.cv (nb062_alpha_dummy_057))).fv ∪ ((Class.cv (nb062_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0057 (x : Var) (y : Var) :
    (nb062_alpha_dummy_060 x y) ∈
      (((Class.cv (nb062_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0058 :
    (nb062_alpha_dummy_058) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_057)) (Class.cv (nb062_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_057))
            (Class.cv (nb062_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0059 (x : Var) (y : Var) :
    (nb062_alpha_dummy_061 x y) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_060 x y))
            (Class.cv (nb062_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_060 x y))
            (Class.cv (nb062_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0060 :
    (nb062_alpha_dummy_058) ∈
      (((Class.cv (nb062_alpha_dummy_057))).fv ∪ ((Class.cv (nb062_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0061 (x : Var) (y : Var) :
    (nb062_alpha_dummy_061 x y) ∈
      (((Class.cv (nb062_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0062 :
    (nb062_alpha_dummy_057) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0063 (x : Var) (y : Var) :
    (nb062_alpha_dummy_060 x y) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0064 :
    (nb062_alpha_dummy_057) ∈
      (((Class.cv (nb062_alpha_dummy_057))).fv ∪ ((Class.cv (nb062_alpha_dummy_057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0065 (x : Var) (y : Var) :
    (nb062_alpha_dummy_060 x y) ∈
      (((Class.cv (nb062_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0066 :
    (nb062_alpha_dummy_058) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0067 (x : Var) (y : Var) :
    (nb062_alpha_dummy_061 x y) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0068 :
    (nb062_alpha_dummy_058) ∈
      (((Class.cv (nb062_alpha_dummy_058))).fv ∪ ((Class.cv (nb062_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0069 (x : Var) (y : Var) :
    (nb062_alpha_dummy_061 x y) ∈
      (((Class.cv (nb062_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0070 :
    (nb062_alpha_dummy_003) ∈
      (((Class.cv (nb062_alpha_dummy_002))).fv ∪ ((Class.cv (nb062_alpha_dummy_003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0071 :
    (nb062_alpha_dummy_003) ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_042)
              (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_043)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_042)
              (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0072 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0073 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_044 x y)
              (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_044 x y)
              (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0074 :
    (nb062_alpha_dummy_003) ∈
      (((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_042)
            (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_042))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0075 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_044 x y)
            (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0076 :
    (nb062_alpha_dummy_043) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_043))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0077 (x : Var) (y : Var) :
    (nb062_alpha_dummy_045 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0078 :
    (nb062_alpha_dummy_043) ∈
      (((syn_cphi (Class.cv (nb062_alpha_dummy_043)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_043)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0079 (x : Var) (y : Var) :
    (nb062_alpha_dummy_045 x y) ∈
      (((syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0080 :
    (nb062_alpha_dummy_003) ∈
      (((Class.cv (nb062_alpha_dummy_003))).fv ∪ ((Class.cv (nb062_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0081 :
    (nb062_alpha_dummy_003) ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_078)
              (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_079)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_078)
              (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0082 (x : Var) (y : Var) :
    y ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0083 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_080 x y)
              (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_080 x y)
              (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0082 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0082 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0084 :
    (nb062_alpha_dummy_003) ∈
      (((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cphi (Class.cv (nb062_alpha_dummy_079))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cphi (Class.cv (nb062_alpha_dummy_079))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0085 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))))).fv ∪
        ((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0082 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0082 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0086 :
    (nb062_alpha_dummy_079) ∈ (((Class.cv (nb062_alpha_dummy_079))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0087 (x : Var) (y : Var) :
    (nb062_alpha_dummy_081 x y) ∈ (((Class.cv (nb062_alpha_dummy_081 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0088 :
    (nb062_alpha_dummy_086) ∈
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_086)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_086)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_086))).fv) :=
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

theorem nb062_support_mem_0089 (x : Var) (y : Var) :
    (nb062_alpha_dummy_088 x y) ∈
      (((Wff.classMem (Class.cv (nb062_alpha_dummy_088 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb062_alpha_dummy_088 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb062_alpha_dummy_088 x y))).fv) :=
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

theorem nb062_support_mem_0090 :
    (nb062_alpha_dummy_086) ∈
      (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0091 (x : Var) (y : Var) :
    (nb062_alpha_dummy_088 x y) ∈
      (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0092 :
    (nb062_alpha_dummy_093) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_093)) (Class.cv (nb062_alpha_dummy_094)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_093))
            (Class.cv (nb062_alpha_dummy_094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0093 (x : Var) (y : Var) :
    (nb062_alpha_dummy_096 x y) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_096 x y))
            (Class.cv (nb062_alpha_dummy_097 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_096 x y))
            (Class.cv (nb062_alpha_dummy_097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0094 :
    (nb062_alpha_dummy_093) ∈
      (((Class.cv (nb062_alpha_dummy_093))).fv ∪ ((Class.cv (nb062_alpha_dummy_094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0095 (x : Var) (y : Var) :
    (nb062_alpha_dummy_096 x y) ∈
      (((Class.cv (nb062_alpha_dummy_096 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0096 :
    (nb062_alpha_dummy_094) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_093)) (Class.cv (nb062_alpha_dummy_094)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_093))
            (Class.cv (nb062_alpha_dummy_094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0097 (x : Var) (y : Var) :
    (nb062_alpha_dummy_097 x y) ∈
      (((syn_cnin (Class.cv (nb062_alpha_dummy_096 x y))
            (Class.cv (nb062_alpha_dummy_097 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb062_alpha_dummy_096 x y))
            (Class.cv (nb062_alpha_dummy_097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0098 :
    (nb062_alpha_dummy_094) ∈
      (((Class.cv (nb062_alpha_dummy_093))).fv ∪ ((Class.cv (nb062_alpha_dummy_094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0099 (x : Var) (y : Var) :
    (nb062_alpha_dummy_097 x y) ∈
      (((Class.cv (nb062_alpha_dummy_096 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0100 :
    (nb062_alpha_dummy_093) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_093)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0101 (x : Var) (y : Var) :
    (nb062_alpha_dummy_096 x y) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_096 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0102 :
    (nb062_alpha_dummy_093) ∈
      (((Class.cv (nb062_alpha_dummy_093))).fv ∪ ((Class.cv (nb062_alpha_dummy_093))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0103 (x : Var) (y : Var) :
    (nb062_alpha_dummy_096 x y) ∈
      (((Class.cv (nb062_alpha_dummy_096 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_096 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0104 :
    (nb062_alpha_dummy_094) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_093)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0105 (x : Var) (y : Var) :
    (nb062_alpha_dummy_097 x y) ∈
      (((syn_ccompl (Class.cv (nb062_alpha_dummy_096 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb062_alpha_dummy_097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0106 :
    (nb062_alpha_dummy_094) ∈
      (((Class.cv (nb062_alpha_dummy_094))).fv ∪ ((Class.cv (nb062_alpha_dummy_094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0107 (x : Var) (y : Var) :
    (nb062_alpha_dummy_097 x y) ∈
      (((Class.cv (nb062_alpha_dummy_097 x y))).fv ∪
        ((Class.cv (nb062_alpha_dummy_097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0108 :
    (nb062_alpha_dummy_002) ∈
      (((Class.cv (nb062_alpha_dummy_003))).fv ∪ ((Class.cv (nb062_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0109 :
    (nb062_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_078)
              (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_079)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_078)
              (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0110 (x : Var) (y : Var) :
    x ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0111 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb062_alpha_dummy_080 x y)
              (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                  (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb062_alpha_dummy_080 x y)
              (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                  (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0112 :
    (nb062_alpha_dummy_002) ∈
      (((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_078)
            (syn_wrex (nb062_alpha_dummy_079) (Class.cv (nb062_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb062_alpha_dummy_078))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_079)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0113 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb062_alpha_dummy_080 x y)
            (syn_wrex (nb062_alpha_dummy_081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062_alpha_dummy_080 x y))
                (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0114 :
    (nb062_alpha_dummy_079) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_079))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0115 (x : Var) (y : Var) :
    (nb062_alpha_dummy_081 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb062_alpha_dummy_081 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0116 :
    (nb062_alpha_dummy_079) ∈
      (((syn_cphi (Class.cv (nb062_alpha_dummy_079)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_079)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0117 (x : Var) (y : Var) :
    (nb062_alpha_dummy_081 x y) ∈
      (((syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb062_alpha_dummy_081 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
