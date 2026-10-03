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

/-! Certificates from `NAR4C060C001Part001`. -/


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
noncomputable def nb060_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb060_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb060_alpha_dummy_002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

@[expose]
noncomputable def nb060_alpha_dummy_003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

@[expose]
noncomputable def nb060_alpha_dummy_004 : Var :=
  (freshVar ((∅ : Finset Var)) 4)

@[expose]
noncomputable def nb060_alpha_dummy_005 : Var :=
  (freshVar
    (({(nb060_alpha_dummy_001)} : Finset Var) ∪ ({(nb060_alpha_dummy_000)} : Finset Var) ∪
      ((syn_wral (nb060_alpha_dummy_002) (Class.cv (nb060_alpha_dummy_000))
          (syn_wral (nb060_alpha_dummy_003) (Class.cv (nb060_alpha_dummy_000))
            (syn_wral (nb060_alpha_dummy_004) (Class.cv (nb060_alpha_dummy_000)) (Wff.imp
                (syn_wa (syn_wbr (Class.cv (nb060_alpha_dummy_002))
                    (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_003)))
                  (syn_wbr (Class.cv (nb060_alpha_dummy_003)) (Class.cv (nb060_alpha_dummy_001))
                    (Class.cv (nb060_alpha_dummy_004))))
                (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001))
                  (Class.cv (nb060_alpha_dummy_004)))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_006 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) : Var :=
  (freshVar (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
          (syn_wral y (Class.cv a) (syn_wral z (Class.cv a) (Wff.imp
                (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y))
                  (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z)))
                (syn_wbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_007 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_008 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_009 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_010 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_011 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cphi (Class.cv (nb060_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_012 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_013 : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_007)
          (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
              (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv ∪
      ((Class.cab (nb060_alpha_dummy_007)
          (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
              (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_014 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_009 r a)
          (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
              (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv ∪
      ((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
              (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_015 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_008))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_016 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_008))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_017 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_010 r a))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_018 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_010 r a))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_019 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_015)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb060_alpha_dummy_015)) (syn_c1c))).fv ∪
      ((Class.cv (nb060_alpha_dummy_015))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_020 (r : Var) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_017 r a)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb060_alpha_dummy_017 r a)) (syn_c1c))).fv ∪
      ((Class.cv (nb060_alpha_dummy_017 r a))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_021 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_022 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_023 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb060_alpha_dummy_024 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_025 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_026 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb060_alpha_dummy_027 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_022))
          (Class.cv (nb060_alpha_dummy_023)))).fv ∪
      ((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_028 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a))
          (Class.cv (nb060_alpha_dummy_026 r a)))).fv ∪
      ((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a))
          (Class.cv (nb060_alpha_dummy_026 r a)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_029 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_030 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪
      ((Class.cv (nb060_alpha_dummy_026 r a))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_031 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_022)))).fv ∪
      ((syn_ccompl (Class.cv (nb060_alpha_dummy_023)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_032 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_025 r a)))).fv ∪
      ((syn_ccompl (Class.cv (nb060_alpha_dummy_026 r a)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_033 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_022))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_034 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪
      ((Class.cv (nb060_alpha_dummy_025 r a))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_035 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_023))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_036 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_026 r a))).fv ∪
      ((Class.cv (nb060_alpha_dummy_026 r a))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_037 : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_007)
          (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007)
          (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_038 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_009 r a)
          (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a)
          (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_039 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_008))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_040 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_041 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv ∪
      ((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_042 (r : Var) (a : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv ∪
      ((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_043 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_044 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_046 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_047 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cphi (Class.cv (nb060_alpha_dummy_044)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_048 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_049 : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_043)
          (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
              (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv ∪
      ((Class.cab (nb060_alpha_dummy_043)
          (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
              (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_050 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_045 x y)
          (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
              (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv ∪
      ((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
              (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_051 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_044))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_052 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_044))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_046 x y))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_054 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_046 x y))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_055 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_051)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb060_alpha_dummy_051)) (syn_c1c))).fv ∪
      ((Class.cv (nb060_alpha_dummy_051))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_056 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb060_alpha_dummy_053 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb060_alpha_dummy_053 x y))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_057 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_058 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_059 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb060_alpha_dummy_060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_062 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb060_alpha_dummy_063 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_058))
          (Class.cv (nb060_alpha_dummy_059)))).fv ∪
      ((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_064 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y))
          (Class.cv (nb060_alpha_dummy_062 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y))
          (Class.cv (nb060_alpha_dummy_062 x y)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_065 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_066 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪
      ((Class.cv (nb060_alpha_dummy_062 x y))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_067 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_058)))).fv ∪
      ((syn_ccompl (Class.cv (nb060_alpha_dummy_059)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_068 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_061 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb060_alpha_dummy_062 x y)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_069 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_058))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_070 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪
      ((Class.cv (nb060_alpha_dummy_061 x y))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_071 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_059))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_072 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_062 x y))).fv ∪
      ((Class.cv (nb060_alpha_dummy_062 x y))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_073 : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_043)
          (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043)
          (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_074 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_045 x y)
          (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y)
          (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_075 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_044))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_076 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_077 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv ∪
      ((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_078 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_079 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_080 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_081 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_082 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_083 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cphi (Class.cv (nb060_alpha_dummy_080)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_084 (y : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_085 : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_079)
          (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
              (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv ∪
      ((Class.cab (nb060_alpha_dummy_079)
          (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
              (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_086 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_081 y z)
          (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
              (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv ∪
      ((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
              (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_087 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_080))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_088 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_080))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_089 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_082 y z))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_090 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_082 y z))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_091 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_087)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb060_alpha_dummy_087)) (syn_c1c))).fv ∪
      ((Class.cv (nb060_alpha_dummy_087))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_092 (y : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb060_alpha_dummy_089 y z)) (syn_c1c))).fv ∪
      ((Class.cv (nb060_alpha_dummy_089 y z))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_093 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_094 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_095 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb060_alpha_dummy_096 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_097 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_098 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb060_alpha_dummy_099 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_094))
          (Class.cv (nb060_alpha_dummy_095)))).fv ∪
      ((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_100 (y : Var) (z : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z))
          (Class.cv (nb060_alpha_dummy_098 y z)))).fv ∪
      ((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z))
          (Class.cv (nb060_alpha_dummy_098 y z)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_101 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_102 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪
      ((Class.cv (nb060_alpha_dummy_098 y z))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_103 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_094)))).fv ∪
      ((syn_ccompl (Class.cv (nb060_alpha_dummy_095)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_104 (y : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_097 y z)))).fv ∪
      ((syn_ccompl (Class.cv (nb060_alpha_dummy_098 y z)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_105 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_094))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_106 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪
      ((Class.cv (nb060_alpha_dummy_097 y z))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_107 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_095))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_108 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_098 y z))).fv ∪
      ((Class.cv (nb060_alpha_dummy_098 y z))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_109 : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_079)
          (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079)
          (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_110 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_081 y z)
          (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z)
          (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_111 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_080))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_112 (y : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_113 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv ∪
      ((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_114 (y : Var) (z : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv ∪
      ((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_115 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_116 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_117 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_118 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_119 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cphi (Class.cv (nb060_alpha_dummy_116)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_120 (x : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_121 : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_115)
          (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
              (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv ∪
      ((Class.cab (nb060_alpha_dummy_115)
          (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
              (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_122 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_117 x z)
          (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
              (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv ∪
      ((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
              (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_123 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_116))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_124 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_116))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_125 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_118 x z))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_126 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_118 x z))).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_127 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_123)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb060_alpha_dummy_123)) (syn_c1c))).fv ∪
      ((Class.cv (nb060_alpha_dummy_123))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_128 (x : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_125 x z)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb060_alpha_dummy_125 x z)) (syn_c1c))).fv ∪
      ((Class.cv (nb060_alpha_dummy_125 x z))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_129 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_130 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_131 : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb060_alpha_dummy_132 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_133 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb060_alpha_dummy_134 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb060_alpha_dummy_135 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_130))
          (Class.cv (nb060_alpha_dummy_131)))).fv ∪
      ((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_136 (x : Var) (z : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z))
          (Class.cv (nb060_alpha_dummy_134 x z)))).fv ∪
      ((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z))
          (Class.cv (nb060_alpha_dummy_134 x z)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_137 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_138 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪
      ((Class.cv (nb060_alpha_dummy_134 x z))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_139 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_130)))).fv ∪
      ((syn_ccompl (Class.cv (nb060_alpha_dummy_131)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_140 (x : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_133 x z)))).fv ∪
      ((syn_ccompl (Class.cv (nb060_alpha_dummy_134 x z)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_141 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_130))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_142 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪
      ((Class.cv (nb060_alpha_dummy_133 x z))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_143 : Var :=
  (freshVar
    (((Class.cv (nb060_alpha_dummy_131))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_144 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060_alpha_dummy_134 x z))).fv ∪
      ((Class.cv (nb060_alpha_dummy_134 x z))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_145 : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_115)
          (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115)
          (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
            (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_146 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb060_alpha_dummy_117 x z)
          (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z)
          (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
            (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
              (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_147 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_116))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_148 (x : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb060_alpha_dummy_149 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv ∪
      ((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part002`. -/


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
noncomputable def nb060_alpha_dummy_150 (x : Var) (z : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv ∪
      ((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv) 0)

theorem nb060_fresh_000 :
    (nb060_alpha_dummy_037) ∉
      (((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb060_fresh_001 :
    (nb060_alpha_dummy_013) ∉
      (((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_013] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv)
      0

theorem nb060_fresh_002 (r : Var) (a : Var) :
    (nb060_alpha_dummy_038 r a) ∉
      (((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_038] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb060_fresh_003 (r : Var) (a : Var) :
    (nb060_alpha_dummy_014 r a) ∉
      (((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_014] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv)
      0

theorem nb060_fresh_004 :
    (nb060_alpha_dummy_049) ∉
      (((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_049] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv)
      0

theorem nb060_fresh_005 :
    (nb060_alpha_dummy_073) ∉
      (((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb060_fresh_006 (x : Var) (y : Var) :
    (nb060_alpha_dummy_050 x y) ∉
      (((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_050] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv)
      0

theorem nb060_fresh_007 (x : Var) (y : Var) :
    (nb060_alpha_dummy_074 x y) ∉
      (((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_074] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb060_fresh_008 :
    (nb060_alpha_dummy_085) ∉
      (((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_085] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv)
      0

theorem nb060_fresh_009 :
    (nb060_alpha_dummy_109) ∉
      (((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_109] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb060_fresh_010 (y : Var) (z : Var) :
    (nb060_alpha_dummy_086 y z) ∉
      (((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_086] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv)
      0

theorem nb060_fresh_011 (y : Var) (z : Var) :
    (nb060_alpha_dummy_110 y z) ∉
      (((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_110] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb060_fresh_012 :
    (nb060_alpha_dummy_121) ∉
      (((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_121] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv)
      0

theorem nb060_fresh_013 :
    (nb060_alpha_dummy_145) ∉
      (((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_145] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb060_fresh_014 (x : Var) (z : Var) :
    (nb060_alpha_dummy_122 x z) ∉
      (((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_122] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv)
      0

theorem nb060_fresh_015 (x : Var) (z : Var) :
    (nb060_alpha_dummy_146 x z) ∉
      (((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_146] using
    freshVar_not_mem
      (((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb060_fresh_016 :
    (nb060_alpha_dummy_007) ∉
      (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) :=
  by
  simpa only [nb060_alpha_dummy_007] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv)
      0

theorem nb060_fresh_017 :
    (nb060_alpha_dummy_008) ∉
      (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) :=
  by
  simpa only [nb060_alpha_dummy_008] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv)
      1

theorem nb060_distinct_018 : (nb060_alpha_dummy_007) ≠ (nb060_alpha_dummy_008) := by
  simpa only [nb060_alpha_dummy_007, nb060_alpha_dummy_008] using
    (freshVar_injective
      (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_fresh_019 :
    (nb060_alpha_dummy_043) ∉
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) :=
  by
  simpa only [nb060_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv)
      0

theorem nb060_fresh_020 :
    (nb060_alpha_dummy_044) ∉
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) :=
  by
  simpa only [nb060_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv)
      1

theorem nb060_distinct_021 : (nb060_alpha_dummy_043) ≠ (nb060_alpha_dummy_044) := by
  simpa only [nb060_alpha_dummy_043, nb060_alpha_dummy_044] using
    (freshVar_injective
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_fresh_022 :
    (nb060_alpha_dummy_115) ∉
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) :=
  by
  simpa only [nb060_alpha_dummy_115] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv)
      0

theorem nb060_fresh_023 :
    (nb060_alpha_dummy_116) ∉
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) :=
  by
  simpa only [nb060_alpha_dummy_116] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv)
      1

theorem nb060_distinct_024 : (nb060_alpha_dummy_115) ≠ (nb060_alpha_dummy_116) := by
  simpa only [nb060_alpha_dummy_115, nb060_alpha_dummy_116] using
    (freshVar_injective
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_fresh_025 :
    (nb060_alpha_dummy_079) ∉
      (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) :=
  by
  simpa only [nb060_alpha_dummy_079] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv)
      0

theorem nb060_fresh_026 :
    (nb060_alpha_dummy_080) ∉
      (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) :=
  by
  simpa only [nb060_alpha_dummy_080] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv)
      1

theorem nb060_distinct_027 : (nb060_alpha_dummy_079) ≠ (nb060_alpha_dummy_080) := by
  simpa only [nb060_alpha_dummy_079, nb060_alpha_dummy_080] using
    (freshVar_injective
      (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_fresh_028 :
    (nb060_alpha_dummy_015) ∉ (((Class.cv (nb060_alpha_dummy_008))).fv) := by
  simpa only [nb060_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_008))).fv) 0

theorem nb060_fresh_029 :
    (nb060_alpha_dummy_016) ∉ (((Class.cv (nb060_alpha_dummy_008))).fv) := by
  simpa only [nb060_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_008))).fv) 1

theorem nb060_distinct_030 : (nb060_alpha_dummy_015) ≠ (nb060_alpha_dummy_016) := by
  simpa only [nb060_alpha_dummy_015, nb060_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_008))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_031 (r : Var) (a : Var) :
    (nb060_alpha_dummy_017 r a) ∉ (((Class.cv (nb060_alpha_dummy_010 r a))).fv) := by
  simpa only [nb060_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_010 r a))).fv) 0

theorem nb060_fresh_032 (r : Var) (a : Var) :
    (nb060_alpha_dummy_018 r a) ∉ (((Class.cv (nb060_alpha_dummy_010 r a))).fv) := by
  simpa only [nb060_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_010 r a))).fv) 1

theorem nb060_distinct_033 (r : Var) (a : Var) :
    (nb060_alpha_dummy_017 r a) ≠ (nb060_alpha_dummy_018 r a) := by
  simpa only [nb060_alpha_dummy_017, nb060_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_010 r a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb060_fresh_034 :
    (nb060_alpha_dummy_021) ∉
      (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_035 :
    (nb060_alpha_dummy_022) ∉
      (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_036 :
    (nb060_alpha_dummy_023) ∉
      (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_037 : (nb060_alpha_dummy_021) ≠ (nb060_alpha_dummy_022) := by
  simpa only [nb060_alpha_dummy_021, nb060_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb060_distinct_038 : (nb060_alpha_dummy_021) ≠ (nb060_alpha_dummy_023) := by
  simpa only [nb060_alpha_dummy_021, nb060_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb060_distinct_039 : (nb060_alpha_dummy_022) ≠ (nb060_alpha_dummy_023) := by
  simpa only [nb060_alpha_dummy_022, nb060_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb060_fresh_040 (r : Var) (a : Var) :
    (nb060_alpha_dummy_024 r a) ∉
      (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_041 (r : Var) (a : Var) :
    (nb060_alpha_dummy_025 r a) ∉
      (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_042 (r : Var) (a : Var) :
    (nb060_alpha_dummy_026 r a) ∉
      (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_026] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_043 (r : Var) (a : Var) :
    (nb060_alpha_dummy_024 r a) ≠ (nb060_alpha_dummy_025 r a) := by
  simpa only [nb060_alpha_dummy_024, nb060_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_distinct_044 (r : Var) (a : Var) :
    (nb060_alpha_dummy_024 r a) ≠ (nb060_alpha_dummy_026 r a) := by
  simpa only [nb060_alpha_dummy_024, nb060_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb060_distinct_045 (r : Var) (a : Var) :
    (nb060_alpha_dummy_025 r a) ≠ (nb060_alpha_dummy_026 r a) := by
  simpa only [nb060_alpha_dummy_025, nb060_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb060_fresh_046 :
    (nb060_alpha_dummy_033) ∉
      (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_022))).fv) :=
  by
  simpa only [nb060_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_022))).fv)
      0

theorem nb060_fresh_047 :
    (nb060_alpha_dummy_029) ∉
      (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) :=
  by
  simpa only [nb060_alpha_dummy_029] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv)
      0

theorem nb060_fresh_048 :
    (nb060_alpha_dummy_035) ∉
      (((Class.cv (nb060_alpha_dummy_023))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) :=
  by
  simpa only [nb060_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_023))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv)
      0

theorem nb060_fresh_049 (r : Var) (a : Var) :
    (nb060_alpha_dummy_034 r a) ∉
      (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪
        ((Class.cv (nb060_alpha_dummy_025 r a))).fv) :=
  by
  simpa only [nb060_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪
        ((Class.cv (nb060_alpha_dummy_025 r a))).fv)
      0

theorem nb060_fresh_050 (r : Var) (a : Var) :
    (nb060_alpha_dummy_030 r a) ∉
      (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪
        ((Class.cv (nb060_alpha_dummy_026 r a))).fv) :=
  by
  simpa only [nb060_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪
        ((Class.cv (nb060_alpha_dummy_026 r a))).fv)
      0

theorem nb060_fresh_051 (r : Var) (a : Var) :
    (nb060_alpha_dummy_036 r a) ∉
      (((Class.cv (nb060_alpha_dummy_026 r a))).fv ∪
        ((Class.cv (nb060_alpha_dummy_026 r a))).fv) :=
  by
  simpa only [nb060_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_026 r a))).fv ∪
        ((Class.cv (nb060_alpha_dummy_026 r a))).fv)
      0

theorem nb060_fresh_052 :
    (nb060_alpha_dummy_051) ∉ (((Class.cv (nb060_alpha_dummy_044))).fv) := by
  simpa only [nb060_alpha_dummy_051] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_044))).fv) 0

theorem nb060_fresh_053 :
    (nb060_alpha_dummy_052) ∉ (((Class.cv (nb060_alpha_dummy_044))).fv) := by
  simpa only [nb060_alpha_dummy_052] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_044))).fv) 1

theorem nb060_distinct_054 : (nb060_alpha_dummy_051) ≠ (nb060_alpha_dummy_052) := by
  simpa only [nb060_alpha_dummy_051, nb060_alpha_dummy_052] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_044))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_055 (x : Var) (y : Var) :
    (nb060_alpha_dummy_053 x y) ∉ (((Class.cv (nb060_alpha_dummy_046 x y))).fv) := by
  simpa only [nb060_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_046 x y))).fv) 0

theorem nb060_fresh_056 (x : Var) (y : Var) :
    (nb060_alpha_dummy_054 x y) ∉ (((Class.cv (nb060_alpha_dummy_046 x y))).fv) := by
  simpa only [nb060_alpha_dummy_054] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_046 x y))).fv) 1

theorem nb060_distinct_057 (x : Var) (y : Var) :
    (nb060_alpha_dummy_053 x y) ≠ (nb060_alpha_dummy_054 x y) := by
  simpa only [nb060_alpha_dummy_053, nb060_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_046 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb060_fresh_058 :
    (nb060_alpha_dummy_057) ∉
      (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_057] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_059 :
    (nb060_alpha_dummy_058) ∉
      (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_060 :
    (nb060_alpha_dummy_059) ∉
      (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_061 : (nb060_alpha_dummy_057) ≠ (nb060_alpha_dummy_058) := by
  simpa only [nb060_alpha_dummy_057, nb060_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb060_distinct_062 : (nb060_alpha_dummy_057) ≠ (nb060_alpha_dummy_059) := by
  simpa only [nb060_alpha_dummy_057, nb060_alpha_dummy_059] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb060_distinct_063 : (nb060_alpha_dummy_058) ≠ (nb060_alpha_dummy_059) := by
  simpa only [nb060_alpha_dummy_058, nb060_alpha_dummy_059] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb060_fresh_064 (x : Var) (y : Var) :
    (nb060_alpha_dummy_060 x y) ∉
      (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_065 (x : Var) (y : Var) :
    (nb060_alpha_dummy_061 x y) ∉
      (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_066 (x : Var) (y : Var) :
    (nb060_alpha_dummy_062 x y) ∉
      (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_062] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_067 (x : Var) (y : Var) :
    (nb060_alpha_dummy_060 x y) ≠ (nb060_alpha_dummy_061 x y) := by
  simpa only [nb060_alpha_dummy_060, nb060_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_distinct_068 (x : Var) (y : Var) :
    (nb060_alpha_dummy_060 x y) ≠ (nb060_alpha_dummy_062 x y) := by
  simpa only [nb060_alpha_dummy_060, nb060_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb060_distinct_069 (x : Var) (y : Var) :
    (nb060_alpha_dummy_061 x y) ≠ (nb060_alpha_dummy_062 x y) := by
  simpa only [nb060_alpha_dummy_061, nb060_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb060_fresh_070 :
    (nb060_alpha_dummy_069) ∉
      (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_058))).fv) :=
  by
  simpa only [nb060_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_058))).fv)
      0

theorem nb060_fresh_071 :
    (nb060_alpha_dummy_065) ∉
      (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) :=
  by
  simpa only [nb060_alpha_dummy_065] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv)
      0

theorem nb060_fresh_072 :
    (nb060_alpha_dummy_071) ∉
      (((Class.cv (nb060_alpha_dummy_059))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) :=
  by
  simpa only [nb060_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_059))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv)
      0

theorem nb060_fresh_073 (x : Var) (y : Var) :
    (nb060_alpha_dummy_070 x y) ∉
      (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb060_alpha_dummy_061 x y))).fv) :=
  by
  simpa only [nb060_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb060_alpha_dummy_061 x y))).fv)
      0

theorem nb060_fresh_074 (x : Var) (y : Var) :
    (nb060_alpha_dummy_066 x y) ∉
      (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb060_alpha_dummy_062 x y))).fv) :=
  by
  simpa only [nb060_alpha_dummy_066] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb060_alpha_dummy_062 x y))).fv)
      0

theorem nb060_fresh_075 (x : Var) (y : Var) :
    (nb060_alpha_dummy_072 x y) ∉
      (((Class.cv (nb060_alpha_dummy_062 x y))).fv ∪
        ((Class.cv (nb060_alpha_dummy_062 x y))).fv) :=
  by
  simpa only [nb060_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_062 x y))).fv ∪
        ((Class.cv (nb060_alpha_dummy_062 x y))).fv)
      0

theorem nb060_fresh_076 :
    (nb060_alpha_dummy_087) ∉ (((Class.cv (nb060_alpha_dummy_080))).fv) := by
  simpa only [nb060_alpha_dummy_087] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_080))).fv) 0

theorem nb060_fresh_077 :
    (nb060_alpha_dummy_088) ∉ (((Class.cv (nb060_alpha_dummy_080))).fv) := by
  simpa only [nb060_alpha_dummy_088] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_080))).fv) 1

theorem nb060_distinct_078 : (nb060_alpha_dummy_087) ≠ (nb060_alpha_dummy_088) := by
  simpa only [nb060_alpha_dummy_087, nb060_alpha_dummy_088] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_080))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_079 (y : Var) (z : Var) :
    (nb060_alpha_dummy_089 y z) ∉ (((Class.cv (nb060_alpha_dummy_082 y z))).fv) := by
  simpa only [nb060_alpha_dummy_089] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_082 y z))).fv) 0

theorem nb060_fresh_080 (y : Var) (z : Var) :
    (nb060_alpha_dummy_090 y z) ∉ (((Class.cv (nb060_alpha_dummy_082 y z))).fv) := by
  simpa only [nb060_alpha_dummy_090] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_082 y z))).fv) 1

theorem nb060_distinct_081 (y : Var) (z : Var) :
    (nb060_alpha_dummy_089 y z) ≠ (nb060_alpha_dummy_090 y z) := by
  simpa only [nb060_alpha_dummy_089, nb060_alpha_dummy_090] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_082 y z))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb060_fresh_082 :
    (nb060_alpha_dummy_093) ∉
      (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_093] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_083 :
    (nb060_alpha_dummy_094) ∉
      (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_094] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_084 :
    (nb060_alpha_dummy_095) ∉
      (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_095] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_085 : (nb060_alpha_dummy_093) ≠ (nb060_alpha_dummy_094) := by
  simpa only [nb060_alpha_dummy_093, nb060_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb060_distinct_086 : (nb060_alpha_dummy_093) ≠ (nb060_alpha_dummy_095) := by
  simpa only [nb060_alpha_dummy_093, nb060_alpha_dummy_095] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb060_distinct_087 : (nb060_alpha_dummy_094) ≠ (nb060_alpha_dummy_095) := by
  simpa only [nb060_alpha_dummy_094, nb060_alpha_dummy_095] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb060_fresh_088 (y : Var) (z : Var) :
    (nb060_alpha_dummy_096 y z) ∉
      (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_096] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_089 (y : Var) (z : Var) :
    (nb060_alpha_dummy_097 y z) ∉
      (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_097] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_090 (y : Var) (z : Var) :
    (nb060_alpha_dummy_098 y z) ∉
      (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_098] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_091 (y : Var) (z : Var) :
    (nb060_alpha_dummy_096 y z) ≠ (nb060_alpha_dummy_097 y z) := by
  simpa only [nb060_alpha_dummy_096, nb060_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_distinct_092 (y : Var) (z : Var) :
    (nb060_alpha_dummy_096 y z) ≠ (nb060_alpha_dummy_098 y z) := by
  simpa only [nb060_alpha_dummy_096, nb060_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb060_distinct_093 (y : Var) (z : Var) :
    (nb060_alpha_dummy_097 y z) ≠ (nb060_alpha_dummy_098 y z) := by
  simpa only [nb060_alpha_dummy_097, nb060_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb060_fresh_094 :
    (nb060_alpha_dummy_105) ∉
      (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_094))).fv) :=
  by
  simpa only [nb060_alpha_dummy_105] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_094))).fv)
      0

theorem nb060_fresh_095 :
    (nb060_alpha_dummy_101) ∉
      (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) :=
  by
  simpa only [nb060_alpha_dummy_101] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv)
      0

theorem nb060_fresh_096 :
    (nb060_alpha_dummy_107) ∉
      (((Class.cv (nb060_alpha_dummy_095))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) :=
  by
  simpa only [nb060_alpha_dummy_107] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_095))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv)
      0

theorem nb060_fresh_097 (y : Var) (z : Var) :
    (nb060_alpha_dummy_106 y z) ∉
      (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_097 y z))).fv) :=
  by
  simpa only [nb060_alpha_dummy_106] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_097 y z))).fv)
      0

theorem nb060_fresh_098 (y : Var) (z : Var) :
    (nb060_alpha_dummy_102 y z) ∉
      (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_098 y z))).fv) :=
  by
  simpa only [nb060_alpha_dummy_102] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_098 y z))).fv)
      0

theorem nb060_fresh_099 (y : Var) (z : Var) :
    (nb060_alpha_dummy_108 y z) ∉
      (((Class.cv (nb060_alpha_dummy_098 y z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_098 y z))).fv) :=
  by
  simpa only [nb060_alpha_dummy_108] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_098 y z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_098 y z))).fv)
      0

theorem nb060_fresh_100 :
    (nb060_alpha_dummy_123) ∉ (((Class.cv (nb060_alpha_dummy_116))).fv) := by
  simpa only [nb060_alpha_dummy_123] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_116))).fv) 0

theorem nb060_fresh_101 :
    (nb060_alpha_dummy_124) ∉ (((Class.cv (nb060_alpha_dummy_116))).fv) := by
  simpa only [nb060_alpha_dummy_124] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_116))).fv) 1

theorem nb060_distinct_102 : (nb060_alpha_dummy_123) ≠ (nb060_alpha_dummy_124) := by
  simpa only [nb060_alpha_dummy_123, nb060_alpha_dummy_124] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_116))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_103 (x : Var) (z : Var) :
    (nb060_alpha_dummy_125 x z) ∉ (((Class.cv (nb060_alpha_dummy_118 x z))).fv) := by
  simpa only [nb060_alpha_dummy_125] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_118 x z))).fv) 0

theorem nb060_fresh_104 (x : Var) (z : Var) :
    (nb060_alpha_dummy_126 x z) ∉ (((Class.cv (nb060_alpha_dummy_118 x z))).fv) := by
  simpa only [nb060_alpha_dummy_126] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_118 x z))).fv) 1

theorem nb060_distinct_105 (x : Var) (z : Var) :
    (nb060_alpha_dummy_125 x z) ≠ (nb060_alpha_dummy_126 x z) := by
  simpa only [nb060_alpha_dummy_125, nb060_alpha_dummy_126] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_118 x z))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb060_fresh_106 :
    (nb060_alpha_dummy_129) ∉
      (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_129] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_107 :
    (nb060_alpha_dummy_130) ∉
      (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_130] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_108 :
    (nb060_alpha_dummy_131) ∉
      (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_131] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_109 : (nb060_alpha_dummy_129) ≠ (nb060_alpha_dummy_130) := by
  simpa only [nb060_alpha_dummy_129, nb060_alpha_dummy_130] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb060_distinct_110 : (nb060_alpha_dummy_129) ≠ (nb060_alpha_dummy_131) := by
  simpa only [nb060_alpha_dummy_129, nb060_alpha_dummy_131] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb060_distinct_111 : (nb060_alpha_dummy_130) ≠ (nb060_alpha_dummy_131) := by
  simpa only [nb060_alpha_dummy_130, nb060_alpha_dummy_131] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb060_fresh_112 (x : Var) (z : Var) :
    (nb060_alpha_dummy_132 x z) ∉
      (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_132] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_113 (x : Var) (z : Var) :
    (nb060_alpha_dummy_133 x z) ∉
      (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_133] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_114 (x : Var) (z : Var) :
    (nb060_alpha_dummy_134 x z) ∉
      (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb060_alpha_dummy_134] using
    freshVar_not_mem (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_115 (x : Var) (z : Var) :
    (nb060_alpha_dummy_132 x z) ≠ (nb060_alpha_dummy_133 x z) := by
  simpa only [nb060_alpha_dummy_132, nb060_alpha_dummy_133] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_distinct_116 (x : Var) (z : Var) :
    (nb060_alpha_dummy_132 x z) ≠ (nb060_alpha_dummy_134 x z) := by
  simpa only [nb060_alpha_dummy_132, nb060_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb060_distinct_117 (x : Var) (z : Var) :
    (nb060_alpha_dummy_133 x z) ≠ (nb060_alpha_dummy_134 x z) := by
  simpa only [nb060_alpha_dummy_133, nb060_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb060_fresh_118 :
    (nb060_alpha_dummy_141) ∉
      (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_130))).fv) :=
  by
  simpa only [nb060_alpha_dummy_141] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_130))).fv)
      0

theorem nb060_fresh_119 :
    (nb060_alpha_dummy_137) ∉
      (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) :=
  by
  simpa only [nb060_alpha_dummy_137] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv)
      0

theorem nb060_fresh_120 :
    (nb060_alpha_dummy_143) ∉
      (((Class.cv (nb060_alpha_dummy_131))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) :=
  by
  simpa only [nb060_alpha_dummy_143] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_131))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv)
      0

theorem nb060_fresh_121 (x : Var) (z : Var) :
    (nb060_alpha_dummy_142 x z) ∉
      (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_133 x z))).fv) :=
  by
  simpa only [nb060_alpha_dummy_142] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_133 x z))).fv)
      0

theorem nb060_fresh_122 (x : Var) (z : Var) :
    (nb060_alpha_dummy_138 x z) ∉
      (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_134 x z))).fv) :=
  by
  simpa only [nb060_alpha_dummy_138] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_134 x z))).fv)
      0

theorem nb060_fresh_123 (x : Var) (z : Var) :
    (nb060_alpha_dummy_144 x z) ∉
      (((Class.cv (nb060_alpha_dummy_134 x z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_134 x z))).fv) :=
  by
  simpa only [nb060_alpha_dummy_144] using
    freshVar_not_mem
      (((Class.cv (nb060_alpha_dummy_134 x z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_134 x z))).fv)
      0

theorem nb060_fresh_124 (r : Var) (a : Var) :
    (nb060_alpha_dummy_009 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb060_alpha_dummy_009] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb060_fresh_125 (r : Var) (a : Var) :
    (nb060_alpha_dummy_010 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb060_alpha_dummy_010] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb060_distinct_126 (r : Var) (a : Var) :
    (nb060_alpha_dummy_009 r a) ≠ (nb060_alpha_dummy_010 r a) := by
  simpa only [nb060_alpha_dummy_009, nb060_alpha_dummy_010] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_127 (x : Var) (y : Var) :
    (nb060_alpha_dummy_045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb060_alpha_dummy_045] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb060_fresh_128 (x : Var) (y : Var) :
    (nb060_alpha_dummy_046 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb060_alpha_dummy_046] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb060_distinct_129 (x : Var) (y : Var) :
    (nb060_alpha_dummy_045 x y) ≠ (nb060_alpha_dummy_046 x y) := by
  simpa only [nb060_alpha_dummy_045, nb060_alpha_dummy_046] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_130 (x : Var) (z : Var) :
    (nb060_alpha_dummy_117 x z) ∉ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060_alpha_dummy_117] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 0

theorem nb060_fresh_131 (x : Var) (z : Var) :
    (nb060_alpha_dummy_118 x z) ∉ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060_alpha_dummy_118] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 1

theorem nb060_distinct_132 (x : Var) (z : Var) :
    (nb060_alpha_dummy_117 x z) ≠ (nb060_alpha_dummy_118 x z) := by
  simpa only [nb060_alpha_dummy_117, nb060_alpha_dummy_118] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_133 (y : Var) (z : Var) :
    (nb060_alpha_dummy_081 y z) ∉ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060_alpha_dummy_081] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0

theorem nb060_fresh_134 (y : Var) (z : Var) :
    (nb060_alpha_dummy_082 y z) ∉ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060_alpha_dummy_082] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 1

theorem nb060_distinct_135 (y : Var) (z : Var) :
    (nb060_alpha_dummy_081 y z) ≠ (nb060_alpha_dummy_082 y z) := by
  simpa only [nb060_alpha_dummy_081, nb060_alpha_dummy_082] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_136 :
    (nb060_alpha_dummy_019) ∉
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_015)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_015)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_015))).fv) :=
  by
  simpa only [nb060_alpha_dummy_019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_015)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_015)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_015))).fv)
      0

theorem nb060_fresh_137 (r : Var) (a : Var) :
    (nb060_alpha_dummy_020 r a) ∉
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_017 r a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_017 r a)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_017 r a))).fv) :=
  by
  simpa only [nb060_alpha_dummy_020] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_017 r a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_017 r a)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_017 r a))).fv)
      0

theorem nb060_fresh_138 :
    (nb060_alpha_dummy_055) ∉
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_051)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_051)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_051))).fv) :=
  by
  simpa only [nb060_alpha_dummy_055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_051)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_051)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_051))).fv)
      0

theorem nb060_fresh_139 (x : Var) (y : Var) :
    (nb060_alpha_dummy_056 x y) ∉
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_053 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_053 x y))).fv) :=
  by
  simpa only [nb060_alpha_dummy_056] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_053 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_053 x y))).fv)
      0

theorem nb060_fresh_140 :
    (nb060_alpha_dummy_091) ∉
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_087)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_087)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_087))).fv) :=
  by
  simpa only [nb060_alpha_dummy_091] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_087)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_087)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_087))).fv)
      0

theorem nb060_fresh_141 (y : Var) (z : Var) :
    (nb060_alpha_dummy_092 y z) ∉
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_089 y z)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_089 y z))).fv) :=
  by
  simpa only [nb060_alpha_dummy_092] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_089 y z)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_089 y z))).fv)
      0

theorem nb060_fresh_142 :
    (nb060_alpha_dummy_127) ∉
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_123)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_123)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_123))).fv) :=
  by
  simpa only [nb060_alpha_dummy_127] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_123)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_123)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_123))).fv)
      0

theorem nb060_fresh_143 (x : Var) (z : Var) :
    (nb060_alpha_dummy_128 x z) ∉
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_125 x z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_125 x z)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_125 x z))).fv) :=
  by
  simpa only [nb060_alpha_dummy_128] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_125 x z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_125 x z)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_125 x z))).fv)
      0

theorem nb060_fresh_144 :
    (nb060_alpha_dummy_011) ∉
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_007)
              (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_007)
              (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_007)
              (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_007)
              (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb060_fresh_145 (r : Var) (a : Var) :
    (nb060_alpha_dummy_012 r a) ∉
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a)
              (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_009 r a)
              (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_012] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a)
              (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_009 r a)
              (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb060_fresh_146 :
    (nb060_alpha_dummy_047) ∉
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_043)
              (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_044)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_043)
              (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_043)
              (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_044)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_043)
              (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb060_fresh_147 (x : Var) (y : Var) :
    (nb060_alpha_dummy_048 x y) ∉
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y)
              (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_045 x y)
              (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y)
              (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_045 x y)
              (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb060_fresh_148 :
    (nb060_alpha_dummy_083) ∉
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_079)
              (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_080)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_079)
              (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_083] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_079)
              (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_080)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_079)
              (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part003`. -/


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

theorem nb060_fresh_149 (y : Var) (z : Var) :
    (nb060_alpha_dummy_084 y z) ∉
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z)
              (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_081 y z)
              (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_084] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z)
              (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_081 y z)
              (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb060_fresh_150 :
    (nb060_alpha_dummy_119) ∉
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_115)
              (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_116)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_115)
              (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_119] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_115)
              (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_116)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_115)
              (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb060_fresh_151 (x : Var) (z : Var) :
    (nb060_alpha_dummy_120 x z) ∉
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z)
              (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_117 x z)
              (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_120] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z)
              (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_117 x z)
              (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb060_fresh_152 :
    (nb060_alpha_dummy_031) ∉
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_022)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_023)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_031] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_022)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_023)))).fv)
      0

theorem nb060_fresh_153 (r : Var) (a : Var) :
    (nb060_alpha_dummy_032 r a) ∉
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_025 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_026 r a)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_032] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_025 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_026 r a)))).fv)
      0

theorem nb060_fresh_154 :
    (nb060_alpha_dummy_067) ∉
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_058)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_059)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_067] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_058)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_059)))).fv)
      0

theorem nb060_fresh_155 (x : Var) (y : Var) :
    (nb060_alpha_dummy_068 x y) ∉
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_061 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_062 x y)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_068] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_061 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_062 x y)))).fv)
      0

theorem nb060_fresh_156 :
    (nb060_alpha_dummy_103) ∉
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_094)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_095)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_103] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_094)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_095)))).fv)
      0

theorem nb060_fresh_157 (y : Var) (z : Var) :
    (nb060_alpha_dummy_104 y z) ∉
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_097 y z)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_098 y z)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_104] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_097 y z)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_098 y z)))).fv)
      0

theorem nb060_fresh_158 :
    (nb060_alpha_dummy_139) ∉
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_130)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_131)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_139] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_130)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_131)))).fv)
      0

theorem nb060_fresh_159 (x : Var) (z : Var) :
    (nb060_alpha_dummy_140 x z) ∉
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_133 x z)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_134 x z)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_140] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_133 x z)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_134 x z)))).fv)
      0

theorem nb060_fresh_160 :
    (nb060_alpha_dummy_039) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_008))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_008))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb060_fresh_161 (r : Var) (a : Var) :
    (nb060_alpha_dummy_040 r a) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb060_fresh_162 :
    (nb060_alpha_dummy_075) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_044))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_075] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_044))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb060_fresh_163 (x : Var) (y : Var) :
    (nb060_alpha_dummy_076 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_076] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb060_fresh_164 :
    (nb060_alpha_dummy_111) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_080))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_111] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_080))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb060_fresh_165 (y : Var) (z : Var) :
    (nb060_alpha_dummy_112 y z) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_112] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb060_fresh_166 :
    (nb060_alpha_dummy_147) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_116))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_147] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_116))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb060_fresh_167 (x : Var) (z : Var) :
    (nb060_alpha_dummy_148 x z) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_148] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb060_fresh_168 :
    (nb060_alpha_dummy_027) ∉
      (((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_022))
            (Class.cv (nb060_alpha_dummy_023)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_027] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv)
      0

theorem nb060_fresh_169 (r : Var) (a : Var) :
    (nb060_alpha_dummy_028 r a) ∉
      (((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a))
            (Class.cv (nb060_alpha_dummy_026 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a))
            (Class.cv (nb060_alpha_dummy_026 r a)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a))
            (Class.cv (nb060_alpha_dummy_026 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a))
            (Class.cv (nb060_alpha_dummy_026 r a)))).fv)
      0

theorem nb060_fresh_170 :
    (nb060_alpha_dummy_063) ∉
      (((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_058))
            (Class.cv (nb060_alpha_dummy_059)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_063] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv)
      0

theorem nb060_fresh_171 (x : Var) (y : Var) :
    (nb060_alpha_dummy_064 x y) ∉
      (((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y))
            (Class.cv (nb060_alpha_dummy_062 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y))
            (Class.cv (nb060_alpha_dummy_062 x y)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_064] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y))
            (Class.cv (nb060_alpha_dummy_062 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y))
            (Class.cv (nb060_alpha_dummy_062 x y)))).fv)
      0

theorem nb060_fresh_172 :
    (nb060_alpha_dummy_099) ∉
      (((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_094))
            (Class.cv (nb060_alpha_dummy_095)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_099] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv)
      0

theorem nb060_fresh_173 (y : Var) (z : Var) :
    (nb060_alpha_dummy_100 y z) ∉
      (((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z))
            (Class.cv (nb060_alpha_dummy_098 y z)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z))
            (Class.cv (nb060_alpha_dummy_098 y z)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_100] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z))
            (Class.cv (nb060_alpha_dummy_098 y z)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z))
            (Class.cv (nb060_alpha_dummy_098 y z)))).fv)
      0

theorem nb060_fresh_174 :
    (nb060_alpha_dummy_135) ∉
      (((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_130))
            (Class.cv (nb060_alpha_dummy_131)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_135] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv)
      0

theorem nb060_fresh_175 (x : Var) (z : Var) :
    (nb060_alpha_dummy_136 x z) ∉
      (((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z))
            (Class.cv (nb060_alpha_dummy_134 x z)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z))
            (Class.cv (nb060_alpha_dummy_134 x z)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_136] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z))
            (Class.cv (nb060_alpha_dummy_134 x z)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z))
            (Class.cv (nb060_alpha_dummy_134 x z)))).fv)
      0

theorem nb060_fresh_176 :
    (nb060_alpha_dummy_041) ∉
      (((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv)
      0

theorem nb060_fresh_177 (r : Var) (a : Var) :
    (nb060_alpha_dummy_042 r a) ∉
      (((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv)
      0

theorem nb060_fresh_178 :
    (nb060_alpha_dummy_077) ∉
      (((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv)
      0

theorem nb060_fresh_179 (x : Var) (y : Var) :
    (nb060_alpha_dummy_078 x y) ∉
      (((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_078] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv)
      0

theorem nb060_fresh_180 :
    (nb060_alpha_dummy_113) ∉
      (((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_113] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv)
      0

theorem nb060_fresh_181 (y : Var) (z : Var) :
    (nb060_alpha_dummy_114 y z) ∉
      (((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_114] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv)
      0

theorem nb060_fresh_182 :
    (nb060_alpha_dummy_149) ∉
      (((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_149] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv)
      0

theorem nb060_fresh_183 (x : Var) (z : Var) :
    (nb060_alpha_dummy_150 x z) ∉
      (((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv) :=
  by
  simpa only [nb060_alpha_dummy_150] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv)
      0

theorem nb060_fresh_184 :
    (nb060_alpha_dummy_005) ∉
      (({(nb060_alpha_dummy_001)} : Finset Var) ∪ ({(nb060_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb060_alpha_dummy_002) (Class.cv (nb060_alpha_dummy_000))
            (syn_wral (nb060_alpha_dummy_003) (Class.cv (nb060_alpha_dummy_000))
              (syn_wral (nb060_alpha_dummy_004) (Class.cv (nb060_alpha_dummy_000)) (Wff.imp
                  (syn_wa (syn_wbr (Class.cv (nb060_alpha_dummy_002))
                      (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_003)))
                    (syn_wbr (Class.cv (nb060_alpha_dummy_003))
                      (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004))))
                  (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001))
                    (Class.cv (nb060_alpha_dummy_004)))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_005] using
    freshVar_not_mem
      (({(nb060_alpha_dummy_001)} : Finset Var) ∪ ({(nb060_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb060_alpha_dummy_002) (Class.cv (nb060_alpha_dummy_000))
            (syn_wral (nb060_alpha_dummy_003) (Class.cv (nb060_alpha_dummy_000))
              (syn_wral (nb060_alpha_dummy_004) (Class.cv (nb060_alpha_dummy_000)) (Wff.imp
                  (syn_wa (syn_wbr (Class.cv (nb060_alpha_dummy_002))
                      (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_003)))
                    (syn_wbr (Class.cv (nb060_alpha_dummy_003))
                      (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004))))
                  (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001))
                    (Class.cv (nb060_alpha_dummy_004)))))))).fv)
      0

theorem nb060_fresh_185 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) :
    (nb060_alpha_dummy_006 x y z r a) ∉
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
            (syn_wral y (Class.cv a) (syn_wral z (Class.cv a) (Wff.imp
                  (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y))
                    (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z)))
                  (syn_wbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) :=
  by
  simpa only [nb060_alpha_dummy_006] using
    freshVar_not_mem
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
            (syn_wral y (Class.cv a) (syn_wral z (Class.cv a) (Wff.imp
                  (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y))
                    (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z)))
                  (syn_wbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv)
      0

theorem nb060_fresh_186 : (nb060_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb060_fresh_187 : (nb060_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb060_fresh_188 : (nb060_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb060_fresh_189 : (nb060_alpha_dummy_003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060_alpha_dummy_003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb060_fresh_190 : (nb060_alpha_dummy_004) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060_alpha_dummy_004] using freshVar_not_mem ((∅ : Finset Var)) 4

theorem nb060_distinct_191 : (nb060_alpha_dummy_000) ≠ (nb060_alpha_dummy_001) := by
  simpa only [nb060_alpha_dummy_000, nb060_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb060_distinct_192 : (nb060_alpha_dummy_000) ≠ (nb060_alpha_dummy_002) := by
  simpa only [nb060_alpha_dummy_000, nb060_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb060_distinct_193 : (nb060_alpha_dummy_000) ≠ (nb060_alpha_dummy_003) := by
  simpa only [nb060_alpha_dummy_000, nb060_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb060_distinct_194 : (nb060_alpha_dummy_000) ≠ (nb060_alpha_dummy_004) := by
  simpa only [nb060_alpha_dummy_000, nb060_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 4) (by decide))

theorem nb060_distinct_195 : (nb060_alpha_dummy_001) ≠ (nb060_alpha_dummy_002) := by
  simpa only [nb060_alpha_dummy_001, nb060_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb060_distinct_196 : (nb060_alpha_dummy_001) ≠ (nb060_alpha_dummy_003) := by
  simpa only [nb060_alpha_dummy_001, nb060_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb060_distinct_197 : (nb060_alpha_dummy_001) ≠ (nb060_alpha_dummy_004) := by
  simpa only [nb060_alpha_dummy_001, nb060_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 4) (by decide))

theorem nb060_distinct_198 : (nb060_alpha_dummy_002) ≠ (nb060_alpha_dummy_003) := by
  simpa only [nb060_alpha_dummy_002, nb060_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb060_distinct_199 : (nb060_alpha_dummy_002) ≠ (nb060_alpha_dummy_004) := by
  simpa only [nb060_alpha_dummy_002, nb060_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 4) (by decide))

theorem nb060_distinct_200 : (nb060_alpha_dummy_003) ≠ (nb060_alpha_dummy_004) := by
  simpa only [nb060_alpha_dummy_003, nb060_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 3) (j := 4) (by decide))

theorem nb060_support_mem_0000 :
    (nb060_alpha_dummy_001) ∈
      (({(nb060_alpha_dummy_001)} : Finset Var) ∪ ({(nb060_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb060_alpha_dummy_002) (Class.cv (nb060_alpha_dummy_000))
            (syn_wral (nb060_alpha_dummy_003) (Class.cv (nb060_alpha_dummy_000))
              (syn_wral (nb060_alpha_dummy_004) (Class.cv (nb060_alpha_dummy_000)) (Wff.imp
                  (syn_wa (syn_wbr (Class.cv (nb060_alpha_dummy_002))
                      (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_003)))
                    (syn_wbr (Class.cv (nb060_alpha_dummy_003))
                      (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004))))
                  (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001))
                    (Class.cv (nb060_alpha_dummy_004)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0001 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) :
    r ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
            (syn_wral y (Class.cv a) (syn_wral z (Class.cv a) (Wff.imp
                  (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y))
                    (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z)))
                  (syn_wbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0002 :
    (nb060_alpha_dummy_000) ∈
      (({(nb060_alpha_dummy_001)} : Finset Var) ∪ ({(nb060_alpha_dummy_000)} : Finset Var) ∪
        ((syn_wral (nb060_alpha_dummy_002) (Class.cv (nb060_alpha_dummy_000))
            (syn_wral (nb060_alpha_dummy_003) (Class.cv (nb060_alpha_dummy_000))
              (syn_wral (nb060_alpha_dummy_004) (Class.cv (nb060_alpha_dummy_000)) (Wff.imp
                  (syn_wa (syn_wbr (Class.cv (nb060_alpha_dummy_002))
                      (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_003)))
                    (syn_wbr (Class.cv (nb060_alpha_dummy_003))
                      (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004))))
                  (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001))
                    (Class.cv (nb060_alpha_dummy_004)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0003 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) :
    a ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((syn_wral x (Class.cv a)
            (syn_wral y (Class.cv a) (syn_wral z (Class.cv a) (Wff.imp
                  (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y))
                    (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z)))
                  (syn_wbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0004 :
    (nb060_alpha_dummy_001) ∈
      (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0005 :
    (nb060_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_007)
              (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_007)
              (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0006 (r : Var) (a : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0007 (r : Var) (a : Var) :
    r ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a)
              (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_009 r a)
              (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0008 :
    (nb060_alpha_dummy_001) ∈
      (((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0009 (r : Var) (a : Var) :
    r ∈
      (((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0010 :
    (nb060_alpha_dummy_008) ∈ (((Class.cv (nb060_alpha_dummy_008))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0011 (r : Var) (a : Var) :
    (nb060_alpha_dummy_010 r a) ∈ (((Class.cv (nb060_alpha_dummy_010 r a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0012 :
    (nb060_alpha_dummy_015) ∈
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_015)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_015)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_015))).fv) :=
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

theorem nb060_support_mem_0013 (r : Var) (a : Var) :
    (nb060_alpha_dummy_017 r a) ∈
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_017 r a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_017 r a)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_017 r a))).fv) :=
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

theorem nb060_support_mem_0014 :
    (nb060_alpha_dummy_015) ∈
      (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0015 (r : Var) (a : Var) :
    (nb060_alpha_dummy_017 r a) ∈
      (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0016 :
    (nb060_alpha_dummy_022) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_022))
            (Class.cv (nb060_alpha_dummy_023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0017 (r : Var) (a : Var) :
    (nb060_alpha_dummy_025 r a) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a))
            (Class.cv (nb060_alpha_dummy_026 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a))
            (Class.cv (nb060_alpha_dummy_026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0018 :
    (nb060_alpha_dummy_022) ∈
      (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0019 (r : Var) (a : Var) :
    (nb060_alpha_dummy_025 r a) ∈
      (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪
        ((Class.cv (nb060_alpha_dummy_026 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0020 :
    (nb060_alpha_dummy_023) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_022))
            (Class.cv (nb060_alpha_dummy_023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0021 (r : Var) (a : Var) :
    (nb060_alpha_dummy_026 r a) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a))
            (Class.cv (nb060_alpha_dummy_026 r a)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a))
            (Class.cv (nb060_alpha_dummy_026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0022 :
    (nb060_alpha_dummy_023) ∈
      (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0023 (r : Var) (a : Var) :
    (nb060_alpha_dummy_026 r a) ∈
      (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪
        ((Class.cv (nb060_alpha_dummy_026 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0024 :
    (nb060_alpha_dummy_022) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_022)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0025 (r : Var) (a : Var) :
    (nb060_alpha_dummy_025 r a) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_025 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0026 :
    (nb060_alpha_dummy_022) ∈
      (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0027 (r : Var) (a : Var) :
    (nb060_alpha_dummy_025 r a) ∈
      (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪
        ((Class.cv (nb060_alpha_dummy_025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0028 :
    (nb060_alpha_dummy_023) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_022)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0029 (r : Var) (a : Var) :
    (nb060_alpha_dummy_026 r a) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_025 r a)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0030 :
    (nb060_alpha_dummy_023) ∈
      (((Class.cv (nb060_alpha_dummy_023))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0031 (r : Var) (a : Var) :
    (nb060_alpha_dummy_026 r a) ∈
      (((Class.cv (nb060_alpha_dummy_026 r a))).fv ∪
        ((Class.cv (nb060_alpha_dummy_026 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0032 :
    (nb060_alpha_dummy_000) ∈
      (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0033 :
    (nb060_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_007)
              (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_007)
              (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0034 (r : Var) (a : Var) :
    a ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0035 (r : Var) (a : Var) :
    a ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a)
              (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_009 r a)
              (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0036 :
    (nb060_alpha_dummy_000) ∈
      (((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007)
            (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0037 (r : Var) (a : Var) :
    a ∈
      (((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a)
            (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0038 :
    (nb060_alpha_dummy_008) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_008))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0039 (r : Var) (a : Var) :
    (nb060_alpha_dummy_010 r a) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0040 :
    (nb060_alpha_dummy_008) ∈
      (((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0041 (r : Var) (a : Var) :
    (nb060_alpha_dummy_010 r a) ∈
      (((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0042 :
    (nb060_alpha_dummy_002) ∈
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0043 :
    (nb060_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_043)
              (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_044)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_043)
              (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0044 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0045 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y)
              (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_045 x y)
              (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0046 :
    (nb060_alpha_dummy_002) ∈
      (((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0047 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0048 :
    (nb060_alpha_dummy_044) ∈ (((Class.cv (nb060_alpha_dummy_044))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0049 (x : Var) (y : Var) :
    (nb060_alpha_dummy_046 x y) ∈ (((Class.cv (nb060_alpha_dummy_046 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0050 :
    (nb060_alpha_dummy_051) ∈
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_051)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_051)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_051))).fv) :=
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

theorem nb060_support_mem_0051 (x : Var) (y : Var) :
    (nb060_alpha_dummy_053 x y) ∈
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_053 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_053 x y))).fv) :=
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

theorem nb060_support_mem_0052 :
    (nb060_alpha_dummy_051) ∈
      (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0053 (x : Var) (y : Var) :
    (nb060_alpha_dummy_053 x y) ∈
      (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0054 :
    (nb060_alpha_dummy_058) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_058))
            (Class.cv (nb060_alpha_dummy_059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0055 (x : Var) (y : Var) :
    (nb060_alpha_dummy_061 x y) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y))
            (Class.cv (nb060_alpha_dummy_062 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y))
            (Class.cv (nb060_alpha_dummy_062 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0056 :
    (nb060_alpha_dummy_058) ∈
      (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0057 (x : Var) (y : Var) :
    (nb060_alpha_dummy_061 x y) ∈
      (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb060_alpha_dummy_062 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0058 :
    (nb060_alpha_dummy_059) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_058))
            (Class.cv (nb060_alpha_dummy_059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0059 (x : Var) (y : Var) :
    (nb060_alpha_dummy_062 x y) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y))
            (Class.cv (nb060_alpha_dummy_062 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y))
            (Class.cv (nb060_alpha_dummy_062 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0060 :
    (nb060_alpha_dummy_059) ∈
      (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0061 (x : Var) (y : Var) :
    (nb060_alpha_dummy_062 x y) ∈
      (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb060_alpha_dummy_062 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0062 :
    (nb060_alpha_dummy_058) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_058)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0063 (x : Var) (y : Var) :
    (nb060_alpha_dummy_061 x y) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_061 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_062 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0064 :
    (nb060_alpha_dummy_058) ∈
      (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0065 (x : Var) (y : Var) :
    (nb060_alpha_dummy_061 x y) ∈
      (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb060_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0066 :
    (nb060_alpha_dummy_059) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_058)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0067 (x : Var) (y : Var) :
    (nb060_alpha_dummy_062 x y) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_061 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_062 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0068 :
    (nb060_alpha_dummy_059) ∈
      (((Class.cv (nb060_alpha_dummy_059))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0069 (x : Var) (y : Var) :
    (nb060_alpha_dummy_062 x y) ∈
      (((Class.cv (nb060_alpha_dummy_062 x y))).fv ∪
        ((Class.cv (nb060_alpha_dummy_062 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0070 :
    (nb060_alpha_dummy_003) ∈
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0071 :
    (nb060_alpha_dummy_003) ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_043)
              (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_044)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_043)
              (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0072 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0073 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y)
              (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_045 x y)
              (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0074 :
    (nb060_alpha_dummy_003) ∈
      (((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0075 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0076 :
    (nb060_alpha_dummy_044) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_044))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0077 (x : Var) (y : Var) :
    (nb060_alpha_dummy_046 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0078 :
    (nb060_alpha_dummy_044) ∈
      (((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0079 (x : Var) (y : Var) :
    (nb060_alpha_dummy_046 x y) ∈
      (((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0080 :
    (nb060_alpha_dummy_003) ∈
      (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0081 :
    (nb060_alpha_dummy_003) ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_079)
              (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_080)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_079)
              (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0082 (y : Var) (z : Var) :
    y ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0083 (y : Var) (z : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z)
              (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_081 y z)
              (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0084 :
    (nb060_alpha_dummy_003) ∈
      (((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part004`. -/


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

theorem nb060_support_mem_0085 (y : Var) (z : Var) :
    y ∈
      (((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0086 :
    (nb060_alpha_dummy_080) ∈ (((Class.cv (nb060_alpha_dummy_080))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0087 (y : Var) (z : Var) :
    (nb060_alpha_dummy_082 y z) ∈ (((Class.cv (nb060_alpha_dummy_082 y z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0088 :
    (nb060_alpha_dummy_087) ∈
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_087)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_087)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_087))).fv) :=
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

theorem nb060_support_mem_0089 (y : Var) (z : Var) :
    (nb060_alpha_dummy_089 y z) ∈
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_089 y z)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_089 y z))).fv) :=
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

theorem nb060_support_mem_0090 :
    (nb060_alpha_dummy_087) ∈
      (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0091 (y : Var) (z : Var) :
    (nb060_alpha_dummy_089 y z) ∈
      (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0092 :
    (nb060_alpha_dummy_094) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_094))
            (Class.cv (nb060_alpha_dummy_095)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0093 (y : Var) (z : Var) :
    (nb060_alpha_dummy_097 y z) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z))
            (Class.cv (nb060_alpha_dummy_098 y z)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z))
            (Class.cv (nb060_alpha_dummy_098 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0094 :
    (nb060_alpha_dummy_094) ∈
      (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0095 (y : Var) (z : Var) :
    (nb060_alpha_dummy_097 y z) ∈
      (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_098 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0096 :
    (nb060_alpha_dummy_095) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_094))
            (Class.cv (nb060_alpha_dummy_095)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0097 (y : Var) (z : Var) :
    (nb060_alpha_dummy_098 y z) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z))
            (Class.cv (nb060_alpha_dummy_098 y z)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z))
            (Class.cv (nb060_alpha_dummy_098 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0098 :
    (nb060_alpha_dummy_095) ∈
      (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0099 (y : Var) (z : Var) :
    (nb060_alpha_dummy_098 y z) ∈
      (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_098 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0100 :
    (nb060_alpha_dummy_094) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_094)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_095)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0101 (y : Var) (z : Var) :
    (nb060_alpha_dummy_097 y z) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_097 y z)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_098 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0102 :
    (nb060_alpha_dummy_094) ∈
      (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0103 (y : Var) (z : Var) :
    (nb060_alpha_dummy_097 y z) ∈
      (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_097 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0104 :
    (nb060_alpha_dummy_095) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_094)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_095)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0105 (y : Var) (z : Var) :
    (nb060_alpha_dummy_098 y z) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_097 y z)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_098 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0106 :
    (nb060_alpha_dummy_095) ∈
      (((Class.cv (nb060_alpha_dummy_095))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0107 (y : Var) (z : Var) :
    (nb060_alpha_dummy_098 y z) ∈
      (((Class.cv (nb060_alpha_dummy_098 y z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_098 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0108 :
    (nb060_alpha_dummy_004) ∈
      (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0109 :
    (nb060_alpha_dummy_004) ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_079)
              (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_080)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_079)
              (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0110 (y : Var) (z : Var) :
    z ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0111 (y : Var) (z : Var) :
    z ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z)
              (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_081 y z)
              (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0112 :
    (nb060_alpha_dummy_004) ∈
      (((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079)
            (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0113 (y : Var) (z : Var) :
    z ∈
      (((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z)
            (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0114 :
    (nb060_alpha_dummy_080) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_080))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0115 (y : Var) (z : Var) :
    (nb060_alpha_dummy_082 y z) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0116 :
    (nb060_alpha_dummy_080) ∈
      (((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0117 (y : Var) (z : Var) :
    (nb060_alpha_dummy_082 y z) ∈
      (((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0118 :
    (nb060_alpha_dummy_002) ∈
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0119 :
    (nb060_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_115)
              (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_116)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_115)
              (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0120 (x : Var) (z : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0121 (x : Var) (z : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z)
              (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_117 x z)
              (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0122 :
    (nb060_alpha_dummy_002) ∈
      (((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0123 (x : Var) (z : Var) :
    x ∈
      (((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv ∪
        ((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0124 :
    (nb060_alpha_dummy_116) ∈ (((Class.cv (nb060_alpha_dummy_116))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0125 (x : Var) (z : Var) :
    (nb060_alpha_dummy_118 x z) ∈ (((Class.cv (nb060_alpha_dummy_118 x z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0126 :
    (nb060_alpha_dummy_123) ∈
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_123)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_123)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_123))).fv) :=
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

theorem nb060_support_mem_0127 (x : Var) (z : Var) :
    (nb060_alpha_dummy_125 x z) ∈
      (((Wff.classMem (Class.cv (nb060_alpha_dummy_125 x z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb060_alpha_dummy_125 x z)) (syn_c1c))).fv ∪
        ((Class.cv (nb060_alpha_dummy_125 x z))).fv) :=
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

theorem nb060_support_mem_0128 :
    (nb060_alpha_dummy_123) ∈
      (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0129 (x : Var) (z : Var) :
    (nb060_alpha_dummy_125 x z) ∈
      (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0130 :
    (nb060_alpha_dummy_130) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_130))
            (Class.cv (nb060_alpha_dummy_131)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0131 (x : Var) (z : Var) :
    (nb060_alpha_dummy_133 x z) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z))
            (Class.cv (nb060_alpha_dummy_134 x z)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z))
            (Class.cv (nb060_alpha_dummy_134 x z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0132 :
    (nb060_alpha_dummy_130) ∈
      (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0133 (x : Var) (z : Var) :
    (nb060_alpha_dummy_133 x z) ∈
      (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_134 x z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0134 :
    (nb060_alpha_dummy_131) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_130))
            (Class.cv (nb060_alpha_dummy_131)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0135 (x : Var) (z : Var) :
    (nb060_alpha_dummy_134 x z) ∈
      (((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z))
            (Class.cv (nb060_alpha_dummy_134 x z)))).fv ∪
        ((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z))
            (Class.cv (nb060_alpha_dummy_134 x z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0136 :
    (nb060_alpha_dummy_131) ∈
      (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0137 (x : Var) (z : Var) :
    (nb060_alpha_dummy_134 x z) ∈
      (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_134 x z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0138 :
    (nb060_alpha_dummy_130) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_130)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_131)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0139 (x : Var) (z : Var) :
    (nb060_alpha_dummy_133 x z) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_133 x z)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_134 x z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0140 :
    (nb060_alpha_dummy_130) ∈
      (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_130))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0141 (x : Var) (z : Var) :
    (nb060_alpha_dummy_133 x z) ∈
      (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_133 x z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0142 :
    (nb060_alpha_dummy_131) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_130)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_131)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0143 (x : Var) (z : Var) :
    (nb060_alpha_dummy_134 x z) ∈
      (((syn_ccompl (Class.cv (nb060_alpha_dummy_133 x z)))).fv ∪
        ((syn_ccompl (Class.cv (nb060_alpha_dummy_134 x z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0144 :
    (nb060_alpha_dummy_131) ∈
      (((Class.cv (nb060_alpha_dummy_131))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0145 (x : Var) (z : Var) :
    (nb060_alpha_dummy_134 x z) ∈
      (((Class.cv (nb060_alpha_dummy_134 x z))).fv ∪
        ((Class.cv (nb060_alpha_dummy_134 x z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0146 :
    (nb060_alpha_dummy_004) ∈
      (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0147 :
    (nb060_alpha_dummy_004) ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_115)
              (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_116)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_115)
              (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0148 (x : Var) (z : Var) :
    z ∈ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0149 (x : Var) (z : Var) :
    z ∈
      (((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z)
              (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                  (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb060_alpha_dummy_117 x z)
              (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0150 :
    (nb060_alpha_dummy_004) ∈
      (((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115)
            (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0151 (x : Var) (z : Var) :
    z ∈
      (((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z)
            (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0152 :
    (nb060_alpha_dummy_116) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_116))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0153 (x : Var) (z : Var) :
    (nb060_alpha_dummy_118 x z) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0154 :
    (nb060_alpha_dummy_116) ∈
      (((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0155 (x : Var) (z : Var) :
    (nb060_alpha_dummy_118 x z) ∈
      (((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv ∪
        ((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
