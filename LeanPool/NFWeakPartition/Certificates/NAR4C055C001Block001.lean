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

/-! Certificates from `NAR4C055C001Part001`. -/


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
noncomputable def nb055_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb055_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb055_alpha_dummy_002 : Var :=
  (freshVar (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
          ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
      ((syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_003 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
      ((syn_ccom (Class.cv x) (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_004 : Var :=
  (freshVar
    (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪
        ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv))
            (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv)))
          (Wff.classEq (Class.cv (nb055_alpha_dummy_002))
            (syn_ccom (Class.cv (nb055_alpha_dummy_000))
              (Class.cv (nb055_alpha_dummy_001)))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_005 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
          (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y))
            (syn_ccom (Class.cv x) (Class.cv y))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_006 : Var :=
  (freshVar (((syn_cop (Class.cv (nb055_alpha_dummy_000))
          (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_007 : Var :=
  (freshVar (((syn_cop (Class.cv (nb055_alpha_dummy_000))
          (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_008 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_003 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_009 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_003 x y))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_010 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
              (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb055_alpha_dummy_006)
            (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_011 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_012 : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
            (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
              (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv ∪
      ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
            (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
              (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_008 x y)
          (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
              (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv ∪
      ((Class.cab (nb055_alpha_dummy_008 x y)
          (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
              (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_014 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_015 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_018 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cphi (Class.cv (nb055_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_019 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_020 : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_014)
          (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
              (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv ∪
      ((Class.cab (nb055_alpha_dummy_014)
          (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
              (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_016 x y)
          (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
              (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv ∪
      ((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
              (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_022 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_015))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_023 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_015))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_017 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_017 x y))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_026 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_022)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb055_alpha_dummy_022)) (syn_c1c))).fv ∪
      ((Class.cv (nb055_alpha_dummy_022))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_027 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb055_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb055_alpha_dummy_024 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_028 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_029 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_030 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_034 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_029))
          (Class.cv (nb055_alpha_dummy_030)))).fv ∪
      ((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_035 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y))
          (Class.cv (nb055_alpha_dummy_033 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y))
          (Class.cv (nb055_alpha_dummy_033 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_036 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_037 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_033 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_038 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_029)))).fv ∪
      ((syn_ccompl (Class.cv (nb055_alpha_dummy_030)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_039 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_032 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb055_alpha_dummy_033 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_040 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_029))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_041 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_032 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_042 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_030))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_043 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_033 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_033 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_044 : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_014)
          (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014)
          (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_016 x y)
          (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y)
          (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_046 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_015))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_047 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_048 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv ∪
      ((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_049 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_050 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_007))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_051 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_007))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_009 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_009 x y))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_050)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb055_alpha_dummy_050)) (syn_c1c))).fv ∪
      ((Class.cv (nb055_alpha_dummy_050))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb055_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb055_alpha_dummy_052 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_056 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_057 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_058 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_062 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_057))
          (Class.cv (nb055_alpha_dummy_058)))).fv ∪
      ((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_063 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y))
          (Class.cv (nb055_alpha_dummy_061 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y))
          (Class.cv (nb055_alpha_dummy_061 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_064 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_061 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_066 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_057)))).fv ∪
      ((syn_ccompl (Class.cv (nb055_alpha_dummy_058)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_067 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_060 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb055_alpha_dummy_061 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_068 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_057))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_060 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_070 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_058))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_061 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_061 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_072 : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_006)
          (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006)
          (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_008 x y)
          (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y)
          (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_074 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_007))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_075 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_076 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv ∪
      ((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_077 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_078 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_079 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_080 : Var :=
  (freshVar
    (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪
      ((syn_wex (nb055_alpha_dummy_078) (syn_wa
            (syn_wbr (Class.cv (nb055_alpha_dummy_014)) (Class.cv (nb055_alpha_dummy_001))
              (Class.cv (nb055_alpha_dummy_078)))
            (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000))
              (Class.cv (nb055_alpha_dummy_015)))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_081 (x : Var) (y : Var) : Var :=
  (freshVar (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪
        ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y)
          (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y)
              (Class.cv (nb055_alpha_dummy_079 x y)))
            (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x)
              (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_082 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_083 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_084 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_085 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_086 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cphi (Class.cv (nb055_alpha_dummy_083)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_087 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_088 : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_082)
          (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
              (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv ∪
      ((Class.cab (nb055_alpha_dummy_082)
          (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
              (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_089 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_084 x y)
          (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
              (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv ∪
      ((Class.cab (nb055_alpha_dummy_084 x y)
          (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
              (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_090 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_083))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_091 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_083))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_092 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_085 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_093 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_085 x y))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_094 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_090)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb055_alpha_dummy_090)) (syn_c1c))).fv ∪
      ((Class.cv (nb055_alpha_dummy_090))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_095 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_092 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb055_alpha_dummy_092 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb055_alpha_dummy_092 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_096 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_097 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_098 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_099 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_100 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_101 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_102 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_097))
          (Class.cv (nb055_alpha_dummy_098)))).fv ∪
      ((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_103 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y))
          (Class.cv (nb055_alpha_dummy_101 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y))
          (Class.cv (nb055_alpha_dummy_101 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_104 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_105 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_101 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_106 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_097)))).fv ∪
      ((syn_ccompl (Class.cv (nb055_alpha_dummy_098)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_107 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_100 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb055_alpha_dummy_101 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_108 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_097))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_109 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_100 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_110 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_098))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_111 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_101 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_101 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_112 : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_082)
          (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082)
          (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_113 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_084 x y)
          (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y)
          (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_114 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_083))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_115 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_116 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv ∪
      ((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_117 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_118 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_119 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_120 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_079 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_121 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_079 x y))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_122 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cphi (Class.cv (nb055_alpha_dummy_119)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_123 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_124 : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_118)
          (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
              (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv ∪
      ((Class.cab (nb055_alpha_dummy_118)
          (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
              (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_125 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_120 x y)
          (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
              (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv ∪
      ((Class.cab (nb055_alpha_dummy_120 x y)
          (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
              (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_126 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_119))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_127 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_119))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_128 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_121 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_129 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_121 x y))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_130 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_126)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb055_alpha_dummy_126)) (syn_c1c))).fv ∪
      ((Class.cv (nb055_alpha_dummy_126))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_131 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb055_alpha_dummy_128 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb055_alpha_dummy_128 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_132 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_133 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_134 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_135 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_136 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_137 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_138 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_133))
          (Class.cv (nb055_alpha_dummy_134)))).fv ∪
      ((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_139 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y))
          (Class.cv (nb055_alpha_dummy_137 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y))
          (Class.cv (nb055_alpha_dummy_137 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_140 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_141 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_137 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_142 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_133)))).fv ∪
      ((syn_ccompl (Class.cv (nb055_alpha_dummy_134)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_143 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_136 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb055_alpha_dummy_137 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_144 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_133))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_145 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_136 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_146 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_134))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_147 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_137 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_137 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_148 : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_118)
          (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118)
          (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_149 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_120 x y)
          (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y)
          (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part002`. -/


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
noncomputable def nb055_alpha_dummy_150 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_119))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_151 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_152 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv ∪
      ((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_153 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_154 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_155 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_156 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_157 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_158 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cphi (Class.cv (nb055_alpha_dummy_155)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_159 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_160 : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_154)
          (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
              (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv ∪
      ((Class.cab (nb055_alpha_dummy_154)
          (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
              (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_161 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_156 x y)
          (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
              (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv ∪
      ((Class.cab (nb055_alpha_dummy_156 x y)
          (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
              (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_162 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_155))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_163 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_155))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_164 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_157 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_165 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_157 x y))).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_166 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_162)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb055_alpha_dummy_162)) (syn_c1c))).fv ∪
      ((Class.cv (nb055_alpha_dummy_162))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_167 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_164 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb055_alpha_dummy_164 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb055_alpha_dummy_164 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_168 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_169 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_170 : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_171 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_172 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb055_alpha_dummy_173 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb055_alpha_dummy_174 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_169))
          (Class.cv (nb055_alpha_dummy_170)))).fv ∪
      ((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_175 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y))
          (Class.cv (nb055_alpha_dummy_173 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y))
          (Class.cv (nb055_alpha_dummy_173 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_176 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_177 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_173 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_178 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_169)))).fv ∪
      ((syn_ccompl (Class.cv (nb055_alpha_dummy_170)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_179 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_172 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb055_alpha_dummy_173 x y)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_180 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_169))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_181 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_172 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_182 : Var :=
  (freshVar
    (((Class.cv (nb055_alpha_dummy_170))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_183 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055_alpha_dummy_173 x y))).fv ∪
      ((Class.cv (nb055_alpha_dummy_173 x y))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_184 : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_154)
          (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154)
          (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_185 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055_alpha_dummy_156 x y)
          (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y)
          (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
              (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_186 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_155))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_187 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_188 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv ∪
      ((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv) 0)

@[expose]
noncomputable def nb055_alpha_dummy_189 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv) 0)

theorem nb055_fresh_000 :
    (nb055_alpha_dummy_072) ∉
      (((Class.cab (nb055_alpha_dummy_006)
            (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006)
            (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_006)
            (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006)
            (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb055_fresh_001 :
    (nb055_alpha_dummy_012) ∉
      (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
              (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
              (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
              (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
              (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv)
      0

theorem nb055_fresh_002 (x : Var) (y : Var) :
    (nb055_alpha_dummy_073 x y) ∉
      (((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb055_fresh_003 (x : Var) (y : Var) :
    (nb055_alpha_dummy_013 x y) ∉
      (((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_013] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv)
      0

theorem nb055_fresh_004 :
    (nb055_alpha_dummy_020) ∉
      (((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_020] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv)
      0

theorem nb055_fresh_005 :
    (nb055_alpha_dummy_044) ∉
      (((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb055_fresh_006 (x : Var) (y : Var) :
    (nb055_alpha_dummy_021 x y) ∉
      (((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_021] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv)
      0

theorem nb055_fresh_007 (x : Var) (y : Var) :
    (nb055_alpha_dummy_045 x y) ∉
      (((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb055_fresh_008 :
    (nb055_alpha_dummy_088) ∉
      (((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_088] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv)
      0

theorem nb055_fresh_009 :
    (nb055_alpha_dummy_112) ∉
      (((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_112] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb055_fresh_010 (x : Var) (y : Var) :
    (nb055_alpha_dummy_089 x y) ∉
      (((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_089] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv)
      0

theorem nb055_fresh_011 (x : Var) (y : Var) :
    (nb055_alpha_dummy_113 x y) ∉
      (((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_113] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb055_fresh_012 :
    (nb055_alpha_dummy_124) ∉
      (((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_124] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv)
      0

theorem nb055_fresh_013 :
    (nb055_alpha_dummy_148) ∉
      (((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_148] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb055_fresh_014 (x : Var) (y : Var) :
    (nb055_alpha_dummy_125 x y) ∉
      (((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_125] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv)
      0

theorem nb055_fresh_015 (x : Var) (y : Var) :
    (nb055_alpha_dummy_149 x y) ∉
      (((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_149] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb055_fresh_016 :
    (nb055_alpha_dummy_184) ∉
      (((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_184] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb055_fresh_017 :
    (nb055_alpha_dummy_160) ∉
      (((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_160] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv)
      0

theorem nb055_fresh_018 (x : Var) (y : Var) :
    (nb055_alpha_dummy_185 x y) ∉
      (((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_185] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb055_fresh_019 (x : Var) (y : Var) :
    (nb055_alpha_dummy_161 x y) ∉
      (((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_161] using
    freshVar_not_mem
      (((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv)
      0

theorem nb055_fresh_020 :
    (nb055_alpha_dummy_014) ∉
      (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) :=
  by
  simpa only [nb055_alpha_dummy_014] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv)
      0

theorem nb055_fresh_021 :
    (nb055_alpha_dummy_015) ∉
      (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) :=
  by
  simpa only [nb055_alpha_dummy_015] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv)
      1

theorem nb055_fresh_022 :
    (nb055_alpha_dummy_078) ∉
      (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) :=
  by
  simpa only [nb055_alpha_dummy_078] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv)
      2

theorem nb055_distinct_023 : (nb055_alpha_dummy_014) ≠ (nb055_alpha_dummy_015) := by
  simpa only [nb055_alpha_dummy_014, nb055_alpha_dummy_015] using
    (freshVar_injective
      (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_024 : (nb055_alpha_dummy_014) ≠ (nb055_alpha_dummy_078) := by
  simpa only [nb055_alpha_dummy_014, nb055_alpha_dummy_078] using
    (freshVar_injective
      (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_025 : (nb055_alpha_dummy_015) ≠ (nb055_alpha_dummy_078) := by
  simpa only [nb055_alpha_dummy_015, nb055_alpha_dummy_078] using
    (freshVar_injective
      (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb055_fresh_026 :
    (nb055_alpha_dummy_050) ∉ (((Class.cv (nb055_alpha_dummy_007))).fv) := by
  simpa only [nb055_alpha_dummy_050] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_007))).fv) 0

theorem nb055_fresh_027 :
    (nb055_alpha_dummy_051) ∉ (((Class.cv (nb055_alpha_dummy_007))).fv) := by
  simpa only [nb055_alpha_dummy_051] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_007))).fv) 1

theorem nb055_distinct_028 : (nb055_alpha_dummy_050) ≠ (nb055_alpha_dummy_051) := by
  simpa only [nb055_alpha_dummy_050, nb055_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_007))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_029 (x : Var) (y : Var) :
    (nb055_alpha_dummy_052 x y) ∉ (((Class.cv (nb055_alpha_dummy_009 x y))).fv) := by
  simpa only [nb055_alpha_dummy_052] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_009 x y))).fv) 0

theorem nb055_fresh_030 (x : Var) (y : Var) :
    (nb055_alpha_dummy_053 x y) ∉ (((Class.cv (nb055_alpha_dummy_009 x y))).fv) := by
  simpa only [nb055_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_009 x y))).fv) 1

theorem nb055_distinct_031 (x : Var) (y : Var) :
    (nb055_alpha_dummy_052 x y) ≠ (nb055_alpha_dummy_053 x y) := by
  simpa only [nb055_alpha_dummy_052, nb055_alpha_dummy_053] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_009 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb055_fresh_032 :
    (nb055_alpha_dummy_082) ∉
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) :=
  by
  simpa only [nb055_alpha_dummy_082] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv)
      0

theorem nb055_fresh_033 :
    (nb055_alpha_dummy_083) ∉
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) :=
  by
  simpa only [nb055_alpha_dummy_083] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv)
      1

theorem nb055_distinct_034 : (nb055_alpha_dummy_082) ≠ (nb055_alpha_dummy_083) := by
  simpa only [nb055_alpha_dummy_082, nb055_alpha_dummy_083] using
    (freshVar_injective
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_fresh_035 :
    (nb055_alpha_dummy_118) ∉
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) :=
  by
  simpa only [nb055_alpha_dummy_118] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv)
      0

theorem nb055_fresh_036 :
    (nb055_alpha_dummy_119) ∉
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) :=
  by
  simpa only [nb055_alpha_dummy_119] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv)
      1

theorem nb055_distinct_037 : (nb055_alpha_dummy_118) ≠ (nb055_alpha_dummy_119) := by
  simpa only [nb055_alpha_dummy_118, nb055_alpha_dummy_119] using
    (freshVar_injective
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_fresh_038 :
    (nb055_alpha_dummy_022) ∉ (((Class.cv (nb055_alpha_dummy_015))).fv) := by
  simpa only [nb055_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_015))).fv) 0

theorem nb055_fresh_039 :
    (nb055_alpha_dummy_023) ∉ (((Class.cv (nb055_alpha_dummy_015))).fv) := by
  simpa only [nb055_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_015))).fv) 1

theorem nb055_distinct_040 : (nb055_alpha_dummy_022) ≠ (nb055_alpha_dummy_023) := by
  simpa only [nb055_alpha_dummy_022, nb055_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_015))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_041 (x : Var) (y : Var) :
    (nb055_alpha_dummy_084 x y) ∉
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_084] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv)
      0

theorem nb055_fresh_042 (x : Var) (y : Var) :
    (nb055_alpha_dummy_085 x y) ∉
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_085] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv)
      1

theorem nb055_distinct_043 (x : Var) (y : Var) :
    (nb055_alpha_dummy_084 x y) ≠ (nb055_alpha_dummy_085 x y) := by
  simpa only [nb055_alpha_dummy_084, nb055_alpha_dummy_085] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_044 (x : Var) (y : Var) :
    (nb055_alpha_dummy_120 x y) ∉
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_079 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_120] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_079 x y))).fv)
      0

theorem nb055_fresh_045 (x : Var) (y : Var) :
    (nb055_alpha_dummy_121 x y) ∉
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_079 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_121] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_079 x y))).fv)
      1

theorem nb055_distinct_046 (x : Var) (y : Var) :
    (nb055_alpha_dummy_120 x y) ≠ (nb055_alpha_dummy_121 x y) := by
  simpa only [nb055_alpha_dummy_120, nb055_alpha_dummy_121] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_079 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_047 (x : Var) (y : Var) :
    (nb055_alpha_dummy_024 x y) ∉ (((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  simpa only [nb055_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_017 x y))).fv) 0

theorem nb055_fresh_048 (x : Var) (y : Var) :
    (nb055_alpha_dummy_025 x y) ∉ (((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  simpa only [nb055_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_017 x y))).fv) 1

theorem nb055_distinct_049 (x : Var) (y : Var) :
    (nb055_alpha_dummy_024 x y) ≠ (nb055_alpha_dummy_025 x y) := by
  simpa only [nb055_alpha_dummy_024, nb055_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_017 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb055_fresh_050 :
    (nb055_alpha_dummy_028) ∉
      (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_028] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_051 :
    (nb055_alpha_dummy_029) ∉
      (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_029] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_052 :
    (nb055_alpha_dummy_030) ∉
      (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_030] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_053 : (nb055_alpha_dummy_028) ≠ (nb055_alpha_dummy_029) := by
  simpa only [nb055_alpha_dummy_028, nb055_alpha_dummy_029] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb055_distinct_054 : (nb055_alpha_dummy_028) ≠ (nb055_alpha_dummy_030) := by
  simpa only [nb055_alpha_dummy_028, nb055_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb055_distinct_055 : (nb055_alpha_dummy_029) ≠ (nb055_alpha_dummy_030) := by
  simpa only [nb055_alpha_dummy_029, nb055_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb055_fresh_056 (x : Var) (y : Var) :
    (nb055_alpha_dummy_031 x y) ∉
      (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_031] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_057 (x : Var) (y : Var) :
    (nb055_alpha_dummy_032 x y) ∉
      (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_032] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_058 (x : Var) (y : Var) :
    (nb055_alpha_dummy_033 x y) ∉
      (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_033] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_059 (x : Var) (y : Var) :
    (nb055_alpha_dummy_031 x y) ≠ (nb055_alpha_dummy_032 x y) := by
  simpa only [nb055_alpha_dummy_031, nb055_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_060 (x : Var) (y : Var) :
    (nb055_alpha_dummy_031 x y) ≠ (nb055_alpha_dummy_033 x y) := by
  simpa only [nb055_alpha_dummy_031, nb055_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_061 (x : Var) (y : Var) :
    (nb055_alpha_dummy_032 x y) ≠ (nb055_alpha_dummy_033 x y) := by
  simpa only [nb055_alpha_dummy_032, nb055_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb055_fresh_062 :
    (nb055_alpha_dummy_040) ∉
      (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_029))).fv) :=
  by
  simpa only [nb055_alpha_dummy_040] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_029))).fv)
      0

theorem nb055_fresh_063 :
    (nb055_alpha_dummy_036) ∉
      (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) :=
  by
  simpa only [nb055_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv)
      0

theorem nb055_fresh_064 :
    (nb055_alpha_dummy_042) ∉
      (((Class.cv (nb055_alpha_dummy_030))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) :=
  by
  simpa only [nb055_alpha_dummy_042] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_030))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv)
      0

theorem nb055_fresh_065 (x : Var) (y : Var) :
    (nb055_alpha_dummy_041 x y) ∉
      (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_032 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_041] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_032 x y))).fv)
      0

theorem nb055_fresh_066 (x : Var) (y : Var) :
    (nb055_alpha_dummy_037 x y) ∉
      (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_033 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_033 x y))).fv)
      0

theorem nb055_fresh_067 (x : Var) (y : Var) :
    (nb055_alpha_dummy_043 x y) ∉
      (((Class.cv (nb055_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_033 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_033 x y))).fv)
      0

theorem nb055_fresh_068 :
    (nb055_alpha_dummy_056) ∉
      (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_056] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_069 :
    (nb055_alpha_dummy_057) ∉
      (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_057] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_070 :
    (nb055_alpha_dummy_058) ∉
      (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_071 : (nb055_alpha_dummy_056) ≠ (nb055_alpha_dummy_057) := by
  simpa only [nb055_alpha_dummy_056, nb055_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb055_distinct_072 : (nb055_alpha_dummy_056) ≠ (nb055_alpha_dummy_058) := by
  simpa only [nb055_alpha_dummy_056, nb055_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb055_distinct_073 : (nb055_alpha_dummy_057) ≠ (nb055_alpha_dummy_058) := by
  simpa only [nb055_alpha_dummy_057, nb055_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb055_fresh_074 (x : Var) (y : Var) :
    (nb055_alpha_dummy_059 x y) ∉
      (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_075 (x : Var) (y : Var) :
    (nb055_alpha_dummy_060 x y) ∉
      (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_076 (x : Var) (y : Var) :
    (nb055_alpha_dummy_061 x y) ∉
      (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_077 (x : Var) (y : Var) :
    (nb055_alpha_dummy_059 x y) ≠ (nb055_alpha_dummy_060 x y) := by
  simpa only [nb055_alpha_dummy_059, nb055_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_078 (x : Var) (y : Var) :
    (nb055_alpha_dummy_059 x y) ≠ (nb055_alpha_dummy_061 x y) := by
  simpa only [nb055_alpha_dummy_059, nb055_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_079 (x : Var) (y : Var) :
    (nb055_alpha_dummy_060 x y) ≠ (nb055_alpha_dummy_061 x y) := by
  simpa only [nb055_alpha_dummy_060, nb055_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb055_fresh_080 :
    (nb055_alpha_dummy_068) ∉
      (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_057))).fv) :=
  by
  simpa only [nb055_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_057))).fv)
      0

theorem nb055_fresh_081 :
    (nb055_alpha_dummy_064) ∉
      (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) :=
  by
  simpa only [nb055_alpha_dummy_064] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv)
      0

theorem nb055_fresh_082 :
    (nb055_alpha_dummy_070) ∉
      (((Class.cv (nb055_alpha_dummy_058))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) :=
  by
  simpa only [nb055_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_058))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv)
      0

theorem nb055_fresh_083 (x : Var) (y : Var) :
    (nb055_alpha_dummy_069 x y) ∉
      (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_060 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_060 x y))).fv)
      0

theorem nb055_fresh_084 (x : Var) (y : Var) :
    (nb055_alpha_dummy_065 x y) ∉
      (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_061 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_065] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_061 x y))).fv)
      0

theorem nb055_fresh_085 (x : Var) (y : Var) :
    (nb055_alpha_dummy_071 x y) ∉
      (((Class.cv (nb055_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_061 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_061 x y))).fv)
      0

theorem nb055_fresh_086 :
    (nb055_alpha_dummy_154) ∉
      (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) :=
  by
  simpa only [nb055_alpha_dummy_154] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv)
      0

theorem nb055_fresh_087 :
    (nb055_alpha_dummy_155) ∉
      (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) :=
  by
  simpa only [nb055_alpha_dummy_155] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv)
      1

theorem nb055_distinct_088 : (nb055_alpha_dummy_154) ≠ (nb055_alpha_dummy_155) := by
  simpa only [nb055_alpha_dummy_154, nb055_alpha_dummy_155] using
    (freshVar_injective
      (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_fresh_089 (x : Var) (y : Var) :
    (nb055_alpha_dummy_156 x y) ∉
      (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_156] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv)
      0

theorem nb055_fresh_090 (x : Var) (y : Var) :
    (nb055_alpha_dummy_157 x y) ∉
      (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_157] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv)
      1

theorem nb055_distinct_091 (x : Var) (y : Var) :
    (nb055_alpha_dummy_156 x y) ≠ (nb055_alpha_dummy_157 x y) := by
  simpa only [nb055_alpha_dummy_156, nb055_alpha_dummy_157] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_092 :
    (nb055_alpha_dummy_090) ∉ (((Class.cv (nb055_alpha_dummy_083))).fv) := by
  simpa only [nb055_alpha_dummy_090] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_083))).fv) 0

theorem nb055_fresh_093 :
    (nb055_alpha_dummy_091) ∉ (((Class.cv (nb055_alpha_dummy_083))).fv) := by
  simpa only [nb055_alpha_dummy_091] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_083))).fv) 1

theorem nb055_distinct_094 : (nb055_alpha_dummy_090) ≠ (nb055_alpha_dummy_091) := by
  simpa only [nb055_alpha_dummy_090, nb055_alpha_dummy_091] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_083))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_095 (x : Var) (y : Var) :
    (nb055_alpha_dummy_092 x y) ∉ (((Class.cv (nb055_alpha_dummy_085 x y))).fv) := by
  simpa only [nb055_alpha_dummy_092] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_085 x y))).fv) 0

theorem nb055_fresh_096 (x : Var) (y : Var) :
    (nb055_alpha_dummy_093 x y) ∉ (((Class.cv (nb055_alpha_dummy_085 x y))).fv) := by
  simpa only [nb055_alpha_dummy_093] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_085 x y))).fv) 1

theorem nb055_distinct_097 (x : Var) (y : Var) :
    (nb055_alpha_dummy_092 x y) ≠ (nb055_alpha_dummy_093 x y) := by
  simpa only [nb055_alpha_dummy_092, nb055_alpha_dummy_093] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_085 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb055_fresh_098 :
    (nb055_alpha_dummy_096) ∉
      (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_096] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_099 :
    (nb055_alpha_dummy_097) ∉
      (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_097] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_100 :
    (nb055_alpha_dummy_098) ∉
      (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_098] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_101 : (nb055_alpha_dummy_096) ≠ (nb055_alpha_dummy_097) := by
  simpa only [nb055_alpha_dummy_096, nb055_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb055_distinct_102 : (nb055_alpha_dummy_096) ≠ (nb055_alpha_dummy_098) := by
  simpa only [nb055_alpha_dummy_096, nb055_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb055_distinct_103 : (nb055_alpha_dummy_097) ≠ (nb055_alpha_dummy_098) := by
  simpa only [nb055_alpha_dummy_097, nb055_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb055_fresh_104 (x : Var) (y : Var) :
    (nb055_alpha_dummy_099 x y) ∉
      (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_099] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_105 (x : Var) (y : Var) :
    (nb055_alpha_dummy_100 x y) ∉
      (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_100] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_106 (x : Var) (y : Var) :
    (nb055_alpha_dummy_101 x y) ∉
      (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_101] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_107 (x : Var) (y : Var) :
    (nb055_alpha_dummy_099 x y) ≠ (nb055_alpha_dummy_100 x y) := by
  simpa only [nb055_alpha_dummy_099, nb055_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_108 (x : Var) (y : Var) :
    (nb055_alpha_dummy_099 x y) ≠ (nb055_alpha_dummy_101 x y) := by
  simpa only [nb055_alpha_dummy_099, nb055_alpha_dummy_101] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_109 (x : Var) (y : Var) :
    (nb055_alpha_dummy_100 x y) ≠ (nb055_alpha_dummy_101 x y) := by
  simpa only [nb055_alpha_dummy_100, nb055_alpha_dummy_101] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part003`. -/


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

theorem nb055_fresh_110 :
    (nb055_alpha_dummy_108) ∉
      (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_097))).fv) :=
  by
  simpa only [nb055_alpha_dummy_108] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_097))).fv)
      0

theorem nb055_fresh_111 :
    (nb055_alpha_dummy_104) ∉
      (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) :=
  by
  simpa only [nb055_alpha_dummy_104] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv)
      0

theorem nb055_fresh_112 :
    (nb055_alpha_dummy_110) ∉
      (((Class.cv (nb055_alpha_dummy_098))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) :=
  by
  simpa only [nb055_alpha_dummy_110] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_098))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv)
      0

theorem nb055_fresh_113 (x : Var) (y : Var) :
    (nb055_alpha_dummy_109 x y) ∉
      (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_100 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_109] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_100 x y))).fv)
      0

theorem nb055_fresh_114 (x : Var) (y : Var) :
    (nb055_alpha_dummy_105 x y) ∉
      (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_101 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_105] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_101 x y))).fv)
      0

theorem nb055_fresh_115 (x : Var) (y : Var) :
    (nb055_alpha_dummy_111 x y) ∉
      (((Class.cv (nb055_alpha_dummy_101 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_101 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_111] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_101 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_101 x y))).fv)
      0

theorem nb055_fresh_116 :
    (nb055_alpha_dummy_126) ∉ (((Class.cv (nb055_alpha_dummy_119))).fv) := by
  simpa only [nb055_alpha_dummy_126] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_119))).fv) 0

theorem nb055_fresh_117 :
    (nb055_alpha_dummy_127) ∉ (((Class.cv (nb055_alpha_dummy_119))).fv) := by
  simpa only [nb055_alpha_dummy_127] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_119))).fv) 1

theorem nb055_distinct_118 : (nb055_alpha_dummy_126) ≠ (nb055_alpha_dummy_127) := by
  simpa only [nb055_alpha_dummy_126, nb055_alpha_dummy_127] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_119))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_119 (x : Var) (y : Var) :
    (nb055_alpha_dummy_128 x y) ∉ (((Class.cv (nb055_alpha_dummy_121 x y))).fv) := by
  simpa only [nb055_alpha_dummy_128] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_121 x y))).fv) 0

theorem nb055_fresh_120 (x : Var) (y : Var) :
    (nb055_alpha_dummy_129 x y) ∉ (((Class.cv (nb055_alpha_dummy_121 x y))).fv) := by
  simpa only [nb055_alpha_dummy_129] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_121 x y))).fv) 1

theorem nb055_distinct_121 (x : Var) (y : Var) :
    (nb055_alpha_dummy_128 x y) ≠ (nb055_alpha_dummy_129 x y) := by
  simpa only [nb055_alpha_dummy_128, nb055_alpha_dummy_129] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_121 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb055_fresh_122 :
    (nb055_alpha_dummy_132) ∉
      (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_132] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_123 :
    (nb055_alpha_dummy_133) ∉
      (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_133] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_124 :
    (nb055_alpha_dummy_134) ∉
      (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_134] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_125 : (nb055_alpha_dummy_132) ≠ (nb055_alpha_dummy_133) := by
  simpa only [nb055_alpha_dummy_132, nb055_alpha_dummy_133] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb055_distinct_126 : (nb055_alpha_dummy_132) ≠ (nb055_alpha_dummy_134) := by
  simpa only [nb055_alpha_dummy_132, nb055_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb055_distinct_127 : (nb055_alpha_dummy_133) ≠ (nb055_alpha_dummy_134) := by
  simpa only [nb055_alpha_dummy_133, nb055_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb055_fresh_128 (x : Var) (y : Var) :
    (nb055_alpha_dummy_135 x y) ∉
      (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_135] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_129 (x : Var) (y : Var) :
    (nb055_alpha_dummy_136 x y) ∉
      (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_136] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_130 (x : Var) (y : Var) :
    (nb055_alpha_dummy_137 x y) ∉
      (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_137] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_131 (x : Var) (y : Var) :
    (nb055_alpha_dummy_135 x y) ≠ (nb055_alpha_dummy_136 x y) := by
  simpa only [nb055_alpha_dummy_135, nb055_alpha_dummy_136] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_132 (x : Var) (y : Var) :
    (nb055_alpha_dummy_135 x y) ≠ (nb055_alpha_dummy_137 x y) := by
  simpa only [nb055_alpha_dummy_135, nb055_alpha_dummy_137] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_133 (x : Var) (y : Var) :
    (nb055_alpha_dummy_136 x y) ≠ (nb055_alpha_dummy_137 x y) := by
  simpa only [nb055_alpha_dummy_136, nb055_alpha_dummy_137] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb055_fresh_134 :
    (nb055_alpha_dummy_144) ∉
      (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_133))).fv) :=
  by
  simpa only [nb055_alpha_dummy_144] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_133))).fv)
      0

theorem nb055_fresh_135 :
    (nb055_alpha_dummy_140) ∉
      (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) :=
  by
  simpa only [nb055_alpha_dummy_140] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv)
      0

theorem nb055_fresh_136 :
    (nb055_alpha_dummy_146) ∉
      (((Class.cv (nb055_alpha_dummy_134))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) :=
  by
  simpa only [nb055_alpha_dummy_146] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_134))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv)
      0

theorem nb055_fresh_137 (x : Var) (y : Var) :
    (nb055_alpha_dummy_145 x y) ∉
      (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_136 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_145] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_136 x y))).fv)
      0

theorem nb055_fresh_138 (x : Var) (y : Var) :
    (nb055_alpha_dummy_141 x y) ∉
      (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_137 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_141] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_137 x y))).fv)
      0

theorem nb055_fresh_139 (x : Var) (y : Var) :
    (nb055_alpha_dummy_147 x y) ∉
      (((Class.cv (nb055_alpha_dummy_137 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_137 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_147] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_137 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_137 x y))).fv)
      0

theorem nb055_fresh_140 :
    (nb055_alpha_dummy_162) ∉ (((Class.cv (nb055_alpha_dummy_155))).fv) := by
  simpa only [nb055_alpha_dummy_162] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_155))).fv) 0

theorem nb055_fresh_141 :
    (nb055_alpha_dummy_163) ∉ (((Class.cv (nb055_alpha_dummy_155))).fv) := by
  simpa only [nb055_alpha_dummy_163] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_155))).fv) 1

theorem nb055_distinct_142 : (nb055_alpha_dummy_162) ≠ (nb055_alpha_dummy_163) := by
  simpa only [nb055_alpha_dummy_162, nb055_alpha_dummy_163] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_155))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_143 (x : Var) (y : Var) :
    (nb055_alpha_dummy_164 x y) ∉ (((Class.cv (nb055_alpha_dummy_157 x y))).fv) := by
  simpa only [nb055_alpha_dummy_164] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_157 x y))).fv) 0

theorem nb055_fresh_144 (x : Var) (y : Var) :
    (nb055_alpha_dummy_165 x y) ∉ (((Class.cv (nb055_alpha_dummy_157 x y))).fv) := by
  simpa only [nb055_alpha_dummy_165] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_157 x y))).fv) 1

theorem nb055_distinct_145 (x : Var) (y : Var) :
    (nb055_alpha_dummy_164 x y) ≠ (nb055_alpha_dummy_165 x y) := by
  simpa only [nb055_alpha_dummy_164, nb055_alpha_dummy_165] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_157 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb055_fresh_146 :
    (nb055_alpha_dummy_168) ∉
      (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_168] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_147 :
    (nb055_alpha_dummy_169) ∉
      (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_169] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_148 :
    (nb055_alpha_dummy_170) ∉
      (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_170] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_149 : (nb055_alpha_dummy_168) ≠ (nb055_alpha_dummy_169) := by
  simpa only [nb055_alpha_dummy_168, nb055_alpha_dummy_169] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb055_distinct_150 : (nb055_alpha_dummy_168) ≠ (nb055_alpha_dummy_170) := by
  simpa only [nb055_alpha_dummy_168, nb055_alpha_dummy_170] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb055_distinct_151 : (nb055_alpha_dummy_169) ≠ (nb055_alpha_dummy_170) := by
  simpa only [nb055_alpha_dummy_169, nb055_alpha_dummy_170] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb055_fresh_152 (x : Var) (y : Var) :
    (nb055_alpha_dummy_171 x y) ∉
      (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_171] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_153 (x : Var) (y : Var) :
    (nb055_alpha_dummy_172 x y) ∉
      (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_172] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_154 (x : Var) (y : Var) :
    (nb055_alpha_dummy_173 x y) ∉
      (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb055_alpha_dummy_173] using
    freshVar_not_mem (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_155 (x : Var) (y : Var) :
    (nb055_alpha_dummy_171 x y) ≠ (nb055_alpha_dummy_172 x y) := by
  simpa only [nb055_alpha_dummy_171, nb055_alpha_dummy_172] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_156 (x : Var) (y : Var) :
    (nb055_alpha_dummy_171 x y) ≠ (nb055_alpha_dummy_173 x y) := by
  simpa only [nb055_alpha_dummy_171, nb055_alpha_dummy_173] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_157 (x : Var) (y : Var) :
    (nb055_alpha_dummy_172 x y) ≠ (nb055_alpha_dummy_173 x y) := by
  simpa only [nb055_alpha_dummy_172, nb055_alpha_dummy_173] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb055_fresh_158 :
    (nb055_alpha_dummy_180) ∉
      (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_169))).fv) :=
  by
  simpa only [nb055_alpha_dummy_180] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_169))).fv)
      0

theorem nb055_fresh_159 :
    (nb055_alpha_dummy_176) ∉
      (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) :=
  by
  simpa only [nb055_alpha_dummy_176] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv)
      0

theorem nb055_fresh_160 :
    (nb055_alpha_dummy_182) ∉
      (((Class.cv (nb055_alpha_dummy_170))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) :=
  by
  simpa only [nb055_alpha_dummy_182] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_170))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv)
      0

theorem nb055_fresh_161 (x : Var) (y : Var) :
    (nb055_alpha_dummy_181 x y) ∉
      (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_172 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_181] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_172 x y))).fv)
      0

theorem nb055_fresh_162 (x : Var) (y : Var) :
    (nb055_alpha_dummy_177 x y) ∉
      (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_173 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_177] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_173 x y))).fv)
      0

theorem nb055_fresh_163 (x : Var) (y : Var) :
    (nb055_alpha_dummy_183 x y) ∉
      (((Class.cv (nb055_alpha_dummy_173 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_173 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_183] using
    freshVar_not_mem
      (((Class.cv (nb055_alpha_dummy_173 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_173 x y))).fv)
      0

theorem nb055_fresh_164 (x : Var) (y : Var) :
    (nb055_alpha_dummy_016 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb055_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb055_fresh_165 (x : Var) (y : Var) :
    (nb055_alpha_dummy_017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb055_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb055_fresh_166 (x : Var) (y : Var) :
    (nb055_alpha_dummy_079 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb055_alpha_dummy_079] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 2

theorem nb055_distinct_167 (x : Var) (y : Var) :
    (nb055_alpha_dummy_016 x y) ≠ (nb055_alpha_dummy_017 x y) := by
  simpa only [nb055_alpha_dummy_016, nb055_alpha_dummy_017] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_168 (x : Var) (y : Var) :
    (nb055_alpha_dummy_016 x y) ≠ (nb055_alpha_dummy_079 x y) := by
  simpa only [nb055_alpha_dummy_016, nb055_alpha_dummy_079] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_169 (x : Var) (y : Var) :
    (nb055_alpha_dummy_017 x y) ≠ (nb055_alpha_dummy_079 x y) := by
  simpa only [nb055_alpha_dummy_017, nb055_alpha_dummy_079] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_170 :
    (nb055_alpha_dummy_026) ∉
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_022)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_022)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_022))).fv) :=
  by
  simpa only [nb055_alpha_dummy_026] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_022)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_022)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_022))).fv)
      0

theorem nb055_fresh_171 (x : Var) (y : Var) :
    (nb055_alpha_dummy_027 x y) ∉
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_024 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_027] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_024 x y))).fv)
      0

theorem nb055_fresh_172 :
    (nb055_alpha_dummy_054) ∉
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_050))).fv) :=
  by
  simpa only [nb055_alpha_dummy_054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_050))).fv)
      0

theorem nb055_fresh_173 (x : Var) (y : Var) :
    (nb055_alpha_dummy_055 x y) ∉
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_052 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_052 x y))).fv)
      0

theorem nb055_fresh_174 :
    (nb055_alpha_dummy_094) ∉
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_090)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_090)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_090))).fv) :=
  by
  simpa only [nb055_alpha_dummy_094] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_090)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_090)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_090))).fv)
      0

theorem nb055_fresh_175 (x : Var) (y : Var) :
    (nb055_alpha_dummy_095 x y) ∉
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_092 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_092 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_092 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_095] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_092 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_092 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_092 x y))).fv)
      0

theorem nb055_fresh_176 :
    (nb055_alpha_dummy_130) ∉
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_126)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_126)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_126))).fv) :=
  by
  simpa only [nb055_alpha_dummy_130] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_126)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_126)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_126))).fv)
      0

theorem nb055_fresh_177 (x : Var) (y : Var) :
    (nb055_alpha_dummy_131 x y) ∉
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_128 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_128 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_131] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_128 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_128 x y))).fv)
      0

theorem nb055_fresh_178 :
    (nb055_alpha_dummy_166) ∉
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_162)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_162)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_162))).fv) :=
  by
  simpa only [nb055_alpha_dummy_166] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_162)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_162)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_162))).fv)
      0

theorem nb055_fresh_179 (x : Var) (y : Var) :
    (nb055_alpha_dummy_167 x y) ∉
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_164 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_164 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_164 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_167] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_164 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_164 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_164 x y))).fv)
      0

theorem nb055_fresh_180 :
    (nb055_alpha_dummy_010) ∉
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
                (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_006)
              (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
                (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_006)
              (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb055_fresh_181 (x : Var) (y : Var) :
    (nb055_alpha_dummy_011 x y) ∉
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb055_fresh_182 :
    (nb055_alpha_dummy_018) ∉
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_014)
              (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_014)
              (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_018] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_014)
              (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_014)
              (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb055_fresh_183 (x : Var) (y : Var) :
    (nb055_alpha_dummy_019 x y) ∉
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y)
              (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_016 x y)
              (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_019] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y)
              (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_016 x y)
              (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb055_fresh_184 :
    (nb055_alpha_dummy_086) ∉
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_082)
              (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_083)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_082)
              (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_086] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_082)
              (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_083)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_082)
              (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb055_fresh_185 (x : Var) (y : Var) :
    (nb055_alpha_dummy_087 x y) ∉
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y)
              (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_084 x y)
              (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_087] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y)
              (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_084 x y)
              (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb055_fresh_186 :
    (nb055_alpha_dummy_122) ∉
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_118)
              (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_119)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_118)
              (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_122] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_118)
              (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_119)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_118)
              (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb055_fresh_187 (x : Var) (y : Var) :
    (nb055_alpha_dummy_123 x y) ∉
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y)
              (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_120 x y)
              (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_123] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y)
              (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_120 x y)
              (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb055_fresh_188 :
    (nb055_alpha_dummy_158) ∉
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_154)
              (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_155)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_154)
              (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_158] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_154)
              (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_155)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_154)
              (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb055_fresh_189 (x : Var) (y : Var) :
    (nb055_alpha_dummy_159 x y) ∉
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y)
              (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_156 x y)
              (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_159] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y)
              (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_156 x y)
              (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb055_fresh_190 :
    (nb055_alpha_dummy_038) ∉
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_030)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_030)))).fv)
      0

theorem nb055_fresh_191 (x : Var) (y : Var) :
    (nb055_alpha_dummy_039 x y) ∉
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_033 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_033 x y)))).fv)
      0

theorem nb055_fresh_192 :
    (nb055_alpha_dummy_066) ∉
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_058)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_066] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_058)))).fv)
      0

theorem nb055_fresh_193 (x : Var) (y : Var) :
    (nb055_alpha_dummy_067 x y) ∉
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_061 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_067] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_061 x y)))).fv)
      0

theorem nb055_fresh_194 :
    (nb055_alpha_dummy_106) ∉
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_097)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_098)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_106] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_097)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_098)))).fv)
      0

theorem nb055_fresh_195 (x : Var) (y : Var) :
    (nb055_alpha_dummy_107 x y) ∉
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_100 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_101 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_107] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_100 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_101 x y)))).fv)
      0

theorem nb055_fresh_196 :
    (nb055_alpha_dummy_142) ∉
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_133)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_134)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_142] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_133)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_134)))).fv)
      0

theorem nb055_fresh_197 (x : Var) (y : Var) :
    (nb055_alpha_dummy_143 x y) ∉
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_136 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_137 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_143] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_136 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_137 x y)))).fv)
      0

theorem nb055_fresh_198 :
    (nb055_alpha_dummy_178) ∉
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_169)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_170)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_178] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_169)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_170)))).fv)
      0

theorem nb055_fresh_199 (x : Var) (y : Var) :
    (nb055_alpha_dummy_179 x y) ∉
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_172 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_173 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_179] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_172 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_173 x y)))).fv)
      0

theorem nb055_fresh_200 :
    (nb055_alpha_dummy_074) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_074] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb055_fresh_201 (x : Var) (y : Var) :
    (nb055_alpha_dummy_075 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_075] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb055_fresh_202 :
    (nb055_alpha_dummy_046) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_015))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_046] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_015))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb055_fresh_203 (x : Var) (y : Var) :
    (nb055_alpha_dummy_047 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb055_fresh_204 :
    (nb055_alpha_dummy_114) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_083))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_114] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_083))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb055_fresh_205 (x : Var) (y : Var) :
    (nb055_alpha_dummy_115 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_115] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb055_fresh_206 :
    (nb055_alpha_dummy_150) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_119))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_150] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_119))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb055_fresh_207 (x : Var) (y : Var) :
    (nb055_alpha_dummy_151 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_151] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb055_fresh_208 :
    (nb055_alpha_dummy_186) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_155))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_186] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_155))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb055_fresh_209 (x : Var) (y : Var) :
    (nb055_alpha_dummy_187 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_187] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb055_fresh_210 :
    (nb055_alpha_dummy_034) ∉
      (((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_029))
            (Class.cv (nb055_alpha_dummy_030)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_034] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv)
      0

theorem nb055_fresh_211 (x : Var) (y : Var) :
    (nb055_alpha_dummy_035 x y) ∉
      (((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y))
            (Class.cv (nb055_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y))
            (Class.cv (nb055_alpha_dummy_033 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_035] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y))
            (Class.cv (nb055_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y))
            (Class.cv (nb055_alpha_dummy_033 x y)))).fv)
      0

theorem nb055_fresh_212 :
    (nb055_alpha_dummy_062) ∉
      (((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_057))
            (Class.cv (nb055_alpha_dummy_058)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_062] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv)
      0

theorem nb055_fresh_213 (x : Var) (y : Var) :
    (nb055_alpha_dummy_063 x y) ∉
      (((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y))
            (Class.cv (nb055_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y))
            (Class.cv (nb055_alpha_dummy_061 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_063] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y))
            (Class.cv (nb055_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y))
            (Class.cv (nb055_alpha_dummy_061 x y)))).fv)
      0

theorem nb055_fresh_214 :
    (nb055_alpha_dummy_102) ∉
      (((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_097))
            (Class.cv (nb055_alpha_dummy_098)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_102] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv)
      0

theorem nb055_fresh_215 (x : Var) (y : Var) :
    (nb055_alpha_dummy_103 x y) ∉
      (((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y))
            (Class.cv (nb055_alpha_dummy_101 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y))
            (Class.cv (nb055_alpha_dummy_101 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_103] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y))
            (Class.cv (nb055_alpha_dummy_101 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y))
            (Class.cv (nb055_alpha_dummy_101 x y)))).fv)
      0

theorem nb055_fresh_216 :
    (nb055_alpha_dummy_138) ∉
      (((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_133))
            (Class.cv (nb055_alpha_dummy_134)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_138] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv)
      0

theorem nb055_fresh_217 (x : Var) (y : Var) :
    (nb055_alpha_dummy_139 x y) ∉
      (((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y))
            (Class.cv (nb055_alpha_dummy_137 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y))
            (Class.cv (nb055_alpha_dummy_137 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_139] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y))
            (Class.cv (nb055_alpha_dummy_137 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y))
            (Class.cv (nb055_alpha_dummy_137 x y)))).fv)
      0

theorem nb055_fresh_218 :
    (nb055_alpha_dummy_174) ∉
      (((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_169))
            (Class.cv (nb055_alpha_dummy_170)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_174] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv)
      0

theorem nb055_fresh_219 (x : Var) (y : Var) :
    (nb055_alpha_dummy_175 x y) ∉
      (((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y))
            (Class.cv (nb055_alpha_dummy_173 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y))
            (Class.cv (nb055_alpha_dummy_173 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_175] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y))
            (Class.cv (nb055_alpha_dummy_173 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y))
            (Class.cv (nb055_alpha_dummy_173 x y)))).fv)
      0

theorem nb055_fresh_220 :
    (nb055_alpha_dummy_006) ∉
      (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb055_alpha_dummy_002))).fv) :=
  by
  simpa only [nb055_alpha_dummy_006] using
    freshVar_not_mem
      (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb055_alpha_dummy_002))).fv)
      0

theorem nb055_fresh_221 :
    (nb055_alpha_dummy_007) ∉
      (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb055_alpha_dummy_002))).fv) :=
  by
  simpa only [nb055_alpha_dummy_007] using
    freshVar_not_mem
      (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb055_alpha_dummy_002))).fv)
      1

theorem nb055_distinct_222 : (nb055_alpha_dummy_006) ≠ (nb055_alpha_dummy_007) := by
  simpa only [nb055_alpha_dummy_006, nb055_alpha_dummy_007] using
    (freshVar_injective (((syn_cop (Class.cv (nb055_alpha_dummy_000))
            (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_fresh_223 (x : Var) (y : Var) :
    (nb055_alpha_dummy_008 x y) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_003 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv)
      0

theorem nb055_fresh_224 (x : Var) (y : Var) :
    (nb055_alpha_dummy_009 x y) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_003 x y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv)
      1

theorem nb055_distinct_225 (x : Var) (y : Var) :
    (nb055_alpha_dummy_008 x y) ≠ (nb055_alpha_dummy_009 x y) := by
  simpa only [nb055_alpha_dummy_008, nb055_alpha_dummy_009] using
    (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_003 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_226 :
    (nb055_alpha_dummy_076) ∉
      (((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_076] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv)
      0

theorem nb055_fresh_227 (x : Var) (y : Var) :
    (nb055_alpha_dummy_077 x y) ∉
      (((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv)
      0

theorem nb055_fresh_228 :
    (nb055_alpha_dummy_048) ∉
      (((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv)
      0

theorem nb055_fresh_229 (x : Var) (y : Var) :
    (nb055_alpha_dummy_049 x y) ∉
      (((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv)
      0

theorem nb055_fresh_230 :
    (nb055_alpha_dummy_116) ∉
      (((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_116] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv)
      0

theorem nb055_fresh_231 (x : Var) (y : Var) :
    (nb055_alpha_dummy_117 x y) ∉
      (((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_117] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv)
      0

theorem nb055_fresh_232 :
    (nb055_alpha_dummy_152) ∉
      (((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_152] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv)
      0

theorem nb055_fresh_233 (x : Var) (y : Var) :
    (nb055_alpha_dummy_153 x y) ∉
      (((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_153] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv)
      0

theorem nb055_fresh_234 :
    (nb055_alpha_dummy_188) ∉
      (((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_188] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv)
      0

theorem nb055_fresh_235 (x : Var) (y : Var) :
    (nb055_alpha_dummy_189 x y) ∉
      (((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_189] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv)
      0

theorem nb055_fresh_236 :
    (nb055_alpha_dummy_002) ∉
      (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_ccom (Class.cv (nb055_alpha_dummy_000))
            (Class.cv (nb055_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb055_alpha_dummy_002] using
    freshVar_not_mem
      (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv)
      0

theorem nb055_fresh_237 :
    (nb055_alpha_dummy_004) ∉
      (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪
          ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_002))
              (syn_ccom (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_001)))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_004] using
    freshVar_not_mem
      (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪
          ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_002))
              (syn_ccom (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_001)))))).fv)
      0

theorem nb055_fresh_238 :
    (nb055_alpha_dummy_080) ∉
      (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014))
                (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_015)))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_080] using
    freshVar_not_mem
      (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014))
                (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_015)))))).fv)
      0

theorem nb055_fresh_239 (x : Var) (y : Var) :
    (nb055_alpha_dummy_081 x y) ∉
      (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y)
            (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y)
                (Class.cv (nb055_alpha_dummy_079 x y)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x)
                (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_081] using
    freshVar_not_mem
      (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y)
            (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y)
                (Class.cv (nb055_alpha_dummy_079 x y)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x)
                (Class.cv (nb055_alpha_dummy_017 x y)))))).fv)
      0

theorem nb055_fresh_240 (x : Var) (y : Var) :
    (nb055_alpha_dummy_003 x y) ∉
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_ccom (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb055_alpha_dummy_003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_ccom (Class.cv x) (Class.cv y))).fv)
      0

theorem nb055_fresh_241 (x : Var) (y : Var) :
    (nb055_alpha_dummy_005 x y) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y))
              (syn_ccom (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb055_alpha_dummy_005] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y))
              (syn_ccom (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb055_fresh_242 : (nb055_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb055_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb055_fresh_243 : (nb055_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb055_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb055_distinct_244 : (nb055_alpha_dummy_000) ≠ (nb055_alpha_dummy_001) := by
  simpa only [nb055_alpha_dummy_000, nb055_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb055_support_mem_0000 :
    (nb055_alpha_dummy_000) ∈
      (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪
          ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_002))
              (syn_ccom (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_001)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb055_alpha_dummy_000)) (s :=
        ({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪
          ({(nb055_alpha_dummy_002)} : Finset Var))
        ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_002))
              (syn_ccom (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_001)))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0001 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y))
              (syn_ccom (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055_alpha_dummy_003 x y)} : Finset Var))
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
              (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y))
              (syn_ccom (Class.cv x) (Class.cv y))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0002 :
    (nb055_alpha_dummy_001) ∈
      (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪
          ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_002))
              (syn_ccom (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_001)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb055_alpha_dummy_001)) (s :=
        ({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪
          ({(nb055_alpha_dummy_002)} : Finset Var))
        ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_002))
              (syn_ccom (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_001)))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0003 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y))
              (syn_ccom (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055_alpha_dummy_003 x y)} : Finset Var))
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
              (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y))
              (syn_ccom (Class.cv x) (Class.cv y))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0004 :
    (nb055_alpha_dummy_002) ∈
      (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪
          ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_002))
              (syn_ccom (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_001)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb055_alpha_dummy_002)) (s :=
        ({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪
          ({(nb055_alpha_dummy_002)} : Finset Var))
        ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_002))
              (syn_ccom (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_001)))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0005 (x : Var) (y : Var) :
    (nb055_alpha_dummy_003 x y) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y))
              (syn_ccom (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb055_alpha_dummy_003 x y)) (s :=
        ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055_alpha_dummy_003 x y)} : Finset Var))
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
              (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y))
              (syn_ccom (Class.cv x) (Class.cv y))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0006 :
    (nb055_alpha_dummy_000) ∈
      (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_ccom (Class.cv (nb055_alpha_dummy_000))
            (Class.cv (nb055_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_ccom (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s :=
        ({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv)
        ((syn_ccom (Class.cv x) (Class.cv y))).fv ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0008 :
    (nb055_alpha_dummy_000) ∈
      (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb055_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part004`. -/


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

theorem nb055_support_mem_0009 :
    (nb055_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
                (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_006)
              (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0010 (x : Var) (y : Var) :
    x ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0011 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s := ((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv)
        ((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0012 :
    (nb055_alpha_dummy_000) ∈
      (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
              (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
              (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0013 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0014 :
    (nb055_alpha_dummy_000) ∈
      (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0015 :
    (nb055_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_014)
              (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_014)
              (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0016 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0017 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y)
              (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_016 x y)
              (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0018 :
    (nb055_alpha_dummy_000) ∈
      (((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0019 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0020 :
    (nb055_alpha_dummy_015) ∈ (((Class.cv (nb055_alpha_dummy_015))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0021 (x : Var) (y : Var) :
    (nb055_alpha_dummy_017 x y) ∈ (((Class.cv (nb055_alpha_dummy_017 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0022 :
    (nb055_alpha_dummy_022) ∈
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_022)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_022)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_022))).fv) :=
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

theorem nb055_support_mem_0023 (x : Var) (y : Var) :
    (nb055_alpha_dummy_024 x y) ∈
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_024 x y))).fv) :=
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

theorem nb055_support_mem_0024 :
    (nb055_alpha_dummy_022) ∈
      (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0025 (x : Var) (y : Var) :
    (nb055_alpha_dummy_024 x y) ∈
      (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0026 :
    (nb055_alpha_dummy_029) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_029))
            (Class.cv (nb055_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0027 (x : Var) (y : Var) :
    (nb055_alpha_dummy_032 x y) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y))
            (Class.cv (nb055_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y))
            (Class.cv (nb055_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0028 :
    (nb055_alpha_dummy_029) ∈
      (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0029 (x : Var) (y : Var) :
    (nb055_alpha_dummy_032 x y) ∈
      (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0030 :
    (nb055_alpha_dummy_030) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_029))
            (Class.cv (nb055_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0031 (x : Var) (y : Var) :
    (nb055_alpha_dummy_033 x y) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y))
            (Class.cv (nb055_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y))
            (Class.cv (nb055_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0032 :
    (nb055_alpha_dummy_030) ∈
      (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0033 (x : Var) (y : Var) :
    (nb055_alpha_dummy_033 x y) ∈
      (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0034 :
    (nb055_alpha_dummy_029) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0035 (x : Var) (y : Var) :
    (nb055_alpha_dummy_032 x y) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0036 :
    (nb055_alpha_dummy_029) ∈
      (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0037 (x : Var) (y : Var) :
    (nb055_alpha_dummy_032 x y) ∈
      (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_032 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0038 :
    (nb055_alpha_dummy_030) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0039 (x : Var) (y : Var) :
    (nb055_alpha_dummy_033 x y) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0040 :
    (nb055_alpha_dummy_030) ∈
      (((Class.cv (nb055_alpha_dummy_030))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0041 (x : Var) (y : Var) :
    (nb055_alpha_dummy_033 x y) ∈
      (((Class.cv (nb055_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0042 :
    (nb055_alpha_dummy_001) ∈
      (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_ccom (Class.cv (nb055_alpha_dummy_000))
            (Class.cv (nb055_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0043 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_ccom (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s :=
        ({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv)
        ((syn_ccom (Class.cv x) (Class.cv y))).fv ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0044 :
    (nb055_alpha_dummy_001) ∈
      (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb055_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0045 :
    (nb055_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
                (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_006)
              (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0046 (x : Var) (y : Var) :
    y ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0047 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s := ((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv)
        ((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0048 :
    (nb055_alpha_dummy_001) ∈
      (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
              (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
              (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0049 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0050 :
    (nb055_alpha_dummy_001) ∈
      (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0051 :
    (nb055_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_014)
              (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_014)
              (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0052 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0053 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y)
              (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_016 x y)
              (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0054 :
    (nb055_alpha_dummy_001) ∈
      (((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0055 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0056 :
    (nb055_alpha_dummy_015) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_015))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0057 (x : Var) (y : Var) :
    (nb055_alpha_dummy_017 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0058 :
    (nb055_alpha_dummy_015) ∈
      (((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0059 (x : Var) (y : Var) :
    (nb055_alpha_dummy_017 x y) ∈
      (((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0060 :
    (nb055_alpha_dummy_007) ∈ (((Class.cv (nb055_alpha_dummy_007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0061 (x : Var) (y : Var) :
    (nb055_alpha_dummy_009 x y) ∈ (((Class.cv (nb055_alpha_dummy_009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0062 :
    (nb055_alpha_dummy_050) ∈
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_050))).fv) :=
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

theorem nb055_support_mem_0063 (x : Var) (y : Var) :
    (nb055_alpha_dummy_052 x y) ∈
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_052 x y))).fv) :=
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

theorem nb055_support_mem_0064 :
    (nb055_alpha_dummy_050) ∈
      (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0065 (x : Var) (y : Var) :
    (nb055_alpha_dummy_052 x y) ∈
      (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0066 :
    (nb055_alpha_dummy_057) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_057))
            (Class.cv (nb055_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0067 (x : Var) (y : Var) :
    (nb055_alpha_dummy_060 x y) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y))
            (Class.cv (nb055_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y))
            (Class.cv (nb055_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0068 :
    (nb055_alpha_dummy_057) ∈
      (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0069 (x : Var) (y : Var) :
    (nb055_alpha_dummy_060 x y) ∈
      (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0070 :
    (nb055_alpha_dummy_058) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_057))
            (Class.cv (nb055_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0071 (x : Var) (y : Var) :
    (nb055_alpha_dummy_061 x y) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y))
            (Class.cv (nb055_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y))
            (Class.cv (nb055_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0072 :
    (nb055_alpha_dummy_058) ∈
      (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0073 (x : Var) (y : Var) :
    (nb055_alpha_dummy_061 x y) ∈
      (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0074 :
    (nb055_alpha_dummy_057) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0075 (x : Var) (y : Var) :
    (nb055_alpha_dummy_060 x y) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0076 :
    (nb055_alpha_dummy_057) ∈
      (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0077 (x : Var) (y : Var) :
    (nb055_alpha_dummy_060 x y) ∈
      (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0078 :
    (nb055_alpha_dummy_058) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0079 (x : Var) (y : Var) :
    (nb055_alpha_dummy_061 x y) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0080 :
    (nb055_alpha_dummy_058) ∈
      (((Class.cv (nb055_alpha_dummy_058))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0081 (x : Var) (y : Var) :
    (nb055_alpha_dummy_061 x y) ∈
      (((Class.cv (nb055_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0082 :
    (nb055_alpha_dummy_002) ∈
      (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb055_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0083 :
    (nb055_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
                (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_006)
              (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0084 (x : Var) (y : Var) :
    (nb055_alpha_dummy_003 x y) ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0085 (x : Var) (y : Var) :
    (nb055_alpha_dummy_003 x y) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_right (a := (nb055_alpha_dummy_003 x y)) (t := ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
        ((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0086 :
    (nb055_alpha_dummy_002) ∈
      (((Class.cab (nb055_alpha_dummy_006)
            (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006)
            (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0087 (x : Var) (y : Var) :
    (nb055_alpha_dummy_003 x y) ∈
      (((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y)
            (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0088 :
    (nb055_alpha_dummy_007) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0089 (x : Var) (y : Var) :
    (nb055_alpha_dummy_009 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0090 :
    (nb055_alpha_dummy_007) ∈
      (((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0091 (x : Var) (y : Var) :
    (nb055_alpha_dummy_009 x y) ∈
      (((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0092 :
    (nb055_alpha_dummy_014) ∈
      (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014))
                (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_015)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0093 (x : Var) (y : Var) :
    (nb055_alpha_dummy_016 x y) ∈
      (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y)
            (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y)
                (Class.cv (nb055_alpha_dummy_079 x y)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x)
                (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0094 :
    (nb055_alpha_dummy_015) ∈
      (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014))
                (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_015)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0095 (x : Var) (y : Var) :
    (nb055_alpha_dummy_017 x y) ∈
      (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y)
            (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y)
                (Class.cv (nb055_alpha_dummy_079 x y)))
              (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x)
                (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0096 :
    (nb055_alpha_dummy_014) ∈
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0097 :
    (nb055_alpha_dummy_014) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_082)
              (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_083)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_082)
              (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0098 (x : Var) (y : Var) :
    (nb055_alpha_dummy_016 x y) ∈
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0099 (x : Var) (y : Var) :
    (nb055_alpha_dummy_016 x y) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y)
              (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_084 x y)
              (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0100 :
    (nb055_alpha_dummy_014) ∈
      (((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0101 (x : Var) (y : Var) :
    (nb055_alpha_dummy_016 x y) ∈
      (((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv ∪
        ((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0102 :
    (nb055_alpha_dummy_083) ∈ (((Class.cv (nb055_alpha_dummy_083))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0103 (x : Var) (y : Var) :
    (nb055_alpha_dummy_085 x y) ∈ (((Class.cv (nb055_alpha_dummy_085 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0104 :
    (nb055_alpha_dummy_090) ∈
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_090)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_090)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_090))).fv) :=
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

theorem nb055_support_mem_0105 (x : Var) (y : Var) :
    (nb055_alpha_dummy_092 x y) ∈
      (((Wff.classMem (Class.cv (nb055_alpha_dummy_092 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb055_alpha_dummy_092 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb055_alpha_dummy_092 x y))).fv) :=
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

theorem nb055_support_mem_0106 :
    (nb055_alpha_dummy_090) ∈
      (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0107 (x : Var) (y : Var) :
    (nb055_alpha_dummy_092 x y) ∈
      (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0108 :
    (nb055_alpha_dummy_097) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_097))
            (Class.cv (nb055_alpha_dummy_098)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0109 (x : Var) (y : Var) :
    (nb055_alpha_dummy_100 x y) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y))
            (Class.cv (nb055_alpha_dummy_101 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y))
            (Class.cv (nb055_alpha_dummy_101 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0110 :
    (nb055_alpha_dummy_097) ∈
      (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0111 (x : Var) (y : Var) :
    (nb055_alpha_dummy_100 x y) ∈
      (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_101 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0112 :
    (nb055_alpha_dummy_098) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_097))
            (Class.cv (nb055_alpha_dummy_098)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0113 (x : Var) (y : Var) :
    (nb055_alpha_dummy_101 x y) ∈
      (((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y))
            (Class.cv (nb055_alpha_dummy_101 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y))
            (Class.cv (nb055_alpha_dummy_101 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0114 :
    (nb055_alpha_dummy_098) ∈
      (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0115 (x : Var) (y : Var) :
    (nb055_alpha_dummy_101 x y) ∈
      (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_101 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0116 :
    (nb055_alpha_dummy_097) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_097)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_098)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0117 (x : Var) (y : Var) :
    (nb055_alpha_dummy_100 x y) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_100 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_101 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0118 :
    (nb055_alpha_dummy_097) ∈
      (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_097))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0119 (x : Var) (y : Var) :
    (nb055_alpha_dummy_100 x y) ∈
      (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_100 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0120 :
    (nb055_alpha_dummy_098) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_097)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_098)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0121 (x : Var) (y : Var) :
    (nb055_alpha_dummy_101 x y) ∈
      (((syn_ccompl (Class.cv (nb055_alpha_dummy_100 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb055_alpha_dummy_101 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0122 :
    (nb055_alpha_dummy_098) ∈
      (((Class.cv (nb055_alpha_dummy_098))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0123 (x : Var) (y : Var) :
    (nb055_alpha_dummy_101 x y) ∈
      (((Class.cv (nb055_alpha_dummy_101 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_101 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0124 :
    (nb055_alpha_dummy_015) ∈
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0125 :
    (nb055_alpha_dummy_015) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_082)
              (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_083)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_082)
              (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0126 (x : Var) (y : Var) :
    (nb055_alpha_dummy_017 x y) ∈
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0127 (x : Var) (y : Var) :
    (nb055_alpha_dummy_017 x y) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y)
              (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_084 x y)
              (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0128 :
    (nb055_alpha_dummy_015) ∈
      (((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0129 (x : Var) (y : Var) :
    (nb055_alpha_dummy_017 x y) ∈
      (((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0130 :
    (nb055_alpha_dummy_083) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_083))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0131 (x : Var) (y : Var) :
    (nb055_alpha_dummy_085 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0132 :
    (nb055_alpha_dummy_083) ∈
      (((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0133 (x : Var) (y : Var) :
    (nb055_alpha_dummy_085 x y) ∈
      (((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0134 :
    (nb055_alpha_dummy_014) ∈
      (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0135 :
    (nb055_alpha_dummy_014) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_118)
              (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_119)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_118)
              (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0134) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0134) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0136 (x : Var) (y : Var) :
    (nb055_alpha_dummy_016 x y) ∈
      (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb055_alpha_dummy_079 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0137 (x : Var) (y : Var) :
    (nb055_alpha_dummy_016 x y) ∈
      (((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y)
              (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb055_alpha_dummy_120 x y)
              (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0136 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0136 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
