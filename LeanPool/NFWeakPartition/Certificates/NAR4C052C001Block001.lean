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

/-! Certificates from `NAR4C052C001Part001`. -/


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
noncomputable def nb052_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb052_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb052_alpha_dummy_002 : Var :=
  (freshVar (({(nb052_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
          ({(nb052_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
      ((syn_cun (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_003 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
      ((syn_cun (Class.cv x) (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_004 : Var :=
  (freshVar
    (({(nb052_alpha_dummy_000)} : Finset Var) ∪ ({(nb052_alpha_dummy_001)} : Finset Var) ∪
        ({(nb052_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv (nb052_alpha_dummy_000)) (syn_cvv))
            (Wff.classMem (Class.cv (nb052_alpha_dummy_001)) (syn_cvv)))
          (Wff.classEq (Class.cv (nb052_alpha_dummy_002))
            (syn_cun (Class.cv (nb052_alpha_dummy_000))
              (Class.cv (nb052_alpha_dummy_001)))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_005 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb052_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
          (Wff.classEq (Class.cv (nb052_alpha_dummy_003 x y))
            (syn_cun (Class.cv x) (Class.cv y))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_006 : Var :=
  (freshVar (((syn_cop (Class.cv (nb052_alpha_dummy_000))
          (Class.cv (nb052_alpha_dummy_001)))).fv ∪ ((Class.cv (nb052_alpha_dummy_002))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_007 : Var :=
  (freshVar (((syn_cop (Class.cv (nb052_alpha_dummy_000))
          (Class.cv (nb052_alpha_dummy_001)))).fv ∪ ((Class.cv (nb052_alpha_dummy_002))).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_008 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb052_alpha_dummy_003 x y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_009 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb052_alpha_dummy_003 x y))).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_010 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
              (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cphi (Class.cv (nb052_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb052_alpha_dummy_006)
            (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_011 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_012 : Var :=
  (freshVar (((Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
            (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
              (syn_cphi (Class.cv (nb052_alpha_dummy_007))))))).fv ∪
      ((Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
            (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
              (syn_cphi (Class.cv (nb052_alpha_dummy_007))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb052_alpha_dummy_008 x y)
          (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
              (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))))).fv ∪
      ((Class.cab (nb052_alpha_dummy_008 x y)
          (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
              (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_014 : Var :=
  (freshVar
    (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_015 : Var :=
  (freshVar
    (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_018 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cphi (Class.cv (nb052_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_019 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_020 : Var :=
  (freshVar (((Class.cab (nb052_alpha_dummy_014)
          (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
              (syn_cphi (Class.cv (nb052_alpha_dummy_015))))))).fv ∪
      ((Class.cab (nb052_alpha_dummy_014)
          (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
              (syn_cphi (Class.cv (nb052_alpha_dummy_015))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb052_alpha_dummy_016 x y)
          (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
              (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))))).fv ∪
      ((Class.cab (nb052_alpha_dummy_016 x y) (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
              (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_022 : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_015))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_023 : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_015))).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_017 x y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_017 x y))).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_026 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb052_alpha_dummy_022)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb052_alpha_dummy_022)) (syn_c1c))).fv ∪
      ((Class.cv (nb052_alpha_dummy_022))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_027 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb052_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb052_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb052_alpha_dummy_024 x y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_028 : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_029 : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_030 : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb052_alpha_dummy_031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb052_alpha_dummy_034 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb052_alpha_dummy_029))
          (Class.cv (nb052_alpha_dummy_030)))).fv ∪
      ((syn_cnin (Class.cv (nb052_alpha_dummy_029)) (Class.cv (nb052_alpha_dummy_030)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_035 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb052_alpha_dummy_032 x y))
          (Class.cv (nb052_alpha_dummy_033 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb052_alpha_dummy_032 x y))
          (Class.cv (nb052_alpha_dummy_033 x y)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_036 : Var :=
  (freshVar
    (((Class.cv (nb052_alpha_dummy_029))).fv ∪ ((Class.cv (nb052_alpha_dummy_030))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_037 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_032 x y))).fv ∪
      ((Class.cv (nb052_alpha_dummy_033 x y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_038 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb052_alpha_dummy_029)))).fv ∪
      ((syn_ccompl (Class.cv (nb052_alpha_dummy_030)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_039 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb052_alpha_dummy_032 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb052_alpha_dummy_033 x y)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_040 : Var :=
  (freshVar
    (((Class.cv (nb052_alpha_dummy_029))).fv ∪ ((Class.cv (nb052_alpha_dummy_029))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_041 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_032 x y))).fv ∪
      ((Class.cv (nb052_alpha_dummy_032 x y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_042 : Var :=
  (freshVar
    (((Class.cv (nb052_alpha_dummy_030))).fv ∪ ((Class.cv (nb052_alpha_dummy_030))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_043 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_033 x y))).fv ∪
      ((Class.cv (nb052_alpha_dummy_033 x y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_044 : Var :=
  (freshVar (((Class.cab (nb052_alpha_dummy_014)
          (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
              (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_014)
          (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
              (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb052_alpha_dummy_016 x y)
          (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
              (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_016 x y)
          (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
              (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_046 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_015))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_047 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_048 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb052_alpha_dummy_015)))).fv ∪
      ((syn_cphi (Class.cv (nb052_alpha_dummy_015)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_049 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_050 : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_007))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_051 : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_007))).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_009 x y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_009 x y))).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb052_alpha_dummy_050)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb052_alpha_dummy_050)) (syn_c1c))).fv ∪
      ((Class.cv (nb052_alpha_dummy_050))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb052_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb052_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb052_alpha_dummy_052 x y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_056 : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_057 : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_058 : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb052_alpha_dummy_059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb052_alpha_dummy_061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb052_alpha_dummy_062 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb052_alpha_dummy_057))
          (Class.cv (nb052_alpha_dummy_058)))).fv ∪
      ((syn_cnin (Class.cv (nb052_alpha_dummy_057)) (Class.cv (nb052_alpha_dummy_058)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_063 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb052_alpha_dummy_060 x y))
          (Class.cv (nb052_alpha_dummy_061 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb052_alpha_dummy_060 x y))
          (Class.cv (nb052_alpha_dummy_061 x y)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_064 : Var :=
  (freshVar
    (((Class.cv (nb052_alpha_dummy_057))).fv ∪ ((Class.cv (nb052_alpha_dummy_058))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_060 x y))).fv ∪
      ((Class.cv (nb052_alpha_dummy_061 x y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_066 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb052_alpha_dummy_057)))).fv ∪
      ((syn_ccompl (Class.cv (nb052_alpha_dummy_058)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_067 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb052_alpha_dummy_060 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb052_alpha_dummy_061 x y)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_068 : Var :=
  (freshVar
    (((Class.cv (nb052_alpha_dummy_057))).fv ∪ ((Class.cv (nb052_alpha_dummy_057))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_060 x y))).fv ∪
      ((Class.cv (nb052_alpha_dummy_060 x y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_070 : Var :=
  (freshVar
    (((Class.cv (nb052_alpha_dummy_058))).fv ∪ ((Class.cv (nb052_alpha_dummy_058))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052_alpha_dummy_061 x y))).fv ∪
      ((Class.cv (nb052_alpha_dummy_061 x y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_072 : Var :=
  (freshVar (((Class.cab (nb052_alpha_dummy_006)
          (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
              (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_006)
          (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
              (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb052_alpha_dummy_008 x y)
          (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
              (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_008 x y)
          (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
              (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_074 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_007))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_075 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_076 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb052_alpha_dummy_007)))).fv ∪
      ((syn_cphi (Class.cv (nb052_alpha_dummy_007)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_077 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_078 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb052_alpha_dummy_000)))).fv ∪
      ((syn_ccompl (Class.cv (nb052_alpha_dummy_001)))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_079 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv x))).fv ∪ ((syn_ccompl (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_080 : Var :=
  (freshVar
    (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_081 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_082 : Var :=
  (freshVar
    (((Class.cv (nb052_alpha_dummy_001))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb052_alpha_dummy_083 (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv y)).fv) 0)

theorem nb052_fresh_000 :
    (nb052_alpha_dummy_072) ∉
      (((Class.cab (nb052_alpha_dummy_006)
            (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_006)
            (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cab (nb052_alpha_dummy_006)
            (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_006)
            (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb052_fresh_001 :
    (nb052_alpha_dummy_012) ∉
      (((Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
              (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cphi (Class.cv (nb052_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
              (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cphi (Class.cv (nb052_alpha_dummy_007))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
              (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cphi (Class.cv (nb052_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
              (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cphi (Class.cv (nb052_alpha_dummy_007))))))).fv)
      0

theorem nb052_fresh_002 (x : Var) (y : Var) :
    (nb052_alpha_dummy_073 x y) ∉
      (((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb052_fresh_003 (x : Var) (y : Var) :
    (nb052_alpha_dummy_013 x y) ∉
      (((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_013] using
    freshVar_not_mem
      (((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))))).fv)
      0

theorem nb052_fresh_004 :
    (nb052_alpha_dummy_020) ∉
      (((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cphi (Class.cv (nb052_alpha_dummy_015))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cphi (Class.cv (nb052_alpha_dummy_015))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_020] using
    freshVar_not_mem
      (((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cphi (Class.cv (nb052_alpha_dummy_015))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cphi (Class.cv (nb052_alpha_dummy_015))))))).fv)
      0

theorem nb052_fresh_005 :
    (nb052_alpha_dummy_044) ∉
      (((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb052_fresh_006 (x : Var) (y : Var) :
    (nb052_alpha_dummy_021 x y) ∉
      (((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_021] using
    freshVar_not_mem
      (((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))))).fv)
      0

theorem nb052_fresh_007 (x : Var) (y : Var) :
    (nb052_alpha_dummy_045 x y) ∉
      (((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb052_fresh_008 :
    (nb052_alpha_dummy_080) ∉
      (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_000))).fv) :=
  by
  simpa only [nb052_alpha_dummy_080] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_000))).fv)
      0

theorem nb052_fresh_009 :
    (nb052_alpha_dummy_014) ∉
      (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv) :=
  by
  simpa only [nb052_alpha_dummy_014] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv)
      0

theorem nb052_fresh_010 :
    (nb052_alpha_dummy_015) ∉
      (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv) :=
  by
  simpa only [nb052_alpha_dummy_015] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv)
      1

theorem nb052_distinct_011 : (nb052_alpha_dummy_014) ≠ (nb052_alpha_dummy_015) := by
  simpa only [nb052_alpha_dummy_014, nb052_alpha_dummy_015] using
    (freshVar_injective
      (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb052_fresh_012 :
    (nb052_alpha_dummy_082) ∉
      (((Class.cv (nb052_alpha_dummy_001))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv) :=
  by
  simpa only [nb052_alpha_dummy_082] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_001))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv)
      0

theorem nb052_fresh_013 :
    (nb052_alpha_dummy_050) ∉ (((Class.cv (nb052_alpha_dummy_007))).fv) := by
  simpa only [nb052_alpha_dummy_050] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_007))).fv) 0

theorem nb052_fresh_014 :
    (nb052_alpha_dummy_051) ∉ (((Class.cv (nb052_alpha_dummy_007))).fv) := by
  simpa only [nb052_alpha_dummy_051] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_007))).fv) 1

theorem nb052_distinct_015 : (nb052_alpha_dummy_050) ≠ (nb052_alpha_dummy_051) := by
  simpa only [nb052_alpha_dummy_050, nb052_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_007))).fv) (i := 0) (j := 1) (by decide))

theorem nb052_fresh_016 (x : Var) (y : Var) :
    (nb052_alpha_dummy_052 x y) ∉ (((Class.cv (nb052_alpha_dummy_009 x y))).fv) := by
  simpa only [nb052_alpha_dummy_052] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_009 x y))).fv) 0

theorem nb052_fresh_017 (x : Var) (y : Var) :
    (nb052_alpha_dummy_053 x y) ∉ (((Class.cv (nb052_alpha_dummy_009 x y))).fv) := by
  simpa only [nb052_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_009 x y))).fv) 1

theorem nb052_distinct_018 (x : Var) (y : Var) :
    (nb052_alpha_dummy_052 x y) ≠ (nb052_alpha_dummy_053 x y) := by
  simpa only [nb052_alpha_dummy_052, nb052_alpha_dummy_053] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_009 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb052_fresh_019 :
    (nb052_alpha_dummy_022) ∉ (((Class.cv (nb052_alpha_dummy_015))).fv) := by
  simpa only [nb052_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_015))).fv) 0

theorem nb052_fresh_020 :
    (nb052_alpha_dummy_023) ∉ (((Class.cv (nb052_alpha_dummy_015))).fv) := by
  simpa only [nb052_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_015))).fv) 1

theorem nb052_distinct_021 : (nb052_alpha_dummy_022) ≠ (nb052_alpha_dummy_023) := by
  simpa only [nb052_alpha_dummy_022, nb052_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_015))).fv) (i := 0) (j := 1) (by decide))

theorem nb052_fresh_022 (x : Var) (y : Var) :
    (nb052_alpha_dummy_024 x y) ∉ (((Class.cv (nb052_alpha_dummy_017 x y))).fv) := by
  simpa only [nb052_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_017 x y))).fv) 0

theorem nb052_fresh_023 (x : Var) (y : Var) :
    (nb052_alpha_dummy_025 x y) ∉ (((Class.cv (nb052_alpha_dummy_017 x y))).fv) := by
  simpa only [nb052_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_017 x y))).fv) 1

theorem nb052_distinct_024 (x : Var) (y : Var) :
    (nb052_alpha_dummy_024 x y) ≠ (nb052_alpha_dummy_025 x y) := by
  simpa only [nb052_alpha_dummy_024, nb052_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_017 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb052_fresh_025 :
    (nb052_alpha_dummy_028) ∉
      (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_028] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 0

theorem nb052_fresh_026 :
    (nb052_alpha_dummy_029) ∉
      (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_029] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 1

theorem nb052_fresh_027 :
    (nb052_alpha_dummy_030) ∉
      (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_030] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 2

theorem nb052_distinct_028 : (nb052_alpha_dummy_028) ≠ (nb052_alpha_dummy_029) := by
  simpa only [nb052_alpha_dummy_028, nb052_alpha_dummy_029] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb052_distinct_029 : (nb052_alpha_dummy_028) ≠ (nb052_alpha_dummy_030) := by
  simpa only [nb052_alpha_dummy_028, nb052_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb052_distinct_030 : (nb052_alpha_dummy_029) ≠ (nb052_alpha_dummy_030) := by
  simpa only [nb052_alpha_dummy_029, nb052_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb052_fresh_031 (x : Var) (y : Var) :
    (nb052_alpha_dummy_031 x y) ∉
      (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_031] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb052_fresh_032 (x : Var) (y : Var) :
    (nb052_alpha_dummy_032 x y) ∉
      (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_032] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb052_fresh_033 (x : Var) (y : Var) :
    (nb052_alpha_dummy_033 x y) ∉
      (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_033] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb052_distinct_034 (x : Var) (y : Var) :
    (nb052_alpha_dummy_031 x y) ≠ (nb052_alpha_dummy_032 x y) := by
  simpa only [nb052_alpha_dummy_031, nb052_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb052_distinct_035 (x : Var) (y : Var) :
    (nb052_alpha_dummy_031 x y) ≠ (nb052_alpha_dummy_033 x y) := by
  simpa only [nb052_alpha_dummy_031, nb052_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb052_distinct_036 (x : Var) (y : Var) :
    (nb052_alpha_dummy_032 x y) ≠ (nb052_alpha_dummy_033 x y) := by
  simpa only [nb052_alpha_dummy_032, nb052_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb052_fresh_037 :
    (nb052_alpha_dummy_040) ∉
      (((Class.cv (nb052_alpha_dummy_029))).fv ∪ ((Class.cv (nb052_alpha_dummy_029))).fv) :=
  by
  simpa only [nb052_alpha_dummy_040] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_029))).fv ∪ ((Class.cv (nb052_alpha_dummy_029))).fv)
      0

theorem nb052_fresh_038 :
    (nb052_alpha_dummy_036) ∉
      (((Class.cv (nb052_alpha_dummy_029))).fv ∪ ((Class.cv (nb052_alpha_dummy_030))).fv) :=
  by
  simpa only [nb052_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_029))).fv ∪ ((Class.cv (nb052_alpha_dummy_030))).fv)
      0

theorem nb052_fresh_039 :
    (nb052_alpha_dummy_042) ∉
      (((Class.cv (nb052_alpha_dummy_030))).fv ∪ ((Class.cv (nb052_alpha_dummy_030))).fv) :=
  by
  simpa only [nb052_alpha_dummy_042] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_030))).fv ∪ ((Class.cv (nb052_alpha_dummy_030))).fv)
      0

theorem nb052_fresh_040 (x : Var) (y : Var) :
    (nb052_alpha_dummy_041 x y) ∉
      (((Class.cv (nb052_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_032 x y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_041] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_032 x y))).fv)
      0

theorem nb052_fresh_041 (x : Var) (y : Var) :
    (nb052_alpha_dummy_037 x y) ∉
      (((Class.cv (nb052_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_033 x y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_033 x y))).fv)
      0

theorem nb052_fresh_042 (x : Var) (y : Var) :
    (nb052_alpha_dummy_043 x y) ∉
      (((Class.cv (nb052_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_033 x y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_033 x y))).fv)
      0

theorem nb052_fresh_043 :
    (nb052_alpha_dummy_056) ∉
      (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_056] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0

theorem nb052_fresh_044 :
    (nb052_alpha_dummy_057) ∉
      (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_057] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1

theorem nb052_fresh_045 :
    (nb052_alpha_dummy_058) ∉
      (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2

theorem nb052_distinct_046 : (nb052_alpha_dummy_056) ≠ (nb052_alpha_dummy_057) := by
  simpa only [nb052_alpha_dummy_056, nb052_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb052_distinct_047 : (nb052_alpha_dummy_056) ≠ (nb052_alpha_dummy_058) := by
  simpa only [nb052_alpha_dummy_056, nb052_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb052_distinct_048 : (nb052_alpha_dummy_057) ≠ (nb052_alpha_dummy_058) := by
  simpa only [nb052_alpha_dummy_057, nb052_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb052_fresh_049 (x : Var) (y : Var) :
    (nb052_alpha_dummy_059 x y) ∉
      (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb052_fresh_050 (x : Var) (y : Var) :
    (nb052_alpha_dummy_060 x y) ∉
      (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb052_fresh_051 (x : Var) (y : Var) :
    (nb052_alpha_dummy_061 x y) ∉
      (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb052_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb052_distinct_052 (x : Var) (y : Var) :
    (nb052_alpha_dummy_059 x y) ≠ (nb052_alpha_dummy_060 x y) := by
  simpa only [nb052_alpha_dummy_059, nb052_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb052_distinct_053 (x : Var) (y : Var) :
    (nb052_alpha_dummy_059 x y) ≠ (nb052_alpha_dummy_061 x y) := by
  simpa only [nb052_alpha_dummy_059, nb052_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb052_distinct_054 (x : Var) (y : Var) :
    (nb052_alpha_dummy_060 x y) ≠ (nb052_alpha_dummy_061 x y) := by
  simpa only [nb052_alpha_dummy_060, nb052_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb052_fresh_055 :
    (nb052_alpha_dummy_068) ∉
      (((Class.cv (nb052_alpha_dummy_057))).fv ∪ ((Class.cv (nb052_alpha_dummy_057))).fv) :=
  by
  simpa only [nb052_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_057))).fv ∪ ((Class.cv (nb052_alpha_dummy_057))).fv)
      0

theorem nb052_fresh_056 :
    (nb052_alpha_dummy_064) ∉
      (((Class.cv (nb052_alpha_dummy_057))).fv ∪ ((Class.cv (nb052_alpha_dummy_058))).fv) :=
  by
  simpa only [nb052_alpha_dummy_064] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_057))).fv ∪ ((Class.cv (nb052_alpha_dummy_058))).fv)
      0

theorem nb052_fresh_057 :
    (nb052_alpha_dummy_070) ∉
      (((Class.cv (nb052_alpha_dummy_058))).fv ∪ ((Class.cv (nb052_alpha_dummy_058))).fv) :=
  by
  simpa only [nb052_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_058))).fv ∪ ((Class.cv (nb052_alpha_dummy_058))).fv)
      0

theorem nb052_fresh_058 (x : Var) (y : Var) :
    (nb052_alpha_dummy_069 x y) ∉
      (((Class.cv (nb052_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_060 x y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_060 x y))).fv)
      0

theorem nb052_fresh_059 (x : Var) (y : Var) :
    (nb052_alpha_dummy_065 x y) ∉
      (((Class.cv (nb052_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_061 x y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_065] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_061 x y))).fv)
      0

theorem nb052_fresh_060 (x : Var) (y : Var) :
    (nb052_alpha_dummy_071 x y) ∉
      (((Class.cv (nb052_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_061 x y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb052_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_061 x y))).fv)
      0

theorem nb052_fresh_061 (x : Var) :
    (nb052_alpha_dummy_081 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb052_alpha_dummy_081] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 0

theorem nb052_fresh_062 (x : Var) (y : Var) :
    (nb052_alpha_dummy_016 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb052_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb052_fresh_063 (x : Var) (y : Var) :
    (nb052_alpha_dummy_017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb052_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb052_distinct_064 (x : Var) (y : Var) :
    (nb052_alpha_dummy_016 x y) ≠ (nb052_alpha_dummy_017 x y) := by
  simpa only [nb052_alpha_dummy_016, nb052_alpha_dummy_017] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb052_fresh_065 (y : Var) :
    (nb052_alpha_dummy_083 y) ∉ (((Class.cv y)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb052_alpha_dummy_083] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv y)).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C052C001Part002`. -/


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

theorem nb052_fresh_066 :
    (nb052_alpha_dummy_026) ∉
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_022)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_022)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_022))).fv) :=
  by
  simpa only [nb052_alpha_dummy_026] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_022)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_022)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_022))).fv)
      0

theorem nb052_fresh_067 (x : Var) (y : Var) :
    (nb052_alpha_dummy_027 x y) ∉
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_024 x y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_027] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_024 x y))).fv)
      0

theorem nb052_fresh_068 :
    (nb052_alpha_dummy_054) ∉
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_050))).fv) :=
  by
  simpa only [nb052_alpha_dummy_054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_050))).fv)
      0

theorem nb052_fresh_069 (x : Var) (y : Var) :
    (nb052_alpha_dummy_055 x y) ∉
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_052 x y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_052 x y))).fv)
      0

theorem nb052_fresh_070 :
    (nb052_alpha_dummy_010) ∉
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
                (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_006)
              (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
                (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_006)
              (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb052_fresh_071 (x : Var) (y : Var) :
    (nb052_alpha_dummy_011 x y) ∉
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb052_fresh_072 :
    (nb052_alpha_dummy_018) ∉
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_014)
              (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_014)
              (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_018] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_014)
              (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_014)
              (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb052_fresh_073 (x : Var) (y : Var) :
    (nb052_alpha_dummy_019 x y) ∉
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_016 x y)
              (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_016 x y)
              (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_019] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_016 x y)
              (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_016 x y)
              (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb052_fresh_074 :
    (nb052_alpha_dummy_078) ∉
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_000)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_078] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_000)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_001)))).fv)
      0

theorem nb052_fresh_075 :
    (nb052_alpha_dummy_038) ∉
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_030)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_030)))).fv)
      0

theorem nb052_fresh_076 (x : Var) (y : Var) :
    (nb052_alpha_dummy_039 x y) ∉
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_033 x y)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_033 x y)))).fv)
      0

theorem nb052_fresh_077 :
    (nb052_alpha_dummy_066) ∉
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_058)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_066] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_058)))).fv)
      0

theorem nb052_fresh_078 (x : Var) (y : Var) :
    (nb052_alpha_dummy_067 x y) ∉
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_061 x y)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_067] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_061 x y)))).fv)
      0

theorem nb052_fresh_079 (x : Var) (y : Var) :
    (nb052_alpha_dummy_079 x y) ∉
      (((syn_ccompl (Class.cv x))).fv ∪ ((syn_ccompl (Class.cv y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_079] using
    freshVar_not_mem (((syn_ccompl (Class.cv x))).fv ∪ ((syn_ccompl (Class.cv y))).fv) 0

theorem nb052_fresh_080 :
    (nb052_alpha_dummy_074) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_074] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb052_fresh_081 (x : Var) (y : Var) :
    (nb052_alpha_dummy_075 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_075] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb052_fresh_082 :
    (nb052_alpha_dummy_046) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_015))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_046] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_015))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb052_fresh_083 (x : Var) (y : Var) :
    (nb052_alpha_dummy_047 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb052_fresh_084 :
    (nb052_alpha_dummy_034) ∉
      (((syn_cnin (Class.cv (nb052_alpha_dummy_029)) (Class.cv (nb052_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_029))
            (Class.cv (nb052_alpha_dummy_030)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_034] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb052_alpha_dummy_029)) (Class.cv (nb052_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_029)) (Class.cv (nb052_alpha_dummy_030)))).fv)
      0

theorem nb052_fresh_085 (x : Var) (y : Var) :
    (nb052_alpha_dummy_035 x y) ∉
      (((syn_cnin (Class.cv (nb052_alpha_dummy_032 x y))
            (Class.cv (nb052_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_032 x y))
            (Class.cv (nb052_alpha_dummy_033 x y)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_035] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb052_alpha_dummy_032 x y))
            (Class.cv (nb052_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_032 x y))
            (Class.cv (nb052_alpha_dummy_033 x y)))).fv)
      0

theorem nb052_fresh_086 :
    (nb052_alpha_dummy_062) ∉
      (((syn_cnin (Class.cv (nb052_alpha_dummy_057)) (Class.cv (nb052_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_057))
            (Class.cv (nb052_alpha_dummy_058)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_062] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb052_alpha_dummy_057)) (Class.cv (nb052_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_057)) (Class.cv (nb052_alpha_dummy_058)))).fv)
      0

theorem nb052_fresh_087 (x : Var) (y : Var) :
    (nb052_alpha_dummy_063 x y) ∉
      (((syn_cnin (Class.cv (nb052_alpha_dummy_060 x y))
            (Class.cv (nb052_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_060 x y))
            (Class.cv (nb052_alpha_dummy_061 x y)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_063] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb052_alpha_dummy_060 x y))
            (Class.cv (nb052_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_060 x y))
            (Class.cv (nb052_alpha_dummy_061 x y)))).fv)
      0

theorem nb052_fresh_088 :
    (nb052_alpha_dummy_006) ∉
      (((syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb052_alpha_dummy_002))).fv) :=
  by
  simpa only [nb052_alpha_dummy_006] using
    freshVar_not_mem
      (((syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb052_alpha_dummy_002))).fv)
      0

theorem nb052_fresh_089 :
    (nb052_alpha_dummy_007) ∉
      (((syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb052_alpha_dummy_002))).fv) :=
  by
  simpa only [nb052_alpha_dummy_007] using
    freshVar_not_mem
      (((syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb052_alpha_dummy_002))).fv)
      1

theorem nb052_distinct_090 : (nb052_alpha_dummy_006) ≠ (nb052_alpha_dummy_007) := by
  simpa only [nb052_alpha_dummy_006, nb052_alpha_dummy_007] using
    (freshVar_injective (((syn_cop (Class.cv (nb052_alpha_dummy_000))
            (Class.cv (nb052_alpha_dummy_001)))).fv ∪ ((Class.cv (nb052_alpha_dummy_002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb052_fresh_091 (x : Var) (y : Var) :
    (nb052_alpha_dummy_008 x y) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_003 x y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb052_alpha_dummy_003 x y))).fv)
      0

theorem nb052_fresh_092 (x : Var) (y : Var) :
    (nb052_alpha_dummy_009 x y) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_003 x y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb052_alpha_dummy_003 x y))).fv)
      1

theorem nb052_distinct_093 (x : Var) (y : Var) :
    (nb052_alpha_dummy_008 x y) ≠ (nb052_alpha_dummy_009 x y) := by
  simpa only [nb052_alpha_dummy_008, nb052_alpha_dummy_009] using
    (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_003 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb052_fresh_094 :
    (nb052_alpha_dummy_076) ∉
      (((syn_cphi (Class.cv (nb052_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_007)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_076] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb052_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_007)))).fv)
      0

theorem nb052_fresh_095 (x : Var) (y : Var) :
    (nb052_alpha_dummy_077 x y) ∉
      (((syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))).fv)
      0

theorem nb052_fresh_096 :
    (nb052_alpha_dummy_048) ∉
      (((syn_cphi (Class.cv (nb052_alpha_dummy_015)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_015)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb052_alpha_dummy_015)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_015)))).fv)
      0

theorem nb052_fresh_097 (x : Var) (y : Var) :
    (nb052_alpha_dummy_049 x y) ∉
      (((syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))).fv)
      0

theorem nb052_fresh_098 :
    (nb052_alpha_dummy_002) ∉
      (({(nb052_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb052_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cun (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb052_alpha_dummy_002] using
    freshVar_not_mem
      (({(nb052_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb052_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cun (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv)
      0

theorem nb052_fresh_099 :
    (nb052_alpha_dummy_004) ∉
      (({(nb052_alpha_dummy_000)} : Finset Var) ∪ ({(nb052_alpha_dummy_001)} : Finset Var) ∪
          ({(nb052_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb052_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb052_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_002))
              (syn_cun (Class.cv (nb052_alpha_dummy_000))
                (Class.cv (nb052_alpha_dummy_001)))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_004] using
    freshVar_not_mem
      (({(nb052_alpha_dummy_000)} : Finset Var) ∪ ({(nb052_alpha_dummy_001)} : Finset Var) ∪
          ({(nb052_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb052_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb052_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_002))
              (syn_cun (Class.cv (nb052_alpha_dummy_000))
                (Class.cv (nb052_alpha_dummy_001)))))).fv)
      0

theorem nb052_fresh_100 (x : Var) (y : Var) :
    (nb052_alpha_dummy_003 x y) ∉
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cun (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb052_alpha_dummy_003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cun (Class.cv x) (Class.cv y))).fv)
      0

theorem nb052_fresh_101 (x : Var) (y : Var) :
    (nb052_alpha_dummy_005 x y) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb052_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_003 x y))
              (syn_cun (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb052_alpha_dummy_005] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb052_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_003 x y))
              (syn_cun (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb052_fresh_102 : (nb052_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb052_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb052_fresh_103 : (nb052_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb052_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb052_distinct_104 : (nb052_alpha_dummy_000) ≠ (nb052_alpha_dummy_001) := by
  simpa only [nb052_alpha_dummy_000, nb052_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb052_support_mem_0000 :
    (nb052_alpha_dummy_000) ∈
      (({(nb052_alpha_dummy_000)} : Finset Var) ∪ ({(nb052_alpha_dummy_001)} : Finset Var) ∪
          ({(nb052_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb052_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb052_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_002))
              (syn_cun (Class.cv (nb052_alpha_dummy_000))
                (Class.cv (nb052_alpha_dummy_001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0001 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb052_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_003 x y))
              (syn_cun (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0002 :
    (nb052_alpha_dummy_001) ∈
      (({(nb052_alpha_dummy_000)} : Finset Var) ∪ ({(nb052_alpha_dummy_001)} : Finset Var) ∪
          ({(nb052_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb052_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb052_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_002))
              (syn_cun (Class.cv (nb052_alpha_dummy_000))
                (Class.cv (nb052_alpha_dummy_001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0003 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb052_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_003 x y))
              (syn_cun (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0004 :
    (nb052_alpha_dummy_002) ∈
      (({(nb052_alpha_dummy_000)} : Finset Var) ∪ ({(nb052_alpha_dummy_001)} : Finset Var) ∪
          ({(nb052_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb052_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb052_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_002))
              (syn_cun (Class.cv (nb052_alpha_dummy_000))
                (Class.cv (nb052_alpha_dummy_001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0005 (x : Var) (y : Var) :
    (nb052_alpha_dummy_003 x y) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb052_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb052_alpha_dummy_003 x y))
              (syn_cun (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0006 :
    (nb052_alpha_dummy_000) ∈
      (({(nb052_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb052_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cun (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv) :=
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

theorem nb052_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cun (Class.cv x) (Class.cv y))).fv) :=
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

theorem nb052_support_mem_0008 :
    (nb052_alpha_dummy_000) ∈
      (((syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb052_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0009 :
    (nb052_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
                (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_006)
              (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0010 (x : Var) (y : Var) :
    x ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0011 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s := ((syn_ccompl (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))))))).fv)
        ((syn_ccompl (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0010 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0010 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0012 :
    (nb052_alpha_dummy_000) ∈
      (((Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
              (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cphi (Class.cv (nb052_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
              (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cphi (Class.cv (nb052_alpha_dummy_007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0013 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0010 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0010 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0014 :
    (nb052_alpha_dummy_000) ∈
      (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0015 :
    (nb052_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_014)
              (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_014)
              (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0016 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0017 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_016 x y)
              (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_016 x y)
              (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0018 :
    (nb052_alpha_dummy_000) ∈
      (((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cphi (Class.cv (nb052_alpha_dummy_015))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cphi (Class.cv (nb052_alpha_dummy_015))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0019 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0020 :
    (nb052_alpha_dummy_015) ∈ (((Class.cv (nb052_alpha_dummy_015))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0021 (x : Var) (y : Var) :
    (nb052_alpha_dummy_017 x y) ∈ (((Class.cv (nb052_alpha_dummy_017 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0022 :
    (nb052_alpha_dummy_022) ∈
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_022)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_022)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_022))).fv) :=
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

theorem nb052_support_mem_0023 (x : Var) (y : Var) :
    (nb052_alpha_dummy_024 x y) ∈
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_024 x y))).fv) :=
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

theorem nb052_support_mem_0024 :
    (nb052_alpha_dummy_022) ∈
      (((Class.cv (nb052_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0025 (x : Var) (y : Var) :
    (nb052_alpha_dummy_024 x y) ∈
      (((Class.cv (nb052_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0026 :
    (nb052_alpha_dummy_029) ∈
      (((syn_cnin (Class.cv (nb052_alpha_dummy_029)) (Class.cv (nb052_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_029))
            (Class.cv (nb052_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0027 (x : Var) (y : Var) :
    (nb052_alpha_dummy_032 x y) ∈
      (((syn_cnin (Class.cv (nb052_alpha_dummy_032 x y))
            (Class.cv (nb052_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_032 x y))
            (Class.cv (nb052_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0028 :
    (nb052_alpha_dummy_029) ∈
      (((Class.cv (nb052_alpha_dummy_029))).fv ∪ ((Class.cv (nb052_alpha_dummy_030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0029 (x : Var) (y : Var) :
    (nb052_alpha_dummy_032 x y) ∈
      (((Class.cv (nb052_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0030 :
    (nb052_alpha_dummy_030) ∈
      (((syn_cnin (Class.cv (nb052_alpha_dummy_029)) (Class.cv (nb052_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_029))
            (Class.cv (nb052_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0031 (x : Var) (y : Var) :
    (nb052_alpha_dummy_033 x y) ∈
      (((syn_cnin (Class.cv (nb052_alpha_dummy_032 x y))
            (Class.cv (nb052_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_032 x y))
            (Class.cv (nb052_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0032 :
    (nb052_alpha_dummy_030) ∈
      (((Class.cv (nb052_alpha_dummy_029))).fv ∪ ((Class.cv (nb052_alpha_dummy_030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0033 (x : Var) (y : Var) :
    (nb052_alpha_dummy_033 x y) ∈
      (((Class.cv (nb052_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0034 :
    (nb052_alpha_dummy_029) ∈
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0035 (x : Var) (y : Var) :
    (nb052_alpha_dummy_032 x y) ∈
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0036 :
    (nb052_alpha_dummy_029) ∈
      (((Class.cv (nb052_alpha_dummy_029))).fv ∪ ((Class.cv (nb052_alpha_dummy_029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0037 (x : Var) (y : Var) :
    (nb052_alpha_dummy_032 x y) ∈
      (((Class.cv (nb052_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_032 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0038 :
    (nb052_alpha_dummy_030) ∈
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0039 (x : Var) (y : Var) :
    (nb052_alpha_dummy_033 x y) ∈
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0040 :
    (nb052_alpha_dummy_030) ∈
      (((Class.cv (nb052_alpha_dummy_030))).fv ∪ ((Class.cv (nb052_alpha_dummy_030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0041 (x : Var) (y : Var) :
    (nb052_alpha_dummy_033 x y) ∈
      (((Class.cv (nb052_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0042 :
    (nb052_alpha_dummy_001) ∈
      (({(nb052_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb052_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cun (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0043 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cun (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0044 :
    (nb052_alpha_dummy_001) ∈
      (((syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb052_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0045 :
    (nb052_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
                (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_006)
              (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0046 (x : Var) (y : Var) :
    y ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0047 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s := ((syn_ccompl (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))))))).fv)
        ((syn_ccompl (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0046 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0046 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0048 :
    (nb052_alpha_dummy_001) ∈
      (((Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
              (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cphi (Class.cv (nb052_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
              (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cphi (Class.cv (nb052_alpha_dummy_007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0049 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0046 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0046 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0050 :
    (nb052_alpha_dummy_001) ∈
      (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0051 :
    (nb052_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_014)
              (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_014)
              (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0052 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0053 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_016 x y)
              (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_016 x y)
              (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0054 :
    (nb052_alpha_dummy_001) ∈
      (((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_014)
            (syn_wrex (nb052_alpha_dummy_015) (Class.cv (nb052_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0055 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_016 x y)
            (syn_wrex (nb052_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0056 :
    (nb052_alpha_dummy_015) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_015))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0057 (x : Var) (y : Var) :
    (nb052_alpha_dummy_017 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_017 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0058 :
    (nb052_alpha_dummy_015) ∈
      (((syn_cphi (Class.cv (nb052_alpha_dummy_015)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_015)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0059 (x : Var) (y : Var) :
    (nb052_alpha_dummy_017 x y) ∈
      (((syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_017 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0060 :
    (nb052_alpha_dummy_007) ∈ (((Class.cv (nb052_alpha_dummy_007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0061 (x : Var) (y : Var) :
    (nb052_alpha_dummy_009 x y) ∈ (((Class.cv (nb052_alpha_dummy_009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0062 :
    (nb052_alpha_dummy_050) ∈
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_050))).fv) :=
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

theorem nb052_support_mem_0063 (x : Var) (y : Var) :
    (nb052_alpha_dummy_052 x y) ∈
      (((Wff.classMem (Class.cv (nb052_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb052_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb052_alpha_dummy_052 x y))).fv) :=
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

theorem nb052_support_mem_0064 :
    (nb052_alpha_dummy_050) ∈
      (((Class.cv (nb052_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0065 (x : Var) (y : Var) :
    (nb052_alpha_dummy_052 x y) ∈
      (((Class.cv (nb052_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0066 :
    (nb052_alpha_dummy_057) ∈
      (((syn_cnin (Class.cv (nb052_alpha_dummy_057)) (Class.cv (nb052_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_057))
            (Class.cv (nb052_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0067 (x : Var) (y : Var) :
    (nb052_alpha_dummy_060 x y) ∈
      (((syn_cnin (Class.cv (nb052_alpha_dummy_060 x y))
            (Class.cv (nb052_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_060 x y))
            (Class.cv (nb052_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0068 :
    (nb052_alpha_dummy_057) ∈
      (((Class.cv (nb052_alpha_dummy_057))).fv ∪ ((Class.cv (nb052_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0069 (x : Var) (y : Var) :
    (nb052_alpha_dummy_060 x y) ∈
      (((Class.cv (nb052_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0070 :
    (nb052_alpha_dummy_058) ∈
      (((syn_cnin (Class.cv (nb052_alpha_dummy_057)) (Class.cv (nb052_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_057))
            (Class.cv (nb052_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0071 (x : Var) (y : Var) :
    (nb052_alpha_dummy_061 x y) ∈
      (((syn_cnin (Class.cv (nb052_alpha_dummy_060 x y))
            (Class.cv (nb052_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb052_alpha_dummy_060 x y))
            (Class.cv (nb052_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0072 :
    (nb052_alpha_dummy_058) ∈
      (((Class.cv (nb052_alpha_dummy_057))).fv ∪ ((Class.cv (nb052_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0073 (x : Var) (y : Var) :
    (nb052_alpha_dummy_061 x y) ∈
      (((Class.cv (nb052_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0074 :
    (nb052_alpha_dummy_057) ∈
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0075 (x : Var) (y : Var) :
    (nb052_alpha_dummy_060 x y) ∈
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0076 :
    (nb052_alpha_dummy_057) ∈
      (((Class.cv (nb052_alpha_dummy_057))).fv ∪ ((Class.cv (nb052_alpha_dummy_057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0077 (x : Var) (y : Var) :
    (nb052_alpha_dummy_060 x y) ∈
      (((Class.cv (nb052_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0078 :
    (nb052_alpha_dummy_058) ∈
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0079 (x : Var) (y : Var) :
    (nb052_alpha_dummy_061 x y) ∈
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0080 :
    (nb052_alpha_dummy_058) ∈
      (((Class.cv (nb052_alpha_dummy_058))).fv ∪ ((Class.cv (nb052_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0081 (x : Var) (y : Var) :
    (nb052_alpha_dummy_061 x y) ∈
      (((Class.cv (nb052_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0082 :
    (nb052_alpha_dummy_002) ∈
      (((syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb052_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0083 :
    (nb052_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_006) (syn_wrex (nb052_alpha_dummy_007)
                (syn_cop (Class.cv (nb052_alpha_dummy_000)) (Class.cv (nb052_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_006)
              (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0084 (x : Var) (y : Var) :
    (nb052_alpha_dummy_003 x y) ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052_alpha_dummy_003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0085 (x : Var) (y : Var) :
    (nb052_alpha_dummy_003 x y) ∈
      (((syn_ccompl (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_right (a := (nb052_alpha_dummy_003 x y)) (t := ((syn_ccompl
            (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
        ((syn_ccompl (Class.cab (nb052_alpha_dummy_008 x y)
              (syn_wrex (nb052_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0086 :
    (nb052_alpha_dummy_002) ∈
      (((Class.cab (nb052_alpha_dummy_006)
            (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_006)
            (syn_wrex (nb052_alpha_dummy_007) (Class.cv (nb052_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
