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

/-! Certificates from `NAR4C073C001Part001`. -/


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
noncomputable def nb073_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb073_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb073_alpha_dummy_002 : Var :=
  (freshVar (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
          ({(nb073_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
      ((syn_cxp (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_003 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
      ((syn_cxp (Class.cv x) (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_004 : Var :=
  (freshVar
    (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ({(nb073_alpha_dummy_001)} : Finset Var) ∪
        ({(nb073_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_000)) (syn_cvv))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_001)) (syn_cvv)))
          (Wff.classEq (Class.cv (nb073_alpha_dummy_002))
            (syn_cxp (Class.cv (nb073_alpha_dummy_000))
              (Class.cv (nb073_alpha_dummy_001)))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_005 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb073_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
          (Wff.classEq (Class.cv (nb073_alpha_dummy_003 x y))
            (syn_cxp (Class.cv x) (Class.cv y))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_006 : Var :=
  (freshVar (((syn_cop (Class.cv (nb073_alpha_dummy_000))
          (Class.cv (nb073_alpha_dummy_001)))).fv ∪ ((Class.cv (nb073_alpha_dummy_002))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_007 : Var :=
  (freshVar (((syn_cop (Class.cv (nb073_alpha_dummy_000))
          (Class.cv (nb073_alpha_dummy_001)))).fv ∪ ((Class.cv (nb073_alpha_dummy_002))).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_008 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_003 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_009 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_003 x y))).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_010 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
              (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cphi (Class.cv (nb073_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb073_alpha_dummy_006)
            (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_011 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_012 : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
            (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
              (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv ∪
      ((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
            (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
              (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_008 x y)
          (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
              (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv ∪
      ((Class.cab (nb073_alpha_dummy_008 x y)
          (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
              (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_014 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_015 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_018 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cphi (Class.cv (nb073_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_019 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_020 : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_014)
          (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
              (syn_cphi (Class.cv (nb073_alpha_dummy_015))))))).fv ∪
      ((Class.cab (nb073_alpha_dummy_014)
          (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
              (syn_cphi (Class.cv (nb073_alpha_dummy_015))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_016 x y)
          (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
              (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))).fv ∪
      ((Class.cab (nb073_alpha_dummy_016 x y) (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
              (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_022 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_015))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_023 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_015))).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_017 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_017 x y))).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_026 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073_alpha_dummy_022)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb073_alpha_dummy_022)) (syn_c1c))).fv ∪
      ((Class.cv (nb073_alpha_dummy_022))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_027 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb073_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb073_alpha_dummy_024 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_028 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_029 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_030 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb073_alpha_dummy_031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb073_alpha_dummy_034 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb073_alpha_dummy_029))
          (Class.cv (nb073_alpha_dummy_030)))).fv ∪
      ((syn_cnin (Class.cv (nb073_alpha_dummy_029)) (Class.cv (nb073_alpha_dummy_030)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_035 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb073_alpha_dummy_032 x y))
          (Class.cv (nb073_alpha_dummy_033 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb073_alpha_dummy_032 x y))
          (Class.cv (nb073_alpha_dummy_033 x y)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_036 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_029))).fv ∪ ((Class.cv (nb073_alpha_dummy_030))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_037 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_032 x y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_033 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_038 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb073_alpha_dummy_029)))).fv ∪
      ((syn_ccompl (Class.cv (nb073_alpha_dummy_030)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_039 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb073_alpha_dummy_032 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb073_alpha_dummy_033 x y)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_040 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_029))).fv ∪ ((Class.cv (nb073_alpha_dummy_029))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_041 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_032 x y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_032 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_042 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_030))).fv ∪ ((Class.cv (nb073_alpha_dummy_030))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_043 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_033 x y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_033 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_044 : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_014)
          (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_014)
          (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_016 x y)
          (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_016 x y)
          (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_046 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_015))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_047 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_048 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb073_alpha_dummy_015)))).fv ∪
      ((syn_cphi (Class.cv (nb073_alpha_dummy_015)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_049 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_050 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_007))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_051 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_007))).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_009 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_009 x y))).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073_alpha_dummy_050)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb073_alpha_dummy_050)) (syn_c1c))).fv ∪
      ((Class.cv (nb073_alpha_dummy_050))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb073_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb073_alpha_dummy_052 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_056 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_057 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_058 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb073_alpha_dummy_059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb073_alpha_dummy_062 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb073_alpha_dummy_057))
          (Class.cv (nb073_alpha_dummy_058)))).fv ∪
      ((syn_cnin (Class.cv (nb073_alpha_dummy_057)) (Class.cv (nb073_alpha_dummy_058)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_063 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y))
          (Class.cv (nb073_alpha_dummy_061 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y))
          (Class.cv (nb073_alpha_dummy_061 x y)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_064 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_061 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_066 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb073_alpha_dummy_057)))).fv ∪
      ((syn_ccompl (Class.cv (nb073_alpha_dummy_058)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_067 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb073_alpha_dummy_060 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb073_alpha_dummy_061 x y)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_068 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_057))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_060 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_070 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_058))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_061 x y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_061 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_072 : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_006)
          (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_006)
          (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_008 x y)
          (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_008 x y)
          (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_074 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_007))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_075 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_076 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb073_alpha_dummy_007)))).fv ∪
      ((syn_cphi (Class.cv (nb073_alpha_dummy_007)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_077 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_078 : Var :=
  (freshVar
    (({(nb073_alpha_dummy_014)} : Finset Var) ∪ ({(nb073_alpha_dummy_015)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_014))
            (Class.cv (nb073_alpha_dummy_000))) (Wff.classMem (Class.cv (nb073_alpha_dummy_015))
            (Class.cv (nb073_alpha_dummy_001))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_079 (x : Var) (y : Var) : Var :=
  (freshVar (({(nb073_alpha_dummy_016 x y)} : Finset Var) ∪
        ({(nb073_alpha_dummy_017 x y)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_016 x y)) (Class.cv x))
          (Wff.classMem (Class.cv (nb073_alpha_dummy_017 x y)) (Class.cv y)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_080 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_014))).fv ∪ ((Class.cv (nb073_alpha_dummy_015))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_081 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_014))).fv ∪ ((Class.cv (nb073_alpha_dummy_015))).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_082 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_017 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_083 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_017 x y))).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_084 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cphi (Class.cv (nb073_alpha_dummy_081)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_085 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_086 : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_080)
          (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
              (syn_cphi (Class.cv (nb073_alpha_dummy_081))))))).fv ∪
      ((Class.cab (nb073_alpha_dummy_080)
          (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
              (syn_cphi (Class.cv (nb073_alpha_dummy_081))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_087 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_082 x y)
          (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
              (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))).fv ∪
      ((Class.cab (nb073_alpha_dummy_082 x y)
          (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
              (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_088 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_081))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_089 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_081))).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_090 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_083 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_091 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_083 x y))).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_092 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073_alpha_dummy_088)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb073_alpha_dummy_088)) (syn_c1c))).fv ∪
      ((Class.cv (nb073_alpha_dummy_088))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_093 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073_alpha_dummy_090 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb073_alpha_dummy_090 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb073_alpha_dummy_090 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_094 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_095 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_096 : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb073_alpha_dummy_097 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_098 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb073_alpha_dummy_099 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb073_alpha_dummy_100 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb073_alpha_dummy_095))
          (Class.cv (nb073_alpha_dummy_096)))).fv ∪
      ((syn_cnin (Class.cv (nb073_alpha_dummy_095)) (Class.cv (nb073_alpha_dummy_096)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_101 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y))
          (Class.cv (nb073_alpha_dummy_099 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y))
          (Class.cv (nb073_alpha_dummy_099 x y)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_102 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_103 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_099 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_104 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb073_alpha_dummy_095)))).fv ∪
      ((syn_ccompl (Class.cv (nb073_alpha_dummy_096)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_105 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb073_alpha_dummy_098 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb073_alpha_dummy_099 x y)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_106 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_095))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_107 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_098 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_108 : Var :=
  (freshVar
    (((Class.cv (nb073_alpha_dummy_096))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_109 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073_alpha_dummy_099 x y))).fv ∪
      ((Class.cv (nb073_alpha_dummy_099 x y))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_110 : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_080)
          (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_080)
          (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_111 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073_alpha_dummy_082 x y)
          (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_082 x y)
          (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
              (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_112 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_081))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_113 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_114 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb073_alpha_dummy_081)))).fv ∪
      ((syn_cphi (Class.cv (nb073_alpha_dummy_081)))).fv) 0)

@[expose]
noncomputable def nb073_alpha_dummy_115 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))).fv) 0)

theorem nb073_fresh_000 :
    (nb073_alpha_dummy_072) ∉
      (((Class.cab (nb073_alpha_dummy_006)
            (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_006)
            (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_006)
            (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_006)
            (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb073_fresh_001 :
    (nb073_alpha_dummy_012) ∉
      (((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
              (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
              (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
              (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
              (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv)
      0

theorem nb073_fresh_002 (x : Var) (y : Var) :
    (nb073_alpha_dummy_073 x y) ∉
      (((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb073_fresh_003 (x : Var) (y : Var) :
    (nb073_alpha_dummy_013 x y) ∉
      (((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_013] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv)
      0

theorem nb073_fresh_004 :
    (nb073_alpha_dummy_020) ∉
      (((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cphi (Class.cv (nb073_alpha_dummy_015))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cphi (Class.cv (nb073_alpha_dummy_015))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_020] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cphi (Class.cv (nb073_alpha_dummy_015))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cphi (Class.cv (nb073_alpha_dummy_015))))))).fv)
      0

theorem nb073_fresh_005 :
    (nb073_alpha_dummy_044) ∉
      (((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb073_fresh_006 (x : Var) (y : Var) :
    (nb073_alpha_dummy_021 x y) ∉
      (((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_021] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))).fv)
      0

theorem nb073_fresh_007 (x : Var) (y : Var) :
    (nb073_alpha_dummy_045 x y) ∉
      (((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb073_fresh_008 :
    (nb073_alpha_dummy_086) ∉
      (((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cphi (Class.cv (nb073_alpha_dummy_081))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cphi (Class.cv (nb073_alpha_dummy_081))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_086] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cphi (Class.cv (nb073_alpha_dummy_081))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cphi (Class.cv (nb073_alpha_dummy_081))))))).fv)
      0

theorem nb073_fresh_009 :
    (nb073_alpha_dummy_110) ∉
      (((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_110] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb073_fresh_010 (x : Var) (y : Var) :
    (nb073_alpha_dummy_087 x y) ∉
      (((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_087] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))).fv)
      0

theorem nb073_fresh_011 (x : Var) (y : Var) :
    (nb073_alpha_dummy_111 x y) ∉
      (((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_111] using
    freshVar_not_mem
      (((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb073_fresh_012 :
    (nb073_alpha_dummy_014) ∉
      (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv) :=
  by
  simpa only [nb073_alpha_dummy_014] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv)
      0

theorem nb073_fresh_013 :
    (nb073_alpha_dummy_015) ∉
      (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv) :=
  by
  simpa only [nb073_alpha_dummy_015] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv)
      1

theorem nb073_distinct_014 : (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_015) := by
  simpa only [nb073_alpha_dummy_014, nb073_alpha_dummy_015] using
    (freshVar_injective
      (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_fresh_015 :
    (nb073_alpha_dummy_050) ∉ (((Class.cv (nb073_alpha_dummy_007))).fv) := by
  simpa only [nb073_alpha_dummy_050] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_007))).fv) 0

theorem nb073_fresh_016 :
    (nb073_alpha_dummy_051) ∉ (((Class.cv (nb073_alpha_dummy_007))).fv) := by
  simpa only [nb073_alpha_dummy_051] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_007))).fv) 1

theorem nb073_distinct_017 : (nb073_alpha_dummy_050) ≠ (nb073_alpha_dummy_051) := by
  simpa only [nb073_alpha_dummy_050, nb073_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_007))).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_018 (x : Var) (y : Var) :
    (nb073_alpha_dummy_052 x y) ∉ (((Class.cv (nb073_alpha_dummy_009 x y))).fv) := by
  simpa only [nb073_alpha_dummy_052] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_009 x y))).fv) 0

theorem nb073_fresh_019 (x : Var) (y : Var) :
    (nb073_alpha_dummy_053 x y) ∉ (((Class.cv (nb073_alpha_dummy_009 x y))).fv) := by
  simpa only [nb073_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_009 x y))).fv) 1

theorem nb073_distinct_020 (x : Var) (y : Var) :
    (nb073_alpha_dummy_052 x y) ≠ (nb073_alpha_dummy_053 x y) := by
  simpa only [nb073_alpha_dummy_052, nb073_alpha_dummy_053] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_009 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb073_fresh_021 :
    (nb073_alpha_dummy_080) ∉
      (((Class.cv (nb073_alpha_dummy_014))).fv ∪ ((Class.cv (nb073_alpha_dummy_015))).fv) :=
  by
  simpa only [nb073_alpha_dummy_080] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_014))).fv ∪ ((Class.cv (nb073_alpha_dummy_015))).fv)
      0

theorem nb073_fresh_022 :
    (nb073_alpha_dummy_081) ∉
      (((Class.cv (nb073_alpha_dummy_014))).fv ∪ ((Class.cv (nb073_alpha_dummy_015))).fv) :=
  by
  simpa only [nb073_alpha_dummy_081] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_014))).fv ∪ ((Class.cv (nb073_alpha_dummy_015))).fv)
      1

theorem nb073_distinct_023 : (nb073_alpha_dummy_080) ≠ (nb073_alpha_dummy_081) := by
  simpa only [nb073_alpha_dummy_080, nb073_alpha_dummy_081] using
    (freshVar_injective
      (((Class.cv (nb073_alpha_dummy_014))).fv ∪ ((Class.cv (nb073_alpha_dummy_015))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_fresh_024 :
    (nb073_alpha_dummy_022) ∉ (((Class.cv (nb073_alpha_dummy_015))).fv) := by
  simpa only [nb073_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_015))).fv) 0

theorem nb073_fresh_025 :
    (nb073_alpha_dummy_023) ∉ (((Class.cv (nb073_alpha_dummy_015))).fv) := by
  simpa only [nb073_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_015))).fv) 1

theorem nb073_distinct_026 : (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_023) := by
  simpa only [nb073_alpha_dummy_022, nb073_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_015))).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_027 (x : Var) (y : Var) :
    (nb073_alpha_dummy_082 x y) ∉
      (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_017 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_082] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_017 x y))).fv)
      0

theorem nb073_fresh_028 (x : Var) (y : Var) :
    (nb073_alpha_dummy_083 x y) ∉
      (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_017 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_083] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_017 x y))).fv)
      1

theorem nb073_distinct_029 (x : Var) (y : Var) :
    (nb073_alpha_dummy_082 x y) ≠ (nb073_alpha_dummy_083 x y) := by
  simpa only [nb073_alpha_dummy_082, nb073_alpha_dummy_083] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_017 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_030 (x : Var) (y : Var) :
    (nb073_alpha_dummy_024 x y) ∉ (((Class.cv (nb073_alpha_dummy_017 x y))).fv) := by
  simpa only [nb073_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_017 x y))).fv) 0

theorem nb073_fresh_031 (x : Var) (y : Var) :
    (nb073_alpha_dummy_025 x y) ∉ (((Class.cv (nb073_alpha_dummy_017 x y))).fv) := by
  simpa only [nb073_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_017 x y))).fv) 1

theorem nb073_distinct_032 (x : Var) (y : Var) :
    (nb073_alpha_dummy_024 x y) ≠ (nb073_alpha_dummy_025 x y) := by
  simpa only [nb073_alpha_dummy_024, nb073_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_017 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb073_fresh_033 :
    (nb073_alpha_dummy_028) ∉
      (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_028] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C073C001Part002`. -/


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

theorem nb073_fresh_034 :
    (nb073_alpha_dummy_029) ∉
      (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_029] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 1

theorem nb073_fresh_035 :
    (nb073_alpha_dummy_030) ∉
      (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_030] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 2

theorem nb073_distinct_036 : (nb073_alpha_dummy_028) ≠ (nb073_alpha_dummy_029) := by
  simpa only [nb073_alpha_dummy_028, nb073_alpha_dummy_029] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb073_distinct_037 : (nb073_alpha_dummy_028) ≠ (nb073_alpha_dummy_030) := by
  simpa only [nb073_alpha_dummy_028, nb073_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb073_distinct_038 : (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_030) := by
  simpa only [nb073_alpha_dummy_029, nb073_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb073_fresh_039 (x : Var) (y : Var) :
    (nb073_alpha_dummy_031 x y) ∉
      (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_031] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb073_fresh_040 (x : Var) (y : Var) :
    (nb073_alpha_dummy_032 x y) ∉
      (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_032] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb073_fresh_041 (x : Var) (y : Var) :
    (nb073_alpha_dummy_033 x y) ∉
      (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_033] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb073_distinct_042 (x : Var) (y : Var) :
    (nb073_alpha_dummy_031 x y) ≠ (nb073_alpha_dummy_032 x y) := by
  simpa only [nb073_alpha_dummy_031, nb073_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_distinct_043 (x : Var) (y : Var) :
    (nb073_alpha_dummy_031 x y) ≠ (nb073_alpha_dummy_033 x y) := by
  simpa only [nb073_alpha_dummy_031, nb073_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb073_distinct_044 (x : Var) (y : Var) :
    (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_033 x y) := by
  simpa only [nb073_alpha_dummy_032, nb073_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb073_fresh_045 :
    (nb073_alpha_dummy_040) ∉
      (((Class.cv (nb073_alpha_dummy_029))).fv ∪ ((Class.cv (nb073_alpha_dummy_029))).fv) :=
  by
  simpa only [nb073_alpha_dummy_040] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_029))).fv ∪ ((Class.cv (nb073_alpha_dummy_029))).fv)
      0

theorem nb073_fresh_046 :
    (nb073_alpha_dummy_036) ∉
      (((Class.cv (nb073_alpha_dummy_029))).fv ∪ ((Class.cv (nb073_alpha_dummy_030))).fv) :=
  by
  simpa only [nb073_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_029))).fv ∪ ((Class.cv (nb073_alpha_dummy_030))).fv)
      0

theorem nb073_fresh_047 :
    (nb073_alpha_dummy_042) ∉
      (((Class.cv (nb073_alpha_dummy_030))).fv ∪ ((Class.cv (nb073_alpha_dummy_030))).fv) :=
  by
  simpa only [nb073_alpha_dummy_042] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_030))).fv ∪ ((Class.cv (nb073_alpha_dummy_030))).fv)
      0

theorem nb073_fresh_048 (x : Var) (y : Var) :
    (nb073_alpha_dummy_041 x y) ∉
      (((Class.cv (nb073_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_032 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_041] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_032 x y))).fv)
      0

theorem nb073_fresh_049 (x : Var) (y : Var) :
    (nb073_alpha_dummy_037 x y) ∉
      (((Class.cv (nb073_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_033 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_033 x y))).fv)
      0

theorem nb073_fresh_050 (x : Var) (y : Var) :
    (nb073_alpha_dummy_043 x y) ∉
      (((Class.cv (nb073_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_033 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_033 x y))).fv)
      0

theorem nb073_fresh_051 :
    (nb073_alpha_dummy_056) ∉
      (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_056] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0

theorem nb073_fresh_052 :
    (nb073_alpha_dummy_057) ∉
      (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_057] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1

theorem nb073_fresh_053 :
    (nb073_alpha_dummy_058) ∉
      (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2

theorem nb073_distinct_054 : (nb073_alpha_dummy_056) ≠ (nb073_alpha_dummy_057) := by
  simpa only [nb073_alpha_dummy_056, nb073_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb073_distinct_055 : (nb073_alpha_dummy_056) ≠ (nb073_alpha_dummy_058) := by
  simpa only [nb073_alpha_dummy_056, nb073_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb073_distinct_056 : (nb073_alpha_dummy_057) ≠ (nb073_alpha_dummy_058) := by
  simpa only [nb073_alpha_dummy_057, nb073_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb073_fresh_057 (x : Var) (y : Var) :
    (nb073_alpha_dummy_059 x y) ∉
      (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb073_fresh_058 (x : Var) (y : Var) :
    (nb073_alpha_dummy_060 x y) ∉
      (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb073_fresh_059 (x : Var) (y : Var) :
    (nb073_alpha_dummy_061 x y) ∉
      (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb073_distinct_060 (x : Var) (y : Var) :
    (nb073_alpha_dummy_059 x y) ≠ (nb073_alpha_dummy_060 x y) := by
  simpa only [nb073_alpha_dummy_059, nb073_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_distinct_061 (x : Var) (y : Var) :
    (nb073_alpha_dummy_059 x y) ≠ (nb073_alpha_dummy_061 x y) := by
  simpa only [nb073_alpha_dummy_059, nb073_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb073_distinct_062 (x : Var) (y : Var) :
    (nb073_alpha_dummy_060 x y) ≠ (nb073_alpha_dummy_061 x y) := by
  simpa only [nb073_alpha_dummy_060, nb073_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb073_fresh_063 :
    (nb073_alpha_dummy_068) ∉
      (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_057))).fv) :=
  by
  simpa only [nb073_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_057))).fv)
      0

theorem nb073_fresh_064 :
    (nb073_alpha_dummy_064) ∉
      (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv) :=
  by
  simpa only [nb073_alpha_dummy_064] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv)
      0

theorem nb073_fresh_065 :
    (nb073_alpha_dummy_070) ∉
      (((Class.cv (nb073_alpha_dummy_058))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv) :=
  by
  simpa only [nb073_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_058))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv)
      0

theorem nb073_fresh_066 (x : Var) (y : Var) :
    (nb073_alpha_dummy_069 x y) ∉
      (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_060 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_060 x y))).fv)
      0

theorem nb073_fresh_067 (x : Var) (y : Var) :
    (nb073_alpha_dummy_065 x y) ∉
      (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_061 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_065] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_061 x y))).fv)
      0

theorem nb073_fresh_068 (x : Var) (y : Var) :
    (nb073_alpha_dummy_071 x y) ∉
      (((Class.cv (nb073_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_061 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_061 x y))).fv)
      0

theorem nb073_fresh_069 :
    (nb073_alpha_dummy_088) ∉ (((Class.cv (nb073_alpha_dummy_081))).fv) := by
  simpa only [nb073_alpha_dummy_088] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_081))).fv) 0

theorem nb073_fresh_070 :
    (nb073_alpha_dummy_089) ∉ (((Class.cv (nb073_alpha_dummy_081))).fv) := by
  simpa only [nb073_alpha_dummy_089] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_081))).fv) 1

theorem nb073_distinct_071 : (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_089) := by
  simpa only [nb073_alpha_dummy_088, nb073_alpha_dummy_089] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_081))).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_072 (x : Var) (y : Var) :
    (nb073_alpha_dummy_090 x y) ∉ (((Class.cv (nb073_alpha_dummy_083 x y))).fv) := by
  simpa only [nb073_alpha_dummy_090] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_083 x y))).fv) 0

theorem nb073_fresh_073 (x : Var) (y : Var) :
    (nb073_alpha_dummy_091 x y) ∉ (((Class.cv (nb073_alpha_dummy_083 x y))).fv) := by
  simpa only [nb073_alpha_dummy_091] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_083 x y))).fv) 1

theorem nb073_distinct_074 (x : Var) (y : Var) :
    (nb073_alpha_dummy_090 x y) ≠ (nb073_alpha_dummy_091 x y) := by
  simpa only [nb073_alpha_dummy_090, nb073_alpha_dummy_091] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_083 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb073_fresh_075 :
    (nb073_alpha_dummy_094) ∉
      (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_094] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) 0

theorem nb073_fresh_076 :
    (nb073_alpha_dummy_095) ∉
      (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_095] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) 1

theorem nb073_fresh_077 :
    (nb073_alpha_dummy_096) ∉
      (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_096] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) 2

theorem nb073_distinct_078 : (nb073_alpha_dummy_094) ≠ (nb073_alpha_dummy_095) := by
  simpa only [nb073_alpha_dummy_094, nb073_alpha_dummy_095] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb073_distinct_079 : (nb073_alpha_dummy_094) ≠ (nb073_alpha_dummy_096) := by
  simpa only [nb073_alpha_dummy_094, nb073_alpha_dummy_096] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb073_distinct_080 : (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_096) := by
  simpa only [nb073_alpha_dummy_095, nb073_alpha_dummy_096] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb073_fresh_081 (x : Var) (y : Var) :
    (nb073_alpha_dummy_097 x y) ∉
      (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_097] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb073_fresh_082 (x : Var) (y : Var) :
    (nb073_alpha_dummy_098 x y) ∉
      (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_098] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb073_fresh_083 (x : Var) (y : Var) :
    (nb073_alpha_dummy_099 x y) ∉
      (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb073_alpha_dummy_099] using
    freshVar_not_mem (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb073_distinct_084 (x : Var) (y : Var) :
    (nb073_alpha_dummy_097 x y) ≠ (nb073_alpha_dummy_098 x y) := by
  simpa only [nb073_alpha_dummy_097, nb073_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_distinct_085 (x : Var) (y : Var) :
    (nb073_alpha_dummy_097 x y) ≠ (nb073_alpha_dummy_099 x y) := by
  simpa only [nb073_alpha_dummy_097, nb073_alpha_dummy_099] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb073_distinct_086 (x : Var) (y : Var) :
    (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_099 x y) := by
  simpa only [nb073_alpha_dummy_098, nb073_alpha_dummy_099] using
    (freshVar_injective (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb073_fresh_087 :
    (nb073_alpha_dummy_106) ∉
      (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_095))).fv) :=
  by
  simpa only [nb073_alpha_dummy_106] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_095))).fv)
      0

theorem nb073_fresh_088 :
    (nb073_alpha_dummy_102) ∉
      (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv) :=
  by
  simpa only [nb073_alpha_dummy_102] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv)
      0

theorem nb073_fresh_089 :
    (nb073_alpha_dummy_108) ∉
      (((Class.cv (nb073_alpha_dummy_096))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv) :=
  by
  simpa only [nb073_alpha_dummy_108] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_096))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv)
      0

theorem nb073_fresh_090 (x : Var) (y : Var) :
    (nb073_alpha_dummy_107 x y) ∉
      (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_098 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_107] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_098 x y))).fv)
      0

theorem nb073_fresh_091 (x : Var) (y : Var) :
    (nb073_alpha_dummy_103 x y) ∉
      (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_099 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_103] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_099 x y))).fv)
      0

theorem nb073_fresh_092 (x : Var) (y : Var) :
    (nb073_alpha_dummy_109 x y) ∉
      (((Class.cv (nb073_alpha_dummy_099 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_099 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_109] using
    freshVar_not_mem
      (((Class.cv (nb073_alpha_dummy_099 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_099 x y))).fv)
      0

theorem nb073_fresh_093 (x : Var) (y : Var) :
    (nb073_alpha_dummy_016 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb073_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb073_fresh_094 (x : Var) (y : Var) :
    (nb073_alpha_dummy_017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb073_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb073_distinct_095 (x : Var) (y : Var) :
    (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_017 x y) := by
  simpa only [nb073_alpha_dummy_016, nb073_alpha_dummy_017] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_096 :
    (nb073_alpha_dummy_026) ∉
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_022)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_022)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_022))).fv) :=
  by
  simpa only [nb073_alpha_dummy_026] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_022)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_022)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_022))).fv)
      0

theorem nb073_fresh_097 (x : Var) (y : Var) :
    (nb073_alpha_dummy_027 x y) ∉
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_024 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_027] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_024 x y))).fv)
      0

theorem nb073_fresh_098 :
    (nb073_alpha_dummy_054) ∉
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_050))).fv) :=
  by
  simpa only [nb073_alpha_dummy_054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_050))).fv)
      0

theorem nb073_fresh_099 (x : Var) (y : Var) :
    (nb073_alpha_dummy_055 x y) ∉
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_052 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_052 x y))).fv)
      0

theorem nb073_fresh_100 :
    (nb073_alpha_dummy_092) ∉
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_088)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_088)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_088))).fv) :=
  by
  simpa only [nb073_alpha_dummy_092] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_088)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_088)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_088))).fv)
      0

theorem nb073_fresh_101 (x : Var) (y : Var) :
    (nb073_alpha_dummy_093 x y) ∉
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_090 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_090 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_090 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_093] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_090 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_090 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_090 x y))).fv)
      0

theorem nb073_fresh_102 :
    (nb073_alpha_dummy_010) ∉
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
                (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_006)
              (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
                (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_006)
              (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb073_fresh_103 (x : Var) (y : Var) :
    (nb073_alpha_dummy_011 x y) ∉
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_008 x y)
              (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_008 x y)
              (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_008 x y)
              (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_008 x y)
              (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb073_fresh_104 :
    (nb073_alpha_dummy_018) ∉
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_014)
              (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_014)
              (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_018] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_014)
              (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_014)
              (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb073_fresh_105 (x : Var) (y : Var) :
    (nb073_alpha_dummy_019 x y) ∉
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_016 x y)
              (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_016 x y)
              (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_019] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_016 x y)
              (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_016 x y)
              (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb073_fresh_106 :
    (nb073_alpha_dummy_084) ∉
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_080)
              (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_081)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_080)
              (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_084] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_080)
              (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_081)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_080)
              (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb073_fresh_107 (x : Var) (y : Var) :
    (nb073_alpha_dummy_085 x y) ∉
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_082 x y)
              (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_082 x y)
              (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_085] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_082 x y)
              (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_082 x y)
              (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb073_fresh_108 :
    (nb073_alpha_dummy_038) ∉
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_030)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_030)))).fv)
      0

theorem nb073_fresh_109 (x : Var) (y : Var) :
    (nb073_alpha_dummy_039 x y) ∉
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_033 x y)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_033 x y)))).fv)
      0

theorem nb073_fresh_110 :
    (nb073_alpha_dummy_066) ∉
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_058)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_066] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_058)))).fv)
      0

theorem nb073_fresh_111 (x : Var) (y : Var) :
    (nb073_alpha_dummy_067 x y) ∉
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_061 x y)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_067] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_061 x y)))).fv)
      0

theorem nb073_fresh_112 :
    (nb073_alpha_dummy_104) ∉
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_095)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_096)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_104] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_095)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_096)))).fv)
      0

theorem nb073_fresh_113 (x : Var) (y : Var) :
    (nb073_alpha_dummy_105 x y) ∉
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_098 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_099 x y)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_105] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_098 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_099 x y)))).fv)
      0

theorem nb073_fresh_114 :
    (nb073_alpha_dummy_074) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_074] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb073_fresh_115 (x : Var) (y : Var) :
    (nb073_alpha_dummy_075 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_075] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb073_fresh_116 :
    (nb073_alpha_dummy_046) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_015))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_046] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_015))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb073_fresh_117 (x : Var) (y : Var) :
    (nb073_alpha_dummy_047 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb073_fresh_118 :
    (nb073_alpha_dummy_112) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_081))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_112] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_081))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb073_fresh_119 (x : Var) (y : Var) :
    (nb073_alpha_dummy_113 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_113] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb073_fresh_120 :
    (nb073_alpha_dummy_034) ∉
      (((syn_cnin (Class.cv (nb073_alpha_dummy_029)) (Class.cv (nb073_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_029))
            (Class.cv (nb073_alpha_dummy_030)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_034] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb073_alpha_dummy_029)) (Class.cv (nb073_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_029)) (Class.cv (nb073_alpha_dummy_030)))).fv)
      0

theorem nb073_fresh_121 (x : Var) (y : Var) :
    (nb073_alpha_dummy_035 x y) ∉
      (((syn_cnin (Class.cv (nb073_alpha_dummy_032 x y))
            (Class.cv (nb073_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_032 x y))
            (Class.cv (nb073_alpha_dummy_033 x y)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_035] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb073_alpha_dummy_032 x y))
            (Class.cv (nb073_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_032 x y))
            (Class.cv (nb073_alpha_dummy_033 x y)))).fv)
      0

theorem nb073_fresh_122 :
    (nb073_alpha_dummy_062) ∉
      (((syn_cnin (Class.cv (nb073_alpha_dummy_057)) (Class.cv (nb073_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_057))
            (Class.cv (nb073_alpha_dummy_058)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_062] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb073_alpha_dummy_057)) (Class.cv (nb073_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_057)) (Class.cv (nb073_alpha_dummy_058)))).fv)
      0

theorem nb073_fresh_123 (x : Var) (y : Var) :
    (nb073_alpha_dummy_063 x y) ∉
      (((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y))
            (Class.cv (nb073_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y))
            (Class.cv (nb073_alpha_dummy_061 x y)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_063] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y))
            (Class.cv (nb073_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y))
            (Class.cv (nb073_alpha_dummy_061 x y)))).fv)
      0

theorem nb073_fresh_124 :
    (nb073_alpha_dummy_100) ∉
      (((syn_cnin (Class.cv (nb073_alpha_dummy_095)) (Class.cv (nb073_alpha_dummy_096)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_095))
            (Class.cv (nb073_alpha_dummy_096)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_100] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb073_alpha_dummy_095)) (Class.cv (nb073_alpha_dummy_096)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_095)) (Class.cv (nb073_alpha_dummy_096)))).fv)
      0

theorem nb073_fresh_125 (x : Var) (y : Var) :
    (nb073_alpha_dummy_101 x y) ∉
      (((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y))
            (Class.cv (nb073_alpha_dummy_099 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y))
            (Class.cv (nb073_alpha_dummy_099 x y)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_101] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y))
            (Class.cv (nb073_alpha_dummy_099 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y))
            (Class.cv (nb073_alpha_dummy_099 x y)))).fv)
      0

theorem nb073_fresh_126 :
    (nb073_alpha_dummy_006) ∉
      (((syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb073_alpha_dummy_002))).fv) :=
  by
  simpa only [nb073_alpha_dummy_006] using
    freshVar_not_mem
      (((syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb073_alpha_dummy_002))).fv)
      0

theorem nb073_fresh_127 :
    (nb073_alpha_dummy_007) ∉
      (((syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb073_alpha_dummy_002))).fv) :=
  by
  simpa only [nb073_alpha_dummy_007] using
    freshVar_not_mem
      (((syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb073_alpha_dummy_002))).fv)
      1

theorem nb073_distinct_128 : (nb073_alpha_dummy_006) ≠ (nb073_alpha_dummy_007) := by
  simpa only [nb073_alpha_dummy_006, nb073_alpha_dummy_007] using
    (freshVar_injective (((syn_cop (Class.cv (nb073_alpha_dummy_000))
            (Class.cv (nb073_alpha_dummy_001)))).fv ∪ ((Class.cv (nb073_alpha_dummy_002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_fresh_129 (x : Var) (y : Var) :
    (nb073_alpha_dummy_008 x y) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_003 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb073_alpha_dummy_003 x y))).fv)
      0

theorem nb073_fresh_130 (x : Var) (y : Var) :
    (nb073_alpha_dummy_009 x y) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_003 x y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb073_alpha_dummy_003 x y))).fv)
      1

theorem nb073_distinct_131 (x : Var) (y : Var) :
    (nb073_alpha_dummy_008 x y) ≠ (nb073_alpha_dummy_009 x y) := by
  simpa only [nb073_alpha_dummy_008, nb073_alpha_dummy_009] using
    (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_003 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_132 :
    (nb073_alpha_dummy_076) ∉
      (((syn_cphi (Class.cv (nb073_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_007)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_076] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb073_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_007)))).fv)
      0

theorem nb073_fresh_133 (x : Var) (y : Var) :
    (nb073_alpha_dummy_077 x y) ∉
      (((syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))).fv)
      0

theorem nb073_fresh_134 :
    (nb073_alpha_dummy_048) ∉
      (((syn_cphi (Class.cv (nb073_alpha_dummy_015)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_015)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb073_alpha_dummy_015)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_015)))).fv)
      0

theorem nb073_fresh_135 (x : Var) (y : Var) :
    (nb073_alpha_dummy_049 x y) ∉
      (((syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))).fv)
      0

theorem nb073_fresh_136 :
    (nb073_alpha_dummy_114) ∉
      (((syn_cphi (Class.cv (nb073_alpha_dummy_081)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_081)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_114] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb073_alpha_dummy_081)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_081)))).fv)
      0

theorem nb073_fresh_137 (x : Var) (y : Var) :
    (nb073_alpha_dummy_115 x y) ∉
      (((syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_115] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))).fv)
      0

theorem nb073_fresh_138 :
    (nb073_alpha_dummy_002) ∉
      (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb073_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cxp (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_002] using
    freshVar_not_mem
      (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb073_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cxp (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv)
      0

theorem nb073_fresh_139 :
    (nb073_alpha_dummy_004) ∉
      (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ({(nb073_alpha_dummy_001)} : Finset Var) ∪
          ({(nb073_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb073_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_002))
              (syn_cxp (Class.cv (nb073_alpha_dummy_000))
                (Class.cv (nb073_alpha_dummy_001)))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_004] using
    freshVar_not_mem
      (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ({(nb073_alpha_dummy_001)} : Finset Var) ∪
          ({(nb073_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb073_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_002))
              (syn_cxp (Class.cv (nb073_alpha_dummy_000))
                (Class.cv (nb073_alpha_dummy_001)))))).fv)
      0

theorem nb073_fresh_140 :
    (nb073_alpha_dummy_078) ∉
      (({(nb073_alpha_dummy_014)} : Finset Var) ∪ ({(nb073_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_014))
              (Class.cv (nb073_alpha_dummy_000)))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_015))
              (Class.cv (nb073_alpha_dummy_001))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_078] using
    freshVar_not_mem
      (({(nb073_alpha_dummy_014)} : Finset Var) ∪ ({(nb073_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_014))
              (Class.cv (nb073_alpha_dummy_000)))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_015))
              (Class.cv (nb073_alpha_dummy_001))))).fv)
      0

theorem nb073_fresh_141 (x : Var) (y : Var) :
    (nb073_alpha_dummy_079 x y) ∉
      (({(nb073_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb073_alpha_dummy_017 x y)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_017 x y)) (Class.cv y)))).fv) :=
  by
  simpa only [nb073_alpha_dummy_079] using
    freshVar_not_mem
      (({(nb073_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb073_alpha_dummy_017 x y)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_017 x y)) (Class.cv y)))).fv)
      0

theorem nb073_fresh_142 (x : Var) (y : Var) :
    (nb073_alpha_dummy_003 x y) ∉
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cxp (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb073_alpha_dummy_003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cxp (Class.cv x) (Class.cv y))).fv)
      0

theorem nb073_fresh_143 (x : Var) (y : Var) :
    (nb073_alpha_dummy_005 x y) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb073_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_003 x y))
              (syn_cxp (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb073_alpha_dummy_005] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb073_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_003 x y))
              (syn_cxp (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb073_fresh_144 : (nb073_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb073_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb073_fresh_145 : (nb073_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb073_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb073_distinct_146 : (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_001) := by
  simpa only [nb073_alpha_dummy_000, nb073_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb073_support_mem_0000 :
    (nb073_alpha_dummy_000) ∈
      (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ({(nb073_alpha_dummy_001)} : Finset Var) ∪
          ({(nb073_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb073_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_002))
              (syn_cxp (Class.cv (nb073_alpha_dummy_000))
                (Class.cv (nb073_alpha_dummy_001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0001 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb073_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_003 x y))
              (syn_cxp (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0002 :
    (nb073_alpha_dummy_001) ∈
      (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ({(nb073_alpha_dummy_001)} : Finset Var) ∪
          ({(nb073_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb073_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_002))
              (syn_cxp (Class.cv (nb073_alpha_dummy_000))
                (Class.cv (nb073_alpha_dummy_001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0003 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb073_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_003 x y))
              (syn_cxp (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0004 :
    (nb073_alpha_dummy_002) ∈
      (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ({(nb073_alpha_dummy_001)} : Finset Var) ∪
          ({(nb073_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb073_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_002))
              (syn_cxp (Class.cv (nb073_alpha_dummy_000))
                (Class.cv (nb073_alpha_dummy_001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0005 (x : Var) (y : Var) :
    (nb073_alpha_dummy_003 x y) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb073_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb073_alpha_dummy_003 x y))
              (syn_cxp (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0006 :
    (nb073_alpha_dummy_000) ∈
      (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb073_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cxp (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv) :=
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

theorem nb073_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cxp (Class.cv x) (Class.cv y))).fv) :=
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

theorem nb073_support_mem_0008 :
    (nb073_alpha_dummy_000) ∈
      (((syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb073_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0009 :
    (nb073_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
                (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_006)
              (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_006) from (by
          unfold nb073_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_007) from (by
            unfold nb073_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0010 (x : Var) (y : Var) :
    x ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0011 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_008 x y)
              (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_008 x y)
              (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb073_alpha_dummy_008 x y) from (by
          unfold nb073_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb073_alpha_dummy_009 x y) from (by
            unfold nb073_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0012 :
    (nb073_alpha_dummy_000) ∈
      (((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
              (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
              (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_006) from (by
          unfold nb073_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_007) from (by
            unfold nb073_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0013 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb073_alpha_dummy_008 x y) from (by
          unfold nb073_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb073_alpha_dummy_009 x y) from (by
            unfold nb073_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0014 :
    (nb073_alpha_dummy_000) ∈
      (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0015 :
    (nb073_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_014)
              (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_014)
              (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_014) from (by
          unfold nb073_alpha_dummy_014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_015) from (by
            unfold nb073_alpha_dummy_015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0016 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0017 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_016 x y)
              (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_016 x y)
              (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb073_alpha_dummy_016 x y) from (by
          unfold nb073_alpha_dummy_016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb073_alpha_dummy_017 x y) from (by
            unfold nb073_alpha_dummy_017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0018 :
    (nb073_alpha_dummy_000) ∈
      (((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cphi (Class.cv (nb073_alpha_dummy_015))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cphi (Class.cv (nb073_alpha_dummy_015))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_014) from (by
          unfold nb073_alpha_dummy_014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_015) from (by
            unfold nb073_alpha_dummy_015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0019 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb073_alpha_dummy_016 x y) from (by
          unfold nb073_alpha_dummy_016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb073_alpha_dummy_017 x y) from (by
            unfold nb073_alpha_dummy_017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0020 :
    (nb073_alpha_dummy_015) ∈ (((Class.cv (nb073_alpha_dummy_015))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0021 (x : Var) (y : Var) :
    (nb073_alpha_dummy_017 x y) ∈ (((Class.cv (nb073_alpha_dummy_017 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0022 :
    (nb073_alpha_dummy_022) ∈
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_022)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_022)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_022))).fv) :=
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

theorem nb073_support_mem_0023 (x : Var) (y : Var) :
    (nb073_alpha_dummy_024 x y) ∈
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_024 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_024 x y))).fv) :=
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

theorem nb073_support_mem_0024 :
    (nb073_alpha_dummy_022) ∈
      (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0025 (x : Var) (y : Var) :
    (nb073_alpha_dummy_024 x y) ∈
      (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0026 :
    (nb073_alpha_dummy_029) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_029)) (Class.cv (nb073_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_029))
            (Class.cv (nb073_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0027 (x : Var) (y : Var) :
    (nb073_alpha_dummy_032 x y) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_032 x y))
            (Class.cv (nb073_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_032 x y))
            (Class.cv (nb073_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0028 :
    (nb073_alpha_dummy_029) ∈
      (((Class.cv (nb073_alpha_dummy_029))).fv ∪ ((Class.cv (nb073_alpha_dummy_030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0029 (x : Var) (y : Var) :
    (nb073_alpha_dummy_032 x y) ∈
      (((Class.cv (nb073_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0030 :
    (nb073_alpha_dummy_030) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_029)) (Class.cv (nb073_alpha_dummy_030)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_029))
            (Class.cv (nb073_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0031 (x : Var) (y : Var) :
    (nb073_alpha_dummy_033 x y) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_032 x y))
            (Class.cv (nb073_alpha_dummy_033 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_032 x y))
            (Class.cv (nb073_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0032 :
    (nb073_alpha_dummy_030) ∈
      (((Class.cv (nb073_alpha_dummy_029))).fv ∪ ((Class.cv (nb073_alpha_dummy_030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C073C001Part003`. -/


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

theorem nb073_support_mem_0033 (x : Var) (y : Var) :
    (nb073_alpha_dummy_033 x y) ∈
      (((Class.cv (nb073_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0034 :
    (nb073_alpha_dummy_029) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0035 (x : Var) (y : Var) :
    (nb073_alpha_dummy_032 x y) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0036 :
    (nb073_alpha_dummy_029) ∈
      (((Class.cv (nb073_alpha_dummy_029))).fv ∪ ((Class.cv (nb073_alpha_dummy_029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0037 (x : Var) (y : Var) :
    (nb073_alpha_dummy_032 x y) ∈
      (((Class.cv (nb073_alpha_dummy_032 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_032 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0038 :
    (nb073_alpha_dummy_030) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_029)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0039 (x : Var) (y : Var) :
    (nb073_alpha_dummy_033 x y) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_032 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0040 :
    (nb073_alpha_dummy_030) ∈
      (((Class.cv (nb073_alpha_dummy_030))).fv ∪ ((Class.cv (nb073_alpha_dummy_030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0041 (x : Var) (y : Var) :
    (nb073_alpha_dummy_033 x y) ∈
      (((Class.cv (nb073_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0042 :
    (nb073_alpha_dummy_001) ∈
      (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪
            ({(nb073_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cxp (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0043 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
        ((syn_cxp (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0044 :
    (nb073_alpha_dummy_001) ∈
      (((syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb073_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0045 :
    (nb073_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
                (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_006)
              (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_006) from (by
          unfold nb073_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_007) from (by
            unfold nb073_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0046 (x : Var) (y : Var) :
    y ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0047 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_008 x y)
              (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_008 x y)
              (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb073_alpha_dummy_008 x y) from (by
          unfold nb073_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb073_alpha_dummy_009 x y) from (by
            unfold nb073_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0048 :
    (nb073_alpha_dummy_001) ∈
      (((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
              (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
              (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_006) from (by
          unfold nb073_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_007) from (by
            unfold nb073_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0049 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb073_alpha_dummy_008 x y) from (by
          unfold nb073_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb073_alpha_dummy_009 x y) from (by
            unfold nb073_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0050 :
    (nb073_alpha_dummy_001) ∈
      (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0051 :
    (nb073_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_014)
              (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_014)
              (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_014) from (by
          unfold nb073_alpha_dummy_014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_015) from (by
            unfold nb073_alpha_dummy_015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0052 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0053 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_016 x y)
              (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_016 x y)
              (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb073_alpha_dummy_016 x y) from (by
          unfold nb073_alpha_dummy_016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb073_alpha_dummy_017 x y) from (by
            unfold nb073_alpha_dummy_017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0054 :
    (nb073_alpha_dummy_001) ∈
      (((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_014) from (by
          unfold nb073_alpha_dummy_014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_015) from (by
            unfold nb073_alpha_dummy_015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0055 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb073_alpha_dummy_016 x y) from (by
          unfold nb073_alpha_dummy_016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb073_alpha_dummy_017 x y) from (by
            unfold nb073_alpha_dummy_017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0056 :
    (nb073_alpha_dummy_015) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_015))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0057 (x : Var) (y : Var) :
    (nb073_alpha_dummy_017 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0058 :
    (nb073_alpha_dummy_015) ∈
      (((syn_cphi (Class.cv (nb073_alpha_dummy_015)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_015)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0059 (x : Var) (y : Var) :
    (nb073_alpha_dummy_017 x y) ∈
      (((syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0060 :
    (nb073_alpha_dummy_007) ∈ (((Class.cv (nb073_alpha_dummy_007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0061 (x : Var) (y : Var) :
    (nb073_alpha_dummy_009 x y) ∈ (((Class.cv (nb073_alpha_dummy_009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0062 :
    (nb073_alpha_dummy_050) ∈
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_050)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_050)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_050))).fv) :=
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

theorem nb073_support_mem_0063 (x : Var) (y : Var) :
    (nb073_alpha_dummy_052 x y) ∈
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_052 x y))).fv) :=
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

theorem nb073_support_mem_0064 :
    (nb073_alpha_dummy_050) ∈
      (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0065 (x : Var) (y : Var) :
    (nb073_alpha_dummy_052 x y) ∈
      (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0066 :
    (nb073_alpha_dummy_057) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_057)) (Class.cv (nb073_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_057))
            (Class.cv (nb073_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0067 (x : Var) (y : Var) :
    (nb073_alpha_dummy_060 x y) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y))
            (Class.cv (nb073_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y))
            (Class.cv (nb073_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0068 :
    (nb073_alpha_dummy_057) ∈
      (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0069 (x : Var) (y : Var) :
    (nb073_alpha_dummy_060 x y) ∈
      (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0070 :
    (nb073_alpha_dummy_058) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_057)) (Class.cv (nb073_alpha_dummy_058)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_057))
            (Class.cv (nb073_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0071 (x : Var) (y : Var) :
    (nb073_alpha_dummy_061 x y) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y))
            (Class.cv (nb073_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y))
            (Class.cv (nb073_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0072 :
    (nb073_alpha_dummy_058) ∈
      (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0073 (x : Var) (y : Var) :
    (nb073_alpha_dummy_061 x y) ∈
      (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0074 :
    (nb073_alpha_dummy_057) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0075 (x : Var) (y : Var) :
    (nb073_alpha_dummy_060 x y) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0076 :
    (nb073_alpha_dummy_057) ∈
      (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0077 (x : Var) (y : Var) :
    (nb073_alpha_dummy_060 x y) ∈
      (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0078 :
    (nb073_alpha_dummy_058) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_057)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0079 (x : Var) (y : Var) :
    (nb073_alpha_dummy_061 x y) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0080 :
    (nb073_alpha_dummy_058) ∈
      (((Class.cv (nb073_alpha_dummy_058))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0081 (x : Var) (y : Var) :
    (nb073_alpha_dummy_061 x y) ∈
      (((Class.cv (nb073_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0082 :
    (nb073_alpha_dummy_002) ∈
      (((syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb073_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0083 :
    (nb073_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007)
                (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_006)
              (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_002) ≠ (nb073_alpha_dummy_006) from (by
          unfold nb073_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_002) ≠ (nb073_alpha_dummy_007) from (by
            unfold nb073_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0084 (x : Var) (y : Var) :
    (nb073_alpha_dummy_003 x y) ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0085 (x : Var) (y : Var) :
    (nb073_alpha_dummy_003 x y) ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_008 x y)
              (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_008 x y)
              (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_003 x y) ≠ (nb073_alpha_dummy_008 x y) from (by
          unfold nb073_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_003 x y) ≠ (nb073_alpha_dummy_009 x y) from (by
            unfold nb073_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0086 :
    (nb073_alpha_dummy_002) ∈
      (((Class.cab (nb073_alpha_dummy_006)
            (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_006)
            (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_002) ≠ (nb073_alpha_dummy_006) from (by
          unfold nb073_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_002) ≠ (nb073_alpha_dummy_007) from (by
            unfold nb073_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0087 (x : Var) (y : Var) :
    (nb073_alpha_dummy_003 x y) ∈
      (((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_008 x y)
            (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_003 x y) ≠ (nb073_alpha_dummy_008 x y) from (by
          unfold nb073_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_003 x y) ≠ (nb073_alpha_dummy_009 x y) from (by
            unfold nb073_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0088 :
    (nb073_alpha_dummy_007) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0089 (x : Var) (y : Var) :
    (nb073_alpha_dummy_009 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0090 :
    (nb073_alpha_dummy_007) ∈
      (((syn_cphi (Class.cv (nb073_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0091 (x : Var) (y : Var) :
    (nb073_alpha_dummy_009 x y) ∈
      (((syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0092 :
    (nb073_alpha_dummy_014) ∈
      (({(nb073_alpha_dummy_014)} : Finset Var) ∪ ({(nb073_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_014))
              (Class.cv (nb073_alpha_dummy_000)))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_015))
              (Class.cv (nb073_alpha_dummy_001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0093 (x : Var) (y : Var) :
    (nb073_alpha_dummy_016 x y) ∈
      (({(nb073_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb073_alpha_dummy_017 x y)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_017 x y)) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0094 :
    (nb073_alpha_dummy_015) ∈
      (({(nb073_alpha_dummy_014)} : Finset Var) ∪ ({(nb073_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_014))
              (Class.cv (nb073_alpha_dummy_000)))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_015))
              (Class.cv (nb073_alpha_dummy_001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0095 (x : Var) (y : Var) :
    (nb073_alpha_dummy_017 x y) ∈
      (({(nb073_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb073_alpha_dummy_017 x y)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_017 x y)) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0096 :
    (nb073_alpha_dummy_014) ∈
      (((Class.cv (nb073_alpha_dummy_014))).fv ∪ ((Class.cv (nb073_alpha_dummy_015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0097 :
    (nb073_alpha_dummy_014) ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_080)
              (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_081)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_080)
              (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_080) from (by
          unfold nb073_alpha_dummy_080;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_081) from (by
            unfold nb073_alpha_dummy_081;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0098 (x : Var) (y : Var) :
    (nb073_alpha_dummy_016 x y) ∈
      (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0099 (x : Var) (y : Var) :
    (nb073_alpha_dummy_016 x y) ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_082 x y)
              (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_082 x y)
              (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_082 x y) from (by
          unfold nb073_alpha_dummy_082;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_083 x y) from (by
            unfold nb073_alpha_dummy_083;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0100 :
    (nb073_alpha_dummy_014) ∈
      (((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cphi (Class.cv (nb073_alpha_dummy_081))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cphi (Class.cv (nb073_alpha_dummy_081))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_080) from (by
          unfold nb073_alpha_dummy_080;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_081) from (by
            unfold nb073_alpha_dummy_081;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0101 (x : Var) (y : Var) :
    (nb073_alpha_dummy_016 x y) ∈
      (((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))).fv ∪
        ((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_082 x y) from (by
          unfold nb073_alpha_dummy_082;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_083 x y) from (by
            unfold nb073_alpha_dummy_083;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0102 :
    (nb073_alpha_dummy_081) ∈ (((Class.cv (nb073_alpha_dummy_081))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0103 (x : Var) (y : Var) :
    (nb073_alpha_dummy_083 x y) ∈ (((Class.cv (nb073_alpha_dummy_083 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0104 :
    (nb073_alpha_dummy_088) ∈
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_088)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_088)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_088))).fv) :=
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

theorem nb073_support_mem_0105 (x : Var) (y : Var) :
    (nb073_alpha_dummy_090 x y) ∈
      (((Wff.classMem (Class.cv (nb073_alpha_dummy_090 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb073_alpha_dummy_090 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb073_alpha_dummy_090 x y))).fv) :=
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

theorem nb073_support_mem_0106 :
    (nb073_alpha_dummy_088) ∈
      (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0107 (x : Var) (y : Var) :
    (nb073_alpha_dummy_090 x y) ∈
      (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0108 :
    (nb073_alpha_dummy_095) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_095)) (Class.cv (nb073_alpha_dummy_096)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_095))
            (Class.cv (nb073_alpha_dummy_096)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0109 (x : Var) (y : Var) :
    (nb073_alpha_dummy_098 x y) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y))
            (Class.cv (nb073_alpha_dummy_099 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y))
            (Class.cv (nb073_alpha_dummy_099 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0110 :
    (nb073_alpha_dummy_095) ∈
      (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0111 (x : Var) (y : Var) :
    (nb073_alpha_dummy_098 x y) ∈
      (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_099 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0112 :
    (nb073_alpha_dummy_096) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_095)) (Class.cv (nb073_alpha_dummy_096)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_095))
            (Class.cv (nb073_alpha_dummy_096)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0113 (x : Var) (y : Var) :
    (nb073_alpha_dummy_099 x y) ∈
      (((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y))
            (Class.cv (nb073_alpha_dummy_099 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y))
            (Class.cv (nb073_alpha_dummy_099 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0114 :
    (nb073_alpha_dummy_096) ∈
      (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0115 (x : Var) (y : Var) :
    (nb073_alpha_dummy_099 x y) ∈
      (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_099 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0116 :
    (nb073_alpha_dummy_095) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_095)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_096)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0117 (x : Var) (y : Var) :
    (nb073_alpha_dummy_098 x y) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_098 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_099 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0118 :
    (nb073_alpha_dummy_095) ∈
      (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_095))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0119 (x : Var) (y : Var) :
    (nb073_alpha_dummy_098 x y) ∈
      (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_098 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0120 :
    (nb073_alpha_dummy_096) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_095)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_096)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0121 (x : Var) (y : Var) :
    (nb073_alpha_dummy_099 x y) ∈
      (((syn_ccompl (Class.cv (nb073_alpha_dummy_098 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb073_alpha_dummy_099 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0122 :
    (nb073_alpha_dummy_096) ∈
      (((Class.cv (nb073_alpha_dummy_096))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0123 (x : Var) (y : Var) :
    (nb073_alpha_dummy_099 x y) ∈
      (((Class.cv (nb073_alpha_dummy_099 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_099 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0124 :
    (nb073_alpha_dummy_015) ∈
      (((Class.cv (nb073_alpha_dummy_014))).fv ∪ ((Class.cv (nb073_alpha_dummy_015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0125 :
    (nb073_alpha_dummy_015) ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_080)
              (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_081)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_080)
              (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_080) from (by
          unfold nb073_alpha_dummy_080;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_081) from (by
            unfold nb073_alpha_dummy_081;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0126 (x : Var) (y : Var) :
    (nb073_alpha_dummy_017 x y) ∈
      (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪
        ((Class.cv (nb073_alpha_dummy_017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0127 (x : Var) (y : Var) :
    (nb073_alpha_dummy_017 x y) ∈
      (((syn_ccompl (Class.cab (nb073_alpha_dummy_082 x y)
              (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb073_alpha_dummy_082 x y)
              (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                  (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_082 x y) from (by
          unfold nb073_alpha_dummy_082;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_083 x y) from (by
            unfold nb073_alpha_dummy_083;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0128 :
    (nb073_alpha_dummy_015) ∈
      (((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_080) from (by
          unfold nb073_alpha_dummy_080;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_081) from (by
            unfold nb073_alpha_dummy_081;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0129 (x : Var) (y : Var) :
    (nb073_alpha_dummy_017 x y) ∈
      (((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_082 x y) from (by
          unfold nb073_alpha_dummy_082;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_083 x y) from (by
            unfold nb073_alpha_dummy_083;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0130 :
    (nb073_alpha_dummy_081) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_081))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0131 (x : Var) (y : Var) :
    (nb073_alpha_dummy_083 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0132 :
    (nb073_alpha_dummy_081) ∈
      (((syn_cphi (Class.cv (nb073_alpha_dummy_081)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_081)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0133 (x : Var) (y : Var) :
    (nb073_alpha_dummy_083 x y) ∈
      (((syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0134 :
    (nb073_alpha_dummy_000) ∈
      (({(nb073_alpha_dummy_014)} : Finset Var) ∪ ({(nb073_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_014))
              (Class.cv (nb073_alpha_dummy_000)))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_015))
              (Class.cv (nb073_alpha_dummy_001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0135 (x : Var) (y : Var) :
    x ∈
      (({(nb073_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb073_alpha_dummy_017 x y)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_017 x y)) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0136 :
    (nb073_alpha_dummy_001) ∈
      (({(nb073_alpha_dummy_014)} : Finset Var) ∪ ({(nb073_alpha_dummy_015)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_014))
              (Class.cv (nb073_alpha_dummy_000)))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_015))
              (Class.cv (nb073_alpha_dummy_001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0137 (x : Var) (y : Var) :
    y ∈
      (({(nb073_alpha_dummy_016 x y)} : Finset Var) ∪
          ({(nb073_alpha_dummy_017 x y)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073_alpha_dummy_017 x y)) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
