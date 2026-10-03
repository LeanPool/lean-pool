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

/-! Certificates from `NAR4C067C001Part001`. -/


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
noncomputable def nb067_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb067_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb067_alpha_dummy_002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

@[expose]
noncomputable def nb067_alpha_dummy_003 : Var :=
  (freshVar (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪
          ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ((syn_cvv)).fv ∪
      ((Class.cab (nb067_alpha_dummy_000)
          (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
            (Class.cv (nb067_alpha_dummy_001))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_004 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ({ y } : Finset Var) ∪ ((syn_cvv)).fv ∪
      ((Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_005 : Var :=
  (freshVar
    (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪
        ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv))
            (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv)))
          (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000)
              (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
                (Class.cv (nb067_alpha_dummy_001))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_006 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
          (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f))
            (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_007 : Var :=
  (freshVar (((syn_cop (Class.cv (nb067_alpha_dummy_001))
          (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_008 : Var :=
  (freshVar (((syn_cop (Class.cv (nb067_alpha_dummy_001))
          (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_009 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_010 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_011 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
              (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_007)
            (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_012 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f)
              (Class.cv (nb067_alpha_dummy_004 x y f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_013 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
            (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
              (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
            (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
              (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_014 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_009 x y f)
          (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_009 x y f)
          (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_015 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_016 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_018 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_019 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cphi (Class.cv (nb067_alpha_dummy_016)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_020 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_021 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_015)
          (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
              (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_015)
          (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
              (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_022 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_017 x y)
          (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
              (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
              (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_023 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_016))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_024 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_016))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_018 x y))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_026 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_018 x y))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_027 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_023)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_023)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_023))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_028 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_025 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_025 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_025 x y))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_029 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_030 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_031 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_034 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_035 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_030))
          (Class.cv (nb067_alpha_dummy_031)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_036 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y))
          (Class.cv (nb067_alpha_dummy_034 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y))
          (Class.cv (nb067_alpha_dummy_034 x y)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_037 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_038 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪
      ((Class.cv (nb067_alpha_dummy_034 x y))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_039 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_030)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_031)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_040 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_033 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_034 x y)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_041 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_030))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_042 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪
      ((Class.cv (nb067_alpha_dummy_033 x y))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_043 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_031))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_044 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_034 x y))).fv ∪
      ((Class.cv (nb067_alpha_dummy_034 x y))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_045 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_015)
          (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015)
          (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_046 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_017 x y)
          (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y)
          (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_047 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_016))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_048 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_049 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_050 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_051 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_008))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_052 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_008))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_053 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_054 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_055 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_051)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_051)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_051))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_056 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_053 x y f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_057 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_058 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_059 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_060 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_061 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_062 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_063 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_058))
          (Class.cv (nb067_alpha_dummy_059)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_064 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f))
          (Class.cv (nb067_alpha_dummy_062 x y f)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f))
          (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_065 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_066 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_067 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_058)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_059)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_068 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_061 x y f)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_069 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_058))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_070 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_061 x y f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_071 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_059))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_072 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_062 x y f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_073 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_007)
          (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007)
          (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_074 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_009 x y f)
          (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f)
          (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_075 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_008))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_076 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_077 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_078 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_079 : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
          (syn_ccom (Class.cv (nb067_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_080 (f : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_081 : Var :=
  (freshVar (((syn_ccom (Class.cv (nb067_alpha_dummy_000))
          (syn_ccnv (Class.cv (nb067_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_082 (f : Var) : Var :=
  (freshVar (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_083 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_084 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_085 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_086 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_087 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_088 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_089 : Var :=
  (freshVar
    (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪
      ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083))
              (syn_ccnv (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_085)))
            (syn_wbr (Class.cv (nb067_alpha_dummy_085)) (Class.cv (nb067_alpha_dummy_000))
              (Class.cv (nb067_alpha_dummy_084)))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_090 (f : Var) : Var :=
  (freshVar (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪
        ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa
            (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f))
              (Class.cv (nb067_alpha_dummy_088 f)))
            (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f)
              (Class.cv (nb067_alpha_dummy_087 f)))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_091 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_092 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_093 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_087 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_094 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_087 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_095 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cphi (Class.cv (nb067_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_096 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_097 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_091)
          (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
              (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_091)
          (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
              (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_098 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_093 f)
          (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_093 f)
          (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_099 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_092))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_100 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_092))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_101 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_094 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_102 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_094 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_103 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_099))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_104 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_101 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_105 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_106 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_107 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_108 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_109 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_110 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_111 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_106))
          (Class.cv (nb067_alpha_dummy_107)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_112 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_109 f))
          (Class.cv (nb067_alpha_dummy_110 f)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_109 f)) (Class.cv (nb067_alpha_dummy_110 f)))).fv)
    0)

@[expose]
noncomputable def nb067_alpha_dummy_113 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_114 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_110 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_115 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_106)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_107)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_116 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_109 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_110 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_117 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_106))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_118 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_109 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_119 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_107))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_120 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_110 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_110 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_121 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_091)
          (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091)
          (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_122 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_093 f)
          (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f)
          (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_123 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_092))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_124 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_125 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_126 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_127 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_128 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_129 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_088 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_130 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_088 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_131 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cphi (Class.cv (nb067_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_132 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_133 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_127)
          (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
              (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_127)
          (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
              (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_134 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_129 f)
          (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_129 f)
          (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_135 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_128))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_136 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_128))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_137 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_130 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_138 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_130 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_139 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_135))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_140 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_137 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_141 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_142 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_143 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_144 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_145 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_146 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_147 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_142))
          (Class.cv (nb067_alpha_dummy_143)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_148 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_145 f))
          (Class.cv (nb067_alpha_dummy_146 f)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))).fv)
    0)

@[expose]
noncomputable def nb067_alpha_dummy_149 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part002`. -/


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
noncomputable def nb067_alpha_dummy_150 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_146 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_151 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_142)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_143)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_152 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_145 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_146 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_153 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_142))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_154 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_145 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_155 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_143))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_156 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_146 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_146 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_157 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_127)
          (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127)
          (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_158 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_129 f)
          (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f)
          (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_159 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_128))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_160 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_161 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_162 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_163 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_164 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_165 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_166 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_167 : Var :=
  (freshVar
    (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000))
          (Class.cv (nb067_alpha_dummy_163)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_168 (f : Var) : Var :=
  (freshVar (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪
        ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f)
          (Class.cv (nb067_alpha_dummy_165 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_169 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_170 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_171 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_166 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_172 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_166 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_173 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cphi (Class.cv (nb067_alpha_dummy_170)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_174 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_175 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_169)
          (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
              (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_169)
          (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
              (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_176 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_171 f)
          (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_171 f)
          (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_177 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_170))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_178 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_170))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_179 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_172 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_180 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_172 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_181 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_177))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_182 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_179 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_183 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_184 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_185 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_186 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_187 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_188 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_189 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_184))
          (Class.cv (nb067_alpha_dummy_185)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_190 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_187 f))
          (Class.cv (nb067_alpha_dummy_188 f)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))).fv)
    0)

@[expose]
noncomputable def nb067_alpha_dummy_191 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_192 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_188 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_193 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_184)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_185)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_194 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_187 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_188 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_195 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_184))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_196 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_187 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_197 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_185))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_198 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_188 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_188 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_199 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_169)
          (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169)
          (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_200 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_171 f)
          (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f)
          (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_201 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_170))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_202 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_203 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_204 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_205 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_206 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_207 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_165 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_208 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_165 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_209 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cphi (Class.cv (nb067_alpha_dummy_206)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_210 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_211 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_205)
          (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
              (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_205)
          (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
              (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_212 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_207 f)
          (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_207 f)
          (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_213 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_206))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_214 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_206))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_215 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_208 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_216 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_208 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_217 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_213))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_218 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_215 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_219 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_220 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_221 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_222 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_223 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_224 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_225 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_220))
          (Class.cv (nb067_alpha_dummy_221)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_226 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_223 f))
          (Class.cv (nb067_alpha_dummy_224 f)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_223 f)) (Class.cv (nb067_alpha_dummy_224 f)))).fv)
    0)

@[expose]
noncomputable def nb067_alpha_dummy_227 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_228 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_224 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_229 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_220)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_221)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_230 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_223 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_224 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_231 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_220))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_232 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_223 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_233 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_221))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_234 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_224 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_224 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_235 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_205)
          (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205)
          (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_236 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_207 f)
          (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f)
          (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_237 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_206))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_238 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_239 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_240 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_241 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_242 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_243 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_087 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_244 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_087 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_245 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cphi (Class.cv (nb067_alpha_dummy_242)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_246 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_247 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_241)
          (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
              (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_241)
          (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
              (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_248 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_243 f)
          (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_243 f)
          (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_249 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_242))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_250 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_242))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_251 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_244 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_252 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_244 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_253 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_249))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_254 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_251 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_255 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_256 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_257 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_258 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_259 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_260 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_261 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_256))
          (Class.cv (nb067_alpha_dummy_257)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_262 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_259 f))
          (Class.cv (nb067_alpha_dummy_260 f)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_259 f)) (Class.cv (nb067_alpha_dummy_260 f)))).fv)
    0)

@[expose]
noncomputable def nb067_alpha_dummy_263 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_264 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_260 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_265 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_256)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_257)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_266 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_259 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_260 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_267 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_256))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_268 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_259 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_269 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_257))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_270 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_260 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_260 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_271 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_241)
          (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241)
          (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_272 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_243 f)
          (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f)
          (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_273 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_242))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_274 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_275 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_276 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_277 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_278 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_279 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_280 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_281 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_282 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_283 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_279 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_284 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_279 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_285 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cphi (Class.cv (nb067_alpha_dummy_282)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_286 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_287 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_281)
          (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
              (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_281)
          (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
              (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_288 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_283 f)
          (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_283 f)
          (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_289 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_282))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_290 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_282))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_291 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_284 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_292 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_284 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_293 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_289)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_289)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_289))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_294 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_291 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_291 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_291 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_295 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_296 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_297 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_298 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_299 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part003`. -/


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
noncomputable def nb067_alpha_dummy_300 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_301 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_296))
          (Class.cv (nb067_alpha_dummy_297)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_302 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_299 f))
          (Class.cv (nb067_alpha_dummy_300 f)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))).fv)
    0)

@[expose]
noncomputable def nb067_alpha_dummy_303 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_304 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_300 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_305 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_296)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_297)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_306 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_299 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_300 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_307 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_296))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_308 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_299 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_309 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_297))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_310 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_300 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_300 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_311 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_281)
          (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281)
          (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_312 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_283 f)
          (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f)
          (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_313 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_282))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_314 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_315 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_316 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_317 : Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000)))
          (Class.cv (nb067_alpha_dummy_001)))).fv ∪
      ((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000)))
          (Class.cv (nb067_alpha_dummy_001)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_318 (x : Var) (f : Var) : Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv ∪
      ((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_319 : Var :=
  (freshVar (((syn_crn (Class.cv (nb067_alpha_dummy_000)))).fv ∪
      ((Class.cv (nb067_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_320 (x : Var) (f : Var) : Var :=
  (freshVar (((syn_crn (Class.cv f))).fv ∪ ((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_321 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_322 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_323 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_324 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_325 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_326 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_327 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_323 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_328 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_323 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_329 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cphi (Class.cv (nb067_alpha_dummy_326)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_330 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_331 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_325)
          (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
              (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_325)
          (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
              (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_332 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_327 f)
          (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv ∪
      ((Class.cab (nb067_alpha_dummy_327 f)
          (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
              (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_333 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_326))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_334 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_326))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_335 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_328 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_336 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_328 f))).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_337 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_333))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_338 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb067_alpha_dummy_335 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_339 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_340 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_341 : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_342 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_343 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb067_alpha_dummy_344 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb067_alpha_dummy_345 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_340))
          (Class.cv (nb067_alpha_dummy_341)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_346 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_343 f))
          (Class.cv (nb067_alpha_dummy_344 f)))).fv ∪
      ((syn_cnin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))).fv)
    0)

@[expose]
noncomputable def nb067_alpha_dummy_347 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_348 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_344 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_349 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_340)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_341)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_350 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_343 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb067_alpha_dummy_344 f)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_351 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_340))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_352 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_343 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_353 : Var :=
  (freshVar
    (((Class.cv (nb067_alpha_dummy_341))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_354 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067_alpha_dummy_344 f))).fv ∪
      ((Class.cv (nb067_alpha_dummy_344 f))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_355 : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_325)
          (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325)
          (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_356 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067_alpha_dummy_327 f)
          (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f)
          (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
              (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_357 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_326))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_358 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_359 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv) 0)

@[expose]
noncomputable def nb067_alpha_dummy_360 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv ∪
      ((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv) 0)

theorem nb067_fresh_000 :
    (nb067_alpha_dummy_073) ∉
      (((Class.cab (nb067_alpha_dummy_007)
            (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007)
            (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_007)
            (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007)
            (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_001 :
    (nb067_alpha_dummy_013) ∉
      (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
              (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
              (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_013] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
              (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
              (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv)
      0

theorem nb067_fresh_002 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_074 x y f) ∉
      (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f)
              (Class.cv (nb067_alpha_dummy_004 x y f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_074] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f)
              (Class.cv (nb067_alpha_dummy_004 x y f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_003 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_014 x y f) ∉
      (((Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_014] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_009 x y f)
            (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv)
      0

theorem nb067_fresh_004 :
    (nb067_alpha_dummy_021) ∉
      (((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_021] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv)
      0

theorem nb067_fresh_005 :
    (nb067_alpha_dummy_045) ∉
      (((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_006 (x : Var) (y : Var) :
    (nb067_alpha_dummy_022 x y) ∉
      (((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_022] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv)
      0

theorem nb067_fresh_007 (x : Var) (y : Var) :
    (nb067_alpha_dummy_046 x y) ∉
      (((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_008 :
    (nb067_alpha_dummy_097) ∉
      (((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_097] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv)
      0

theorem nb067_fresh_009 :
    (nb067_alpha_dummy_121) ∉
      (((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_121] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_010 (f : Var) :
    (nb067_alpha_dummy_098 f) ∉
      (((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_098] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv)
      0

theorem nb067_fresh_011 (f : Var) :
    (nb067_alpha_dummy_122 f) ∉
      (((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_122] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_012 :
    (nb067_alpha_dummy_133) ∉
      (((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_133] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv)
      0

theorem nb067_fresh_013 :
    (nb067_alpha_dummy_157) ∉
      (((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_157] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_014 (f : Var) :
    (nb067_alpha_dummy_134 f) ∉
      (((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_134] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv)
      0

theorem nb067_fresh_015 (f : Var) :
    (nb067_alpha_dummy_158 f) ∉
      (((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_158] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_016 :
    (nb067_alpha_dummy_175) ∉
      (((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_175] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv)
      0

theorem nb067_fresh_017 :
    (nb067_alpha_dummy_199) ∉
      (((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_199] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_018 (f : Var) :
    (nb067_alpha_dummy_176 f) ∉
      (((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_176] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv)
      0

theorem nb067_fresh_019 (f : Var) :
    (nb067_alpha_dummy_200 f) ∉
      (((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_200] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_020 :
    (nb067_alpha_dummy_235) ∉
      (((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_235] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_021 :
    (nb067_alpha_dummy_211) ∉
      (((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_211] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv)
      0

theorem nb067_fresh_022 (f : Var) :
    (nb067_alpha_dummy_236 f) ∉
      (((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_236] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_023 (f : Var) :
    (nb067_alpha_dummy_212 f) ∉
      (((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_212] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv)
      0

theorem nb067_fresh_024 :
    (nb067_alpha_dummy_271) ∉
      (((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_271] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_025 :
    (nb067_alpha_dummy_247) ∉
      (((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_247] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv)
      0

theorem nb067_fresh_026 (f : Var) :
    (nb067_alpha_dummy_272 f) ∉
      (((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_272] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_027 (f : Var) :
    (nb067_alpha_dummy_248 f) ∉
      (((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_248] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv)
      0

theorem nb067_fresh_028 :
    (nb067_alpha_dummy_311) ∉
      (((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_311] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_029 :
    (nb067_alpha_dummy_287) ∉
      (((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_287] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv)
      0

theorem nb067_fresh_030 (f : Var) :
    (nb067_alpha_dummy_312 f) ∉
      (((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_312] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_031 (f : Var) :
    (nb067_alpha_dummy_288 f) ∉
      (((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_288] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv)
      0

theorem nb067_fresh_032 :
    (nb067_alpha_dummy_355) ∉
      (((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_355] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_033 :
    (nb067_alpha_dummy_331) ∉
      (((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_331] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv)
      0

theorem nb067_fresh_034 (f : Var) :
    (nb067_alpha_dummy_356 f) ∉
      (((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_356] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb067_fresh_035 (f : Var) :
    (nb067_alpha_dummy_332 f) ∉
      (((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_332] using
    freshVar_not_mem
      (((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv)
      0

theorem nb067_fresh_036 :
    (nb067_alpha_dummy_163) ∉ (((Class.cv (nb067_alpha_dummy_000))).fv) := by
  simpa only [nb067_alpha_dummy_163] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_000))).fv) 0

theorem nb067_fresh_037 :
    (nb067_alpha_dummy_164) ∉ (((Class.cv (nb067_alpha_dummy_000))).fv) := by
  simpa only [nb067_alpha_dummy_164] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_000))).fv) 1

theorem nb067_distinct_038 : (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_164) := by
  simpa only [nb067_alpha_dummy_163, nb067_alpha_dummy_164] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_039 :
    (nb067_alpha_dummy_083) ∉
      (((Class.cv (nb067_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_083] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv)
      0

theorem nb067_fresh_040 :
    (nb067_alpha_dummy_084) ∉
      (((Class.cv (nb067_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_084] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv)
      1

theorem nb067_fresh_041 :
    (nb067_alpha_dummy_085) ∉
      (((Class.cv (nb067_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_085] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv)
      2

theorem nb067_distinct_042 : (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_084) := by
  simpa only [nb067_alpha_dummy_083, nb067_alpha_dummy_084] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_043 : (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_085) := by
  simpa only [nb067_alpha_dummy_083, nb067_alpha_dummy_085] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_044 : (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_085) := by
  simpa only [nb067_alpha_dummy_084, nb067_alpha_dummy_085] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_045 :
    (nb067_alpha_dummy_321) ∉
      (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb067_alpha_dummy_321] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0

theorem nb067_fresh_046 :
    (nb067_alpha_dummy_322) ∉
      (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb067_alpha_dummy_322] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1

theorem nb067_distinct_047 : (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_322) := by
  simpa only [nb067_alpha_dummy_321, nb067_alpha_dummy_322] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_fresh_048 :
    (nb067_alpha_dummy_015) ∉
      (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) :=
  by
  simpa only [nb067_alpha_dummy_015] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv)
      0

theorem nb067_fresh_049 :
    (nb067_alpha_dummy_016) ∉
      (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) :=
  by
  simpa only [nb067_alpha_dummy_016] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv)
      1

theorem nb067_distinct_050 : (nb067_alpha_dummy_015) ≠ (nb067_alpha_dummy_016) := by
  simpa only [nb067_alpha_dummy_015, nb067_alpha_dummy_016] using
    (freshVar_injective
      (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_051 :
    (nb067_alpha_dummy_051) ∉ (((Class.cv (nb067_alpha_dummy_008))).fv) := by
  simpa only [nb067_alpha_dummy_051] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_008))).fv) 0

theorem nb067_fresh_052 :
    (nb067_alpha_dummy_052) ∉ (((Class.cv (nb067_alpha_dummy_008))).fv) := by
  simpa only [nb067_alpha_dummy_052] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_008))).fv) 1

theorem nb067_distinct_053 : (nb067_alpha_dummy_051) ≠ (nb067_alpha_dummy_052) := by
  simpa only [nb067_alpha_dummy_051, nb067_alpha_dummy_052] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_008))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_054 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_053 x y f) ∉ (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) := by
  simpa only [nb067_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) 0

theorem nb067_fresh_055 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_054 x y f) ∉ (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) := by
  simpa only [nb067_alpha_dummy_054] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) 1

theorem nb067_distinct_056 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_053 x y f) ≠ (nb067_alpha_dummy_054 x y f) := by
  simpa only [nb067_alpha_dummy_053, nb067_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_057 :
    (nb067_alpha_dummy_023) ∉ (((Class.cv (nb067_alpha_dummy_016))).fv) := by
  simpa only [nb067_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_016))).fv) 0

theorem nb067_fresh_058 :
    (nb067_alpha_dummy_024) ∉ (((Class.cv (nb067_alpha_dummy_016))).fv) := by
  simpa only [nb067_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_016))).fv) 1

theorem nb067_distinct_059 : (nb067_alpha_dummy_023) ≠ (nb067_alpha_dummy_024) := by
  simpa only [nb067_alpha_dummy_023, nb067_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_016))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_060 (x : Var) (y : Var) :
    (nb067_alpha_dummy_025 x y) ∉ (((Class.cv (nb067_alpha_dummy_018 x y))).fv) := by
  simpa only [nb067_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_018 x y))).fv) 0

theorem nb067_fresh_061 (x : Var) (y : Var) :
    (nb067_alpha_dummy_026 x y) ∉ (((Class.cv (nb067_alpha_dummy_018 x y))).fv) := by
  simpa only [nb067_alpha_dummy_026] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_018 x y))).fv) 1

theorem nb067_distinct_062 (x : Var) (y : Var) :
    (nb067_alpha_dummy_025 x y) ≠ (nb067_alpha_dummy_026 x y) := by
  simpa only [nb067_alpha_dummy_025, nb067_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_018 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_063 :
    (nb067_alpha_dummy_029) ∉
      (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_029] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_064 :
    (nb067_alpha_dummy_030) ∉
      (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_030] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_065 :
    (nb067_alpha_dummy_031) ∉
      (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_031] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_066 : (nb067_alpha_dummy_029) ≠ (nb067_alpha_dummy_030) := by
  simpa only [nb067_alpha_dummy_029, nb067_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_067 : (nb067_alpha_dummy_029) ≠ (nb067_alpha_dummy_031) := by
  simpa only [nb067_alpha_dummy_029, nb067_alpha_dummy_031] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_068 : (nb067_alpha_dummy_030) ≠ (nb067_alpha_dummy_031) := by
  simpa only [nb067_alpha_dummy_030, nb067_alpha_dummy_031] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_069 (x : Var) (y : Var) :
    (nb067_alpha_dummy_032 x y) ∉
      (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_032] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_070 (x : Var) (y : Var) :
    (nb067_alpha_dummy_033 x y) ∉
      (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_033] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part004`. -/


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

theorem nb067_fresh_071 (x : Var) (y : Var) :
    (nb067_alpha_dummy_034 x y) ∉
      (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_034] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_072 (x : Var) (y : Var) :
    (nb067_alpha_dummy_032 x y) ≠ (nb067_alpha_dummy_033 x y) := by
  simpa only [nb067_alpha_dummy_032, nb067_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_distinct_073 (x : Var) (y : Var) :
    (nb067_alpha_dummy_032 x y) ≠ (nb067_alpha_dummy_034 x y) := by
  simpa only [nb067_alpha_dummy_032, nb067_alpha_dummy_034] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb067_distinct_074 (x : Var) (y : Var) :
    (nb067_alpha_dummy_033 x y) ≠ (nb067_alpha_dummy_034 x y) := by
  simpa only [nb067_alpha_dummy_033, nb067_alpha_dummy_034] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb067_fresh_075 :
    (nb067_alpha_dummy_041) ∉
      (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_030))).fv) :=
  by
  simpa only [nb067_alpha_dummy_041] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_030))).fv)
      0

theorem nb067_fresh_076 :
    (nb067_alpha_dummy_037) ∉
      (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) :=
  by
  simpa only [nb067_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv)
      0

theorem nb067_fresh_077 :
    (nb067_alpha_dummy_043) ∉
      (((Class.cv (nb067_alpha_dummy_031))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) :=
  by
  simpa only [nb067_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_031))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv)
      0

theorem nb067_fresh_078 (x : Var) (y : Var) :
    (nb067_alpha_dummy_042 x y) ∉
      (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_033 x y))).fv) :=
  by
  simpa only [nb067_alpha_dummy_042] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_033 x y))).fv)
      0

theorem nb067_fresh_079 (x : Var) (y : Var) :
    (nb067_alpha_dummy_038 x y) ∉
      (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_034 x y))).fv) :=
  by
  simpa only [nb067_alpha_dummy_038] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_034 x y))).fv)
      0

theorem nb067_fresh_080 (x : Var) (y : Var) :
    (nb067_alpha_dummy_044 x y) ∉
      (((Class.cv (nb067_alpha_dummy_034 x y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_034 x y))).fv) :=
  by
  simpa only [nb067_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_034 x y))).fv ∪
        ((Class.cv (nb067_alpha_dummy_034 x y))).fv)
      0

theorem nb067_fresh_081 :
    (nb067_alpha_dummy_057) ∉
      (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_057] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_082 :
    (nb067_alpha_dummy_058) ∉
      (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_083 :
    (nb067_alpha_dummy_059) ∉
      (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_084 : (nb067_alpha_dummy_057) ≠ (nb067_alpha_dummy_058) := by
  simpa only [nb067_alpha_dummy_057, nb067_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_085 : (nb067_alpha_dummy_057) ≠ (nb067_alpha_dummy_059) := by
  simpa only [nb067_alpha_dummy_057, nb067_alpha_dummy_059] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_086 : (nb067_alpha_dummy_058) ≠ (nb067_alpha_dummy_059) := by
  simpa only [nb067_alpha_dummy_058, nb067_alpha_dummy_059] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_087 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_060 x y f) ∉
      (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_088 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_061 x y f) ∉
      (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_089 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_062 x y f) ∉
      (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_062] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_090 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_060 x y f) ≠ (nb067_alpha_dummy_061 x y f) := by
  simpa only [nb067_alpha_dummy_060, nb067_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_distinct_091 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_060 x y f) ≠ (nb067_alpha_dummy_062 x y f) := by
  simpa only [nb067_alpha_dummy_060, nb067_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb067_distinct_092 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_061 x y f) ≠ (nb067_alpha_dummy_062 x y f) := by
  simpa only [nb067_alpha_dummy_061, nb067_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb067_fresh_093 :
    (nb067_alpha_dummy_069) ∉
      (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_058))).fv) :=
  by
  simpa only [nb067_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_058))).fv)
      0

theorem nb067_fresh_094 :
    (nb067_alpha_dummy_065) ∉
      (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) :=
  by
  simpa only [nb067_alpha_dummy_065] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv)
      0

theorem nb067_fresh_095 :
    (nb067_alpha_dummy_071) ∉
      (((Class.cv (nb067_alpha_dummy_059))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) :=
  by
  simpa only [nb067_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_059))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv)
      0

theorem nb067_fresh_096 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_070 x y f) ∉
      (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_061 x y f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_061 x y f))).fv)
      0

theorem nb067_fresh_097 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_066 x y f) ∉
      (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_066] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_062 x y f))).fv)
      0

theorem nb067_fresh_098 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_072 x y f) ∉
      (((Class.cv (nb067_alpha_dummy_062 x y f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_062 x y f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_062 x y f))).fv)
      0

theorem nb067_fresh_099 :
    (nb067_alpha_dummy_091) ∉
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) :=
  by
  simpa only [nb067_alpha_dummy_091] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv)
      0

theorem nb067_fresh_100 :
    (nb067_alpha_dummy_092) ∉
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) :=
  by
  simpa only [nb067_alpha_dummy_092] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv)
      1

theorem nb067_distinct_101 : (nb067_alpha_dummy_091) ≠ (nb067_alpha_dummy_092) := by
  simpa only [nb067_alpha_dummy_091, nb067_alpha_dummy_092] using
    (freshVar_injective
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_102 :
    (nb067_alpha_dummy_127) ∉
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) :=
  by
  simpa only [nb067_alpha_dummy_127] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv)
      0

theorem nb067_fresh_103 :
    (nb067_alpha_dummy_128) ∉
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) :=
  by
  simpa only [nb067_alpha_dummy_128] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv)
      1

theorem nb067_distinct_104 : (nb067_alpha_dummy_127) ≠ (nb067_alpha_dummy_128) := by
  simpa only [nb067_alpha_dummy_127, nb067_alpha_dummy_128] using
    (freshVar_injective
      (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_105 :
    (nb067_alpha_dummy_241) ∉
      (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) :=
  by
  simpa only [nb067_alpha_dummy_241] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv)
      0

theorem nb067_fresh_106 :
    (nb067_alpha_dummy_242) ∉
      (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) :=
  by
  simpa only [nb067_alpha_dummy_242] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv)
      1

theorem nb067_distinct_107 : (nb067_alpha_dummy_241) ≠ (nb067_alpha_dummy_242) := by
  simpa only [nb067_alpha_dummy_241, nb067_alpha_dummy_242] using
    (freshVar_injective
      (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_108 (f : Var) :
    (nb067_alpha_dummy_093 f) ∉
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_093] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv)
      0

theorem nb067_fresh_109 (f : Var) :
    (nb067_alpha_dummy_094 f) ∉
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_094] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv)
      1

theorem nb067_distinct_110 (f : Var) :
    (nb067_alpha_dummy_093 f) ≠ (nb067_alpha_dummy_094 f) := by
  simpa only [nb067_alpha_dummy_093, nb067_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_087 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_111 (f : Var) :
    (nb067_alpha_dummy_129 f) ∉
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_129] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv)
      0

theorem nb067_fresh_112 (f : Var) :
    (nb067_alpha_dummy_130 f) ∉
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_130] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv)
      1

theorem nb067_distinct_113 (f : Var) :
    (nb067_alpha_dummy_129 f) ≠ (nb067_alpha_dummy_130 f) := by
  simpa only [nb067_alpha_dummy_129, nb067_alpha_dummy_130] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_088 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_114 (f : Var) :
    (nb067_alpha_dummy_243 f) ∉
      (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_243] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv)
      0

theorem nb067_fresh_115 (f : Var) :
    (nb067_alpha_dummy_244 f) ∉
      (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_244] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv)
      1

theorem nb067_distinct_116 (f : Var) :
    (nb067_alpha_dummy_243 f) ≠ (nb067_alpha_dummy_244 f) := by
  simpa only [nb067_alpha_dummy_243, nb067_alpha_dummy_244] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_087 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_117 :
    (nb067_alpha_dummy_099) ∉ (((Class.cv (nb067_alpha_dummy_092))).fv) := by
  simpa only [nb067_alpha_dummy_099] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_092))).fv) 0

theorem nb067_fresh_118 :
    (nb067_alpha_dummy_100) ∉ (((Class.cv (nb067_alpha_dummy_092))).fv) := by
  simpa only [nb067_alpha_dummy_100] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_092))).fv) 1

theorem nb067_distinct_119 : (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_100) := by
  simpa only [nb067_alpha_dummy_099, nb067_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_092))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_120 (f : Var) :
    (nb067_alpha_dummy_101 f) ∉ (((Class.cv (nb067_alpha_dummy_094 f))).fv) := by
  simpa only [nb067_alpha_dummy_101] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_094 f))).fv) 0

theorem nb067_fresh_121 (f : Var) :
    (nb067_alpha_dummy_102 f) ∉ (((Class.cv (nb067_alpha_dummy_094 f))).fv) := by
  simpa only [nb067_alpha_dummy_102] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_094 f))).fv) 1

theorem nb067_distinct_122 (f : Var) :
    (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_102 f) := by
  simpa only [nb067_alpha_dummy_101, nb067_alpha_dummy_102] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_094 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_123 :
    (nb067_alpha_dummy_105) ∉
      (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_105] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_124 :
    (nb067_alpha_dummy_106) ∉
      (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_106] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_125 :
    (nb067_alpha_dummy_107) ∉
      (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_107] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_126 : (nb067_alpha_dummy_105) ≠ (nb067_alpha_dummy_106) := by
  simpa only [nb067_alpha_dummy_105, nb067_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_127 : (nb067_alpha_dummy_105) ≠ (nb067_alpha_dummy_107) := by
  simpa only [nb067_alpha_dummy_105, nb067_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_128 : (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_107) := by
  simpa only [nb067_alpha_dummy_106, nb067_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_129 (f : Var) :
    (nb067_alpha_dummy_108 f) ∉
      (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_108] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_130 (f : Var) :
    (nb067_alpha_dummy_109 f) ∉
      (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_109] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_131 (f : Var) :
    (nb067_alpha_dummy_110 f) ∉
      (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_110] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_132 (f : Var) :
    (nb067_alpha_dummy_108 f) ≠ (nb067_alpha_dummy_109 f) := by
  simpa only [nb067_alpha_dummy_108, nb067_alpha_dummy_109] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_133 (f : Var) :
    (nb067_alpha_dummy_108 f) ≠ (nb067_alpha_dummy_110 f) := by
  simpa only [nb067_alpha_dummy_108, nb067_alpha_dummy_110] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_134 (f : Var) :
    (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_110 f) := by
  simpa only [nb067_alpha_dummy_109, nb067_alpha_dummy_110] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_135 :
    (nb067_alpha_dummy_117) ∉
      (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_106))).fv) :=
  by
  simpa only [nb067_alpha_dummy_117] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_106))).fv)
      0

theorem nb067_fresh_136 :
    (nb067_alpha_dummy_113) ∉
      (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) :=
  by
  simpa only [nb067_alpha_dummy_113] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv)
      0

theorem nb067_fresh_137 :
    (nb067_alpha_dummy_119) ∉
      (((Class.cv (nb067_alpha_dummy_107))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) :=
  by
  simpa only [nb067_alpha_dummy_119] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_107))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv)
      0

theorem nb067_fresh_138 (f : Var) :
    (nb067_alpha_dummy_118 f) ∉
      (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_109 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_118] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_109 f))).fv)
      0

theorem nb067_fresh_139 (f : Var) :
    (nb067_alpha_dummy_114 f) ∉
      (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_114] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv)
      0

theorem nb067_fresh_140 (f : Var) :
    (nb067_alpha_dummy_120 f) ∉
      (((Class.cv (nb067_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_120] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv)
      0

theorem nb067_fresh_141 :
    (nb067_alpha_dummy_135) ∉ (((Class.cv (nb067_alpha_dummy_128))).fv) := by
  simpa only [nb067_alpha_dummy_135] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_128))).fv) 0

theorem nb067_fresh_142 :
    (nb067_alpha_dummy_136) ∉ (((Class.cv (nb067_alpha_dummy_128))).fv) := by
  simpa only [nb067_alpha_dummy_136] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_128))).fv) 1

theorem nb067_distinct_143 : (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_136) := by
  simpa only [nb067_alpha_dummy_135, nb067_alpha_dummy_136] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_128))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_144 (f : Var) :
    (nb067_alpha_dummy_137 f) ∉ (((Class.cv (nb067_alpha_dummy_130 f))).fv) := by
  simpa only [nb067_alpha_dummy_137] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_130 f))).fv) 0

theorem nb067_fresh_145 (f : Var) :
    (nb067_alpha_dummy_138 f) ∉ (((Class.cv (nb067_alpha_dummy_130 f))).fv) := by
  simpa only [nb067_alpha_dummy_138] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_130 f))).fv) 1

theorem nb067_distinct_146 (f : Var) :
    (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_138 f) := by
  simpa only [nb067_alpha_dummy_137, nb067_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_130 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_147 :
    (nb067_alpha_dummy_141) ∉
      (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_141] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_148 :
    (nb067_alpha_dummy_142) ∉
      (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_142] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_149 :
    (nb067_alpha_dummy_143) ∉
      (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_143] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_150 : (nb067_alpha_dummy_141) ≠ (nb067_alpha_dummy_142) := by
  simpa only [nb067_alpha_dummy_141, nb067_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_151 : (nb067_alpha_dummy_141) ≠ (nb067_alpha_dummy_143) := by
  simpa only [nb067_alpha_dummy_141, nb067_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_152 : (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_143) := by
  simpa only [nb067_alpha_dummy_142, nb067_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_153 (f : Var) :
    (nb067_alpha_dummy_144 f) ∉
      (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_144] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_154 (f : Var) :
    (nb067_alpha_dummy_145 f) ∉
      (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_145] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_155 (f : Var) :
    (nb067_alpha_dummy_146 f) ∉
      (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_146] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_156 (f : Var) :
    (nb067_alpha_dummy_144 f) ≠ (nb067_alpha_dummy_145 f) := by
  simpa only [nb067_alpha_dummy_144, nb067_alpha_dummy_145] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_157 (f : Var) :
    (nb067_alpha_dummy_144 f) ≠ (nb067_alpha_dummy_146 f) := by
  simpa only [nb067_alpha_dummy_144, nb067_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_158 (f : Var) :
    (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_146 f) := by
  simpa only [nb067_alpha_dummy_145, nb067_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_159 :
    (nb067_alpha_dummy_153) ∉
      (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_142))).fv) :=
  by
  simpa only [nb067_alpha_dummy_153] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_142))).fv)
      0

theorem nb067_fresh_160 :
    (nb067_alpha_dummy_149) ∉
      (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) :=
  by
  simpa only [nb067_alpha_dummy_149] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv)
      0

theorem nb067_fresh_161 :
    (nb067_alpha_dummy_155) ∉
      (((Class.cv (nb067_alpha_dummy_143))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) :=
  by
  simpa only [nb067_alpha_dummy_155] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_143))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv)
      0

theorem nb067_fresh_162 (f : Var) :
    (nb067_alpha_dummy_154 f) ∉
      (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_145 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_154] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_145 f))).fv)
      0

theorem nb067_fresh_163 (f : Var) :
    (nb067_alpha_dummy_150 f) ∉
      (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_150] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv)
      0

theorem nb067_fresh_164 (f : Var) :
    (nb067_alpha_dummy_156 f) ∉
      (((Class.cv (nb067_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_156] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv)
      0

theorem nb067_fresh_165 :
    (nb067_alpha_dummy_169) ∉
      (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) :=
  by
  simpa only [nb067_alpha_dummy_169] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv)
      0

theorem nb067_fresh_166 :
    (nb067_alpha_dummy_170) ∉
      (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) :=
  by
  simpa only [nb067_alpha_dummy_170] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv)
      1

theorem nb067_distinct_167 : (nb067_alpha_dummy_169) ≠ (nb067_alpha_dummy_170) := by
  simpa only [nb067_alpha_dummy_169, nb067_alpha_dummy_170] using
    (freshVar_injective
      (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_168 :
    (nb067_alpha_dummy_205) ∉
      (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) :=
  by
  simpa only [nb067_alpha_dummy_205] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv)
      0

theorem nb067_fresh_169 :
    (nb067_alpha_dummy_206) ∉
      (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) :=
  by
  simpa only [nb067_alpha_dummy_206] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv)
      1

theorem nb067_distinct_170 : (nb067_alpha_dummy_205) ≠ (nb067_alpha_dummy_206) := by
  simpa only [nb067_alpha_dummy_205, nb067_alpha_dummy_206] using
    (freshVar_injective
      (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_171 (f : Var) :
    (nb067_alpha_dummy_171 f) ∉
      (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_171] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv)
      0

theorem nb067_fresh_172 (f : Var) :
    (nb067_alpha_dummy_172 f) ∉
      (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_172] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv)
      1

theorem nb067_distinct_173 (f : Var) :
    (nb067_alpha_dummy_171 f) ≠ (nb067_alpha_dummy_172 f) := by
  simpa only [nb067_alpha_dummy_171, nb067_alpha_dummy_172] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_166 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_174 (f : Var) :
    (nb067_alpha_dummy_207 f) ∉
      (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_207] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv)
      0

theorem nb067_fresh_175 (f : Var) :
    (nb067_alpha_dummy_208 f) ∉
      (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_208] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv)
      1

theorem nb067_distinct_176 (f : Var) :
    (nb067_alpha_dummy_207 f) ≠ (nb067_alpha_dummy_208 f) := by
  simpa only [nb067_alpha_dummy_207, nb067_alpha_dummy_208] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_165 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_177 :
    (nb067_alpha_dummy_177) ∉ (((Class.cv (nb067_alpha_dummy_170))).fv) := by
  simpa only [nb067_alpha_dummy_177] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_170))).fv) 0

theorem nb067_fresh_178 :
    (nb067_alpha_dummy_178) ∉ (((Class.cv (nb067_alpha_dummy_170))).fv) := by
  simpa only [nb067_alpha_dummy_178] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_170))).fv) 1

theorem nb067_distinct_179 : (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_178) := by
  simpa only [nb067_alpha_dummy_177, nb067_alpha_dummy_178] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_180 (f : Var) :
    (nb067_alpha_dummy_179 f) ∉ (((Class.cv (nb067_alpha_dummy_172 f))).fv) := by
  simpa only [nb067_alpha_dummy_179] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_172 f))).fv) 0

theorem nb067_fresh_181 (f : Var) :
    (nb067_alpha_dummy_180 f) ∉ (((Class.cv (nb067_alpha_dummy_172 f))).fv) := by
  simpa only [nb067_alpha_dummy_180] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_172 f))).fv) 1

theorem nb067_distinct_182 (f : Var) :
    (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_180 f) := by
  simpa only [nb067_alpha_dummy_179, nb067_alpha_dummy_180] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_183 :
    (nb067_alpha_dummy_183) ∉
      (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_183] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_184 :
    (nb067_alpha_dummy_184) ∉
      (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_184] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_185 :
    (nb067_alpha_dummy_185) ∉
      (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_185] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_186 : (nb067_alpha_dummy_183) ≠ (nb067_alpha_dummy_184) := by
  simpa only [nb067_alpha_dummy_183, nb067_alpha_dummy_184] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_187 : (nb067_alpha_dummy_183) ≠ (nb067_alpha_dummy_185) := by
  simpa only [nb067_alpha_dummy_183, nb067_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_188 : (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_185) := by
  simpa only [nb067_alpha_dummy_184, nb067_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_189 (f : Var) :
    (nb067_alpha_dummy_186 f) ∉
      (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_186] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_190 (f : Var) :
    (nb067_alpha_dummy_187 f) ∉
      (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_187] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_191 (f : Var) :
    (nb067_alpha_dummy_188 f) ∉
      (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_188] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_192 (f : Var) :
    (nb067_alpha_dummy_186 f) ≠ (nb067_alpha_dummy_187 f) := by
  simpa only [nb067_alpha_dummy_186, nb067_alpha_dummy_187] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_193 (f : Var) :
    (nb067_alpha_dummy_186 f) ≠ (nb067_alpha_dummy_188 f) := by
  simpa only [nb067_alpha_dummy_186, nb067_alpha_dummy_188] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_194 (f : Var) :
    (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_188 f) := by
  simpa only [nb067_alpha_dummy_187, nb067_alpha_dummy_188] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_195 :
    (nb067_alpha_dummy_195) ∉
      (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_184))).fv) :=
  by
  simpa only [nb067_alpha_dummy_195] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_184))).fv)
      0

theorem nb067_fresh_196 :
    (nb067_alpha_dummy_191) ∉
      (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) :=
  by
  simpa only [nb067_alpha_dummy_191] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv)
      0

theorem nb067_fresh_197 :
    (nb067_alpha_dummy_197) ∉
      (((Class.cv (nb067_alpha_dummy_185))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) :=
  by
  simpa only [nb067_alpha_dummy_197] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_185))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv)
      0

theorem nb067_fresh_198 (f : Var) :
    (nb067_alpha_dummy_196 f) ∉
      (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_187 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_196] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_187 f))).fv)
      0

theorem nb067_fresh_199 (f : Var) :
    (nb067_alpha_dummy_192 f) ∉
      (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_192] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv)
      0

theorem nb067_fresh_200 (f : Var) :
    (nb067_alpha_dummy_198 f) ∉
      (((Class.cv (nb067_alpha_dummy_188 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_198] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_188 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv)
      0

theorem nb067_fresh_201 :
    (nb067_alpha_dummy_213) ∉ (((Class.cv (nb067_alpha_dummy_206))).fv) := by
  simpa only [nb067_alpha_dummy_213] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_206))).fv) 0

theorem nb067_fresh_202 :
    (nb067_alpha_dummy_214) ∉ (((Class.cv (nb067_alpha_dummy_206))).fv) := by
  simpa only [nb067_alpha_dummy_214] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_206))).fv) 1

theorem nb067_distinct_203 : (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_214) := by
  simpa only [nb067_alpha_dummy_213, nb067_alpha_dummy_214] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_206))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_204 (f : Var) :
    (nb067_alpha_dummy_215 f) ∉ (((Class.cv (nb067_alpha_dummy_208 f))).fv) := by
  simpa only [nb067_alpha_dummy_215] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_208 f))).fv) 0

theorem nb067_fresh_205 (f : Var) :
    (nb067_alpha_dummy_216 f) ∉ (((Class.cv (nb067_alpha_dummy_208 f))).fv) := by
  simpa only [nb067_alpha_dummy_216] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_208 f))).fv) 1

theorem nb067_distinct_206 (f : Var) :
    (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_216 f) := by
  simpa only [nb067_alpha_dummy_215, nb067_alpha_dummy_216] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_208 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_207 :
    (nb067_alpha_dummy_219) ∉
      (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_219] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_208 :
    (nb067_alpha_dummy_220) ∉
      (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_220] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_209 :
    (nb067_alpha_dummy_221) ∉
      (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_221] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_210 : (nb067_alpha_dummy_219) ≠ (nb067_alpha_dummy_220) := by
  simpa only [nb067_alpha_dummy_219, nb067_alpha_dummy_220] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_211 : (nb067_alpha_dummy_219) ≠ (nb067_alpha_dummy_221) := by
  simpa only [nb067_alpha_dummy_219, nb067_alpha_dummy_221] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_212 : (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_221) := by
  simpa only [nb067_alpha_dummy_220, nb067_alpha_dummy_221] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_213 (f : Var) :
    (nb067_alpha_dummy_222 f) ∉
      (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_222] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_214 (f : Var) :
    (nb067_alpha_dummy_223 f) ∉
      (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_223] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_215 (f : Var) :
    (nb067_alpha_dummy_224 f) ∉
      (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_224] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_216 (f : Var) :
    (nb067_alpha_dummy_222 f) ≠ (nb067_alpha_dummy_223 f) := by
  simpa only [nb067_alpha_dummy_222, nb067_alpha_dummy_223] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_217 (f : Var) :
    (nb067_alpha_dummy_222 f) ≠ (nb067_alpha_dummy_224 f) := by
  simpa only [nb067_alpha_dummy_222, nb067_alpha_dummy_224] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_218 (f : Var) :
    (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_224 f) := by
  simpa only [nb067_alpha_dummy_223, nb067_alpha_dummy_224] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_219 :
    (nb067_alpha_dummy_231) ∉
      (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_220))).fv) :=
  by
  simpa only [nb067_alpha_dummy_231] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_220))).fv)
      0

theorem nb067_fresh_220 :
    (nb067_alpha_dummy_227) ∉
      (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) :=
  by
  simpa only [nb067_alpha_dummy_227] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part005`. -/


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

theorem nb067_fresh_221 :
    (nb067_alpha_dummy_233) ∉
      (((Class.cv (nb067_alpha_dummy_221))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) :=
  by
  simpa only [nb067_alpha_dummy_233] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_221))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv)
      0

theorem nb067_fresh_222 (f : Var) :
    (nb067_alpha_dummy_232 f) ∉
      (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_223 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_232] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_223 f))).fv)
      0

theorem nb067_fresh_223 (f : Var) :
    (nb067_alpha_dummy_228 f) ∉
      (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_228] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv)
      0

theorem nb067_fresh_224 (f : Var) :
    (nb067_alpha_dummy_234 f) ∉
      (((Class.cv (nb067_alpha_dummy_224 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_234] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_224 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv)
      0

theorem nb067_fresh_225 :
    (nb067_alpha_dummy_249) ∉ (((Class.cv (nb067_alpha_dummy_242))).fv) := by
  simpa only [nb067_alpha_dummy_249] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_242))).fv) 0

theorem nb067_fresh_226 :
    (nb067_alpha_dummy_250) ∉ (((Class.cv (nb067_alpha_dummy_242))).fv) := by
  simpa only [nb067_alpha_dummy_250] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_242))).fv) 1

theorem nb067_distinct_227 : (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_250) := by
  simpa only [nb067_alpha_dummy_249, nb067_alpha_dummy_250] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_242))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_228 (f : Var) :
    (nb067_alpha_dummy_251 f) ∉ (((Class.cv (nb067_alpha_dummy_244 f))).fv) := by
  simpa only [nb067_alpha_dummy_251] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_244 f))).fv) 0

theorem nb067_fresh_229 (f : Var) :
    (nb067_alpha_dummy_252 f) ∉ (((Class.cv (nb067_alpha_dummy_244 f))).fv) := by
  simpa only [nb067_alpha_dummy_252] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_244 f))).fv) 1

theorem nb067_distinct_230 (f : Var) :
    (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_252 f) := by
  simpa only [nb067_alpha_dummy_251, nb067_alpha_dummy_252] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_244 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_231 :
    (nb067_alpha_dummy_255) ∉
      (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_255] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_232 :
    (nb067_alpha_dummy_256) ∉
      (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_256] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_233 :
    (nb067_alpha_dummy_257) ∉
      (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_257] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_234 : (nb067_alpha_dummy_255) ≠ (nb067_alpha_dummy_256) := by
  simpa only [nb067_alpha_dummy_255, nb067_alpha_dummy_256] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_235 : (nb067_alpha_dummy_255) ≠ (nb067_alpha_dummy_257) := by
  simpa only [nb067_alpha_dummy_255, nb067_alpha_dummy_257] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_236 : (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_257) := by
  simpa only [nb067_alpha_dummy_256, nb067_alpha_dummy_257] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_237 (f : Var) :
    (nb067_alpha_dummy_258 f) ∉
      (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_258] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_238 (f : Var) :
    (nb067_alpha_dummy_259 f) ∉
      (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_259] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_239 (f : Var) :
    (nb067_alpha_dummy_260 f) ∉
      (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_260] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_240 (f : Var) :
    (nb067_alpha_dummy_258 f) ≠ (nb067_alpha_dummy_259 f) := by
  simpa only [nb067_alpha_dummy_258, nb067_alpha_dummy_259] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_241 (f : Var) :
    (nb067_alpha_dummy_258 f) ≠ (nb067_alpha_dummy_260 f) := by
  simpa only [nb067_alpha_dummy_258, nb067_alpha_dummy_260] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_242 (f : Var) :
    (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_260 f) := by
  simpa only [nb067_alpha_dummy_259, nb067_alpha_dummy_260] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_243 :
    (nb067_alpha_dummy_267) ∉
      (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_256))).fv) :=
  by
  simpa only [nb067_alpha_dummy_267] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_256))).fv)
      0

theorem nb067_fresh_244 :
    (nb067_alpha_dummy_263) ∉
      (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) :=
  by
  simpa only [nb067_alpha_dummy_263] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv)
      0

theorem nb067_fresh_245 :
    (nb067_alpha_dummy_269) ∉
      (((Class.cv (nb067_alpha_dummy_257))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) :=
  by
  simpa only [nb067_alpha_dummy_269] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_257))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv)
      0

theorem nb067_fresh_246 (f : Var) :
    (nb067_alpha_dummy_268 f) ∉
      (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_259 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_268] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_259 f))).fv)
      0

theorem nb067_fresh_247 (f : Var) :
    (nb067_alpha_dummy_264 f) ∉
      (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_264] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv)
      0

theorem nb067_fresh_248 (f : Var) :
    (nb067_alpha_dummy_270 f) ∉
      (((Class.cv (nb067_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_270] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv)
      0

theorem nb067_fresh_249 :
    (nb067_alpha_dummy_281) ∉
      (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) :=
  by
  simpa only [nb067_alpha_dummy_281] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv)
      0

theorem nb067_fresh_250 :
    (nb067_alpha_dummy_282) ∉
      (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) :=
  by
  simpa only [nb067_alpha_dummy_282] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv)
      1

theorem nb067_distinct_251 : (nb067_alpha_dummy_281) ≠ (nb067_alpha_dummy_282) := by
  simpa only [nb067_alpha_dummy_281, nb067_alpha_dummy_282] using
    (freshVar_injective
      (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_252 (f : Var) :
    (nb067_alpha_dummy_283 f) ∉
      (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_283] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv)
      0

theorem nb067_fresh_253 (f : Var) :
    (nb067_alpha_dummy_284 f) ∉
      (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_284] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv)
      1

theorem nb067_distinct_254 (f : Var) :
    (nb067_alpha_dummy_283 f) ≠ (nb067_alpha_dummy_284 f) := by
  simpa only [nb067_alpha_dummy_283, nb067_alpha_dummy_284] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_279 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_255 :
    (nb067_alpha_dummy_289) ∉ (((Class.cv (nb067_alpha_dummy_282))).fv) := by
  simpa only [nb067_alpha_dummy_289] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_282))).fv) 0

theorem nb067_fresh_256 :
    (nb067_alpha_dummy_290) ∉ (((Class.cv (nb067_alpha_dummy_282))).fv) := by
  simpa only [nb067_alpha_dummy_290] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_282))).fv) 1

theorem nb067_distinct_257 : (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_290) := by
  simpa only [nb067_alpha_dummy_289, nb067_alpha_dummy_290] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_282))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_258 (f : Var) :
    (nb067_alpha_dummy_291 f) ∉ (((Class.cv (nb067_alpha_dummy_284 f))).fv) := by
  simpa only [nb067_alpha_dummy_291] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_284 f))).fv) 0

theorem nb067_fresh_259 (f : Var) :
    (nb067_alpha_dummy_292 f) ∉ (((Class.cv (nb067_alpha_dummy_284 f))).fv) := by
  simpa only [nb067_alpha_dummy_292] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_284 f))).fv) 1

theorem nb067_distinct_260 (f : Var) :
    (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_292 f) := by
  simpa only [nb067_alpha_dummy_291, nb067_alpha_dummy_292] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_284 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_261 :
    (nb067_alpha_dummy_295) ∉
      (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_295] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_262 :
    (nb067_alpha_dummy_296) ∉
      (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_296] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_263 :
    (nb067_alpha_dummy_297) ∉
      (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_297] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_264 : (nb067_alpha_dummy_295) ≠ (nb067_alpha_dummy_296) := by
  simpa only [nb067_alpha_dummy_295, nb067_alpha_dummy_296] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_265 : (nb067_alpha_dummy_295) ≠ (nb067_alpha_dummy_297) := by
  simpa only [nb067_alpha_dummy_295, nb067_alpha_dummy_297] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_266 : (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_297) := by
  simpa only [nb067_alpha_dummy_296, nb067_alpha_dummy_297] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_267 (f : Var) :
    (nb067_alpha_dummy_298 f) ∉
      (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_298] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_268 (f : Var) :
    (nb067_alpha_dummy_299 f) ∉
      (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_299] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_269 (f : Var) :
    (nb067_alpha_dummy_300 f) ∉
      (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_300] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_270 (f : Var) :
    (nb067_alpha_dummy_298 f) ≠ (nb067_alpha_dummy_299 f) := by
  simpa only [nb067_alpha_dummy_298, nb067_alpha_dummy_299] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_271 (f : Var) :
    (nb067_alpha_dummy_298 f) ≠ (nb067_alpha_dummy_300 f) := by
  simpa only [nb067_alpha_dummy_298, nb067_alpha_dummy_300] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_272 (f : Var) :
    (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_300 f) := by
  simpa only [nb067_alpha_dummy_299, nb067_alpha_dummy_300] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_273 :
    (nb067_alpha_dummy_307) ∉
      (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_296))).fv) :=
  by
  simpa only [nb067_alpha_dummy_307] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_296))).fv)
      0

theorem nb067_fresh_274 :
    (nb067_alpha_dummy_303) ∉
      (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) :=
  by
  simpa only [nb067_alpha_dummy_303] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv)
      0

theorem nb067_fresh_275 :
    (nb067_alpha_dummy_309) ∉
      (((Class.cv (nb067_alpha_dummy_297))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) :=
  by
  simpa only [nb067_alpha_dummy_309] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_297))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv)
      0

theorem nb067_fresh_276 (f : Var) :
    (nb067_alpha_dummy_308 f) ∉
      (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_299 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_308] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_299 f))).fv)
      0

theorem nb067_fresh_277 (f : Var) :
    (nb067_alpha_dummy_304 f) ∉
      (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_304] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv)
      0

theorem nb067_fresh_278 (f : Var) :
    (nb067_alpha_dummy_310 f) ∉
      (((Class.cv (nb067_alpha_dummy_300 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_310] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_300 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv)
      0

theorem nb067_fresh_279 :
    (nb067_alpha_dummy_325) ∉
      (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) :=
  by
  simpa only [nb067_alpha_dummy_325] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv)
      0

theorem nb067_fresh_280 :
    (nb067_alpha_dummy_326) ∉
      (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) :=
  by
  simpa only [nb067_alpha_dummy_326] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv)
      1

theorem nb067_distinct_281 : (nb067_alpha_dummy_325) ≠ (nb067_alpha_dummy_326) := by
  simpa only [nb067_alpha_dummy_325, nb067_alpha_dummy_326] using
    (freshVar_injective
      (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_282 (f : Var) :
    (nb067_alpha_dummy_327 f) ∉
      (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_327] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv)
      0

theorem nb067_fresh_283 (f : Var) :
    (nb067_alpha_dummy_328 f) ∉
      (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_328] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv)
      1

theorem nb067_distinct_284 (f : Var) :
    (nb067_alpha_dummy_327 f) ≠ (nb067_alpha_dummy_328 f) := by
  simpa only [nb067_alpha_dummy_327, nb067_alpha_dummy_328] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_323 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_285 :
    (nb067_alpha_dummy_333) ∉ (((Class.cv (nb067_alpha_dummy_326))).fv) := by
  simpa only [nb067_alpha_dummy_333] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_326))).fv) 0

theorem nb067_fresh_286 :
    (nb067_alpha_dummy_334) ∉ (((Class.cv (nb067_alpha_dummy_326))).fv) := by
  simpa only [nb067_alpha_dummy_334] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_326))).fv) 1

theorem nb067_distinct_287 : (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_334) := by
  simpa only [nb067_alpha_dummy_333, nb067_alpha_dummy_334] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_326))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_288 (f : Var) :
    (nb067_alpha_dummy_335 f) ∉ (((Class.cv (nb067_alpha_dummy_328 f))).fv) := by
  simpa only [nb067_alpha_dummy_335] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_328 f))).fv) 0

theorem nb067_fresh_289 (f : Var) :
    (nb067_alpha_dummy_336 f) ∉ (((Class.cv (nb067_alpha_dummy_328 f))).fv) := by
  simpa only [nb067_alpha_dummy_336] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_328 f))).fv) 1

theorem nb067_distinct_290 (f : Var) :
    (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_336 f) := by
  simpa only [nb067_alpha_dummy_335, nb067_alpha_dummy_336] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_328 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_291 :
    (nb067_alpha_dummy_339) ∉
      (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_339] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_292 :
    (nb067_alpha_dummy_340) ∉
      (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_340] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_293 :
    (nb067_alpha_dummy_341) ∉
      (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_341] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_294 : (nb067_alpha_dummy_339) ≠ (nb067_alpha_dummy_340) := by
  simpa only [nb067_alpha_dummy_339, nb067_alpha_dummy_340] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_295 : (nb067_alpha_dummy_339) ≠ (nb067_alpha_dummy_341) := by
  simpa only [nb067_alpha_dummy_339, nb067_alpha_dummy_341] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_296 : (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_341) := by
  simpa only [nb067_alpha_dummy_340, nb067_alpha_dummy_341] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_297 (f : Var) :
    (nb067_alpha_dummy_342 f) ∉
      (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_342] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_298 (f : Var) :
    (nb067_alpha_dummy_343 f) ∉
      (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_343] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_299 (f : Var) :
    (nb067_alpha_dummy_344 f) ∉
      (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb067_alpha_dummy_344] using
    freshVar_not_mem (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_300 (f : Var) :
    (nb067_alpha_dummy_342 f) ≠ (nb067_alpha_dummy_343 f) := by
  simpa only [nb067_alpha_dummy_342, nb067_alpha_dummy_343] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_301 (f : Var) :
    (nb067_alpha_dummy_342 f) ≠ (nb067_alpha_dummy_344 f) := by
  simpa only [nb067_alpha_dummy_342, nb067_alpha_dummy_344] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_302 (f : Var) :
    (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_344 f) := by
  simpa only [nb067_alpha_dummy_343, nb067_alpha_dummy_344] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_303 :
    (nb067_alpha_dummy_351) ∉
      (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_340))).fv) :=
  by
  simpa only [nb067_alpha_dummy_351] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_340))).fv)
      0

theorem nb067_fresh_304 :
    (nb067_alpha_dummy_347) ∉
      (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) :=
  by
  simpa only [nb067_alpha_dummy_347] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv)
      0

theorem nb067_fresh_305 :
    (nb067_alpha_dummy_353) ∉
      (((Class.cv (nb067_alpha_dummy_341))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) :=
  by
  simpa only [nb067_alpha_dummy_353] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_341))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv)
      0

theorem nb067_fresh_306 (f : Var) :
    (nb067_alpha_dummy_352 f) ∉
      (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_343 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_352] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_343 f))).fv)
      0

theorem nb067_fresh_307 (f : Var) :
    (nb067_alpha_dummy_348 f) ∉
      (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_348] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv)
      0

theorem nb067_fresh_308 (f : Var) :
    (nb067_alpha_dummy_354 f) ∉
      (((Class.cv (nb067_alpha_dummy_344 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_354] using
    freshVar_not_mem
      (((Class.cv (nb067_alpha_dummy_344 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv)
      0

theorem nb067_fresh_309 (f : Var) : (nb067_alpha_dummy_165 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb067_alpha_dummy_165] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb067_fresh_310 (f : Var) : (nb067_alpha_dummy_166 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb067_alpha_dummy_166] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb067_distinct_311 (f : Var) :
    (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_166 f) := by
  simpa only [nb067_alpha_dummy_165, nb067_alpha_dummy_166] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_312 (f : Var) :
    (nb067_alpha_dummy_086 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb067_alpha_dummy_086] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0

theorem nb067_fresh_313 (f : Var) :
    (nb067_alpha_dummy_087 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb067_alpha_dummy_087] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1

theorem nb067_fresh_314 (f : Var) :
    (nb067_alpha_dummy_088 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb067_alpha_dummy_088] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2

theorem nb067_distinct_315 (f : Var) :
    (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_087 f) := by
  simpa only [nb067_alpha_dummy_086, nb067_alpha_dummy_087] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb067_distinct_316 (f : Var) :
    (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_088 f) := by
  simpa only [nb067_alpha_dummy_086, nb067_alpha_dummy_088] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb067_distinct_317 (f : Var) :
    (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_088 f) := by
  simpa only [nb067_alpha_dummy_087, nb067_alpha_dummy_088] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb067_fresh_318 (f : Var) :
    (nb067_alpha_dummy_323 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_323] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0

theorem nb067_fresh_319 (f : Var) :
    (nb067_alpha_dummy_324 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_324] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1

theorem nb067_distinct_320 (f : Var) :
    (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_324 f) := by
  simpa only [nb067_alpha_dummy_323, nb067_alpha_dummy_324] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_321 (x : Var) (y : Var) :
    (nb067_alpha_dummy_017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb067_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb067_fresh_322 (x : Var) (y : Var) :
    (nb067_alpha_dummy_018 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb067_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb067_distinct_323 (x : Var) (y : Var) :
    (nb067_alpha_dummy_017 x y) ≠ (nb067_alpha_dummy_018 x y) := by
  simpa only [nb067_alpha_dummy_017, nb067_alpha_dummy_018] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_324 :
    (nb067_alpha_dummy_027) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_023)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_023)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_023))).fv) :=
  by
  simpa only [nb067_alpha_dummy_027] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_023)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_023)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_023))).fv)
      0

theorem nb067_fresh_325 (x : Var) (y : Var) :
    (nb067_alpha_dummy_028 x y) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_025 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_025 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_025 x y))).fv) :=
  by
  simpa only [nb067_alpha_dummy_028] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_025 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_025 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_025 x y))).fv)
      0

theorem nb067_fresh_326 :
    (nb067_alpha_dummy_055) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_051)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_051)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_051))).fv) :=
  by
  simpa only [nb067_alpha_dummy_055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_051)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_051)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_051))).fv)
      0

theorem nb067_fresh_327 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_056 x y f) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_053 x y f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_056] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_053 x y f))).fv)
      0

theorem nb067_fresh_328 :
    (nb067_alpha_dummy_103) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_099))).fv) :=
  by
  simpa only [nb067_alpha_dummy_103] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_099))).fv)
      0

theorem nb067_fresh_329 (f : Var) :
    (nb067_alpha_dummy_104 f) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_101 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_104] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_101 f))).fv)
      0

theorem nb067_fresh_330 :
    (nb067_alpha_dummy_139) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_135))).fv) :=
  by
  simpa only [nb067_alpha_dummy_139] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_135))).fv)
      0

theorem nb067_fresh_331 (f : Var) :
    (nb067_alpha_dummy_140 f) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_137 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_140] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_137 f))).fv)
      0

theorem nb067_fresh_332 :
    (nb067_alpha_dummy_181) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_177))).fv) :=
  by
  simpa only [nb067_alpha_dummy_181] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_177))).fv)
      0

theorem nb067_fresh_333 (f : Var) :
    (nb067_alpha_dummy_182 f) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_179 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_182] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_179 f))).fv)
      0

theorem nb067_fresh_334 :
    (nb067_alpha_dummy_217) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_213))).fv) :=
  by
  simpa only [nb067_alpha_dummy_217] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_213))).fv)
      0

theorem nb067_fresh_335 (f : Var) :
    (nb067_alpha_dummy_218 f) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_215 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_218] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_215 f))).fv)
      0

theorem nb067_fresh_336 :
    (nb067_alpha_dummy_253) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_249))).fv) :=
  by
  simpa only [nb067_alpha_dummy_253] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_249))).fv)
      0

theorem nb067_fresh_337 (f : Var) :
    (nb067_alpha_dummy_254 f) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_251 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_254] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_251 f))).fv)
      0

theorem nb067_fresh_338 :
    (nb067_alpha_dummy_293) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_289)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_289)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_289))).fv) :=
  by
  simpa only [nb067_alpha_dummy_293] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_289)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_289)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_289))).fv)
      0

theorem nb067_fresh_339 (f : Var) :
    (nb067_alpha_dummy_294 f) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_291 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_291 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_291 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_294] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_291 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_291 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_291 f))).fv)
      0

theorem nb067_fresh_340 :
    (nb067_alpha_dummy_337) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_333))).fv) :=
  by
  simpa only [nb067_alpha_dummy_337] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_333))).fv)
      0

theorem nb067_fresh_341 (f : Var) :
    (nb067_alpha_dummy_338 f) ∉
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_335 f))).fv) :=
  by
  simpa only [nb067_alpha_dummy_338] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_335 f))).fv)
      0

theorem nb067_fresh_342 :
    (nb067_alpha_dummy_277) ∉
      (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb067_alpha_dummy_277] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv)
      0

theorem nb067_fresh_343 :
    (nb067_alpha_dummy_278) ∉
      (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb067_alpha_dummy_278] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv)
      1

theorem nb067_distinct_344 : (nb067_alpha_dummy_277) ≠ (nb067_alpha_dummy_278) := by
  simpa only [nb067_alpha_dummy_277, nb067_alpha_dummy_278] using
    (freshVar_injective
      (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb067_fresh_345 (f : Var) :
    (nb067_alpha_dummy_279 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_279] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0

theorem nb067_fresh_346 (f : Var) :
    (nb067_alpha_dummy_280 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_280] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1

theorem nb067_distinct_347 (f : Var) :
    (nb067_alpha_dummy_279 f) ≠ (nb067_alpha_dummy_280 f) := by
  simpa only [nb067_alpha_dummy_279, nb067_alpha_dummy_280] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_348 :
    (nb067_alpha_dummy_081) ∉
      (((syn_ccom (Class.cv (nb067_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb067_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb067_alpha_dummy_081] using
    freshVar_not_mem
      (((syn_ccom (Class.cv (nb067_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb067_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb067_fresh_349 (f : Var) :
    (nb067_alpha_dummy_082 f) ∉
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb067_alpha_dummy_082] using
    freshVar_not_mem
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0

theorem nb067_fresh_350 :
    (nb067_alpha_dummy_011) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
                (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_007)
              (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
                (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_007)
              (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_351 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_012 x y f) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f)
              (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f)
                (Class.cv (nb067_alpha_dummy_004 x y f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_012] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f)
              (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f)
                (Class.cv (nb067_alpha_dummy_004 x y f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_352 :
    (nb067_alpha_dummy_019) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_015)
              (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_016)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_015)
              (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_019] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_015)
              (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_016)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_015)
              (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_353 (x : Var) (y : Var) :
    (nb067_alpha_dummy_020 x y) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y)
              (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_017 x y)
              (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_020] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y)
              (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_017 x y)
              (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_354 :
    (nb067_alpha_dummy_095) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_091)
              (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_091)
              (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_095] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_091)
              (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_091)
              (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_355 (f : Var) :
    (nb067_alpha_dummy_096 f) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f)
              (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_093 f)
              (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_096] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f)
              (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_093 f)
              (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_356 :
    (nb067_alpha_dummy_131) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_127)
              (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_127)
              (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_131] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_127)
              (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_127)
              (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_357 (f : Var) :
    (nb067_alpha_dummy_132 f) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f)
              (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_129 f)
              (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_132] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f)
              (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_129 f)
              (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_358 :
    (nb067_alpha_dummy_173) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_169)
              (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_170)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_169)
              (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_173] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_169)
              (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_170)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_169)
              (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_359 (f : Var) :
    (nb067_alpha_dummy_174 f) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f)
              (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_171 f)
              (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_174] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f)
              (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_171 f)
              (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_360 :
    (nb067_alpha_dummy_209) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_205)
              (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_206)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_205)
              (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_209] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_205)
              (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_206)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_205)
              (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_361 (f : Var) :
    (nb067_alpha_dummy_210 f) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f)
              (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_207 f)
              (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_210] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f)
              (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_207 f)
              (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_362 :
    (nb067_alpha_dummy_245) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_241)
              (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_242)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_241)
              (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_245] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_241)
              (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_242)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_241)
              (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_363 (f : Var) :
    (nb067_alpha_dummy_246 f) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f)
              (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_243 f)
              (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_246] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f)
              (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_243 f)
              (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_364 :
    (nb067_alpha_dummy_285) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_281)
              (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_282)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_281)
              (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_285] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_281)
              (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_282)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_281)
              (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_365 (f : Var) :
    (nb067_alpha_dummy_286 f) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f)
              (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_283 f)
              (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_286] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f)
              (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_283 f)
              (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_366 :
    (nb067_alpha_dummy_329) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_325)
              (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_326)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_325)
              (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_329] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_325)
              (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_326)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_325)
              (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_367 (f : Var) :
    (nb067_alpha_dummy_330 f) ∉
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f)
              (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_327 f)
              (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb067_alpha_dummy_330] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f)
              (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_327 f)
              (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb067_fresh_368 :
    (nb067_alpha_dummy_039) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_030)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_031)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_030)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_031)))).fv)
      0

theorem nb067_fresh_369 (x : Var) (y : Var) :
    (nb067_alpha_dummy_040 x y) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_033 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_034 x y)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_033 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_034 x y)))).fv)
      0

theorem nb067_fresh_370 :
    (nb067_alpha_dummy_067) ∉
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_058)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_059)))).fv) :=
  by
  simpa only [nb067_alpha_dummy_067] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_058)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_059)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
