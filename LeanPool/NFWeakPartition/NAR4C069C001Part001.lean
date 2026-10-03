/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C069C001Part001. -/


public section


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
noncomputable def nb069_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb069_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb069_alpha_dummy_002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

@[expose]
noncomputable def nb069_alpha_dummy_003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

@[expose]
noncomputable def nb069_alpha_dummy_004 : Var :=
  (freshVar
    (({(nb069_alpha_dummy_000)} : Finset Var) ∪ ({(nb069_alpha_dummy_001)} : Finset Var) ∪
      ((syn_wrex (nb069_alpha_dummy_002) (Class.cv (nb069_alpha_dummy_000))
          (syn_wrex (nb069_alpha_dummy_003) (Class.cv (nb069_alpha_dummy_001))
            (syn_wss (Class.cv (nb069_alpha_dummy_002))
              (Class.cv (nb069_alpha_dummy_003)))))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_005 (x : Var) (y : Var) (a : Var) (b : Var) : Var :=
  (freshVar (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((syn_wrex x (Class.cv a)
          (syn_wrex y (Class.cv b) (syn_wss (Class.cv x) (Class.cv y))))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_006 : Var :=
  (freshVar
    (((Class.cv (nb069_alpha_dummy_000))).fv ∪ ((Class.cv (nb069_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_007 : Var :=
  (freshVar
    (((Class.cv (nb069_alpha_dummy_000))).fv ∪ ((Class.cv (nb069_alpha_dummy_001))).fv) 1)

@[expose]
noncomputable def nb069_alpha_dummy_008 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_009 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 1)

@[expose]
noncomputable def nb069_alpha_dummy_010 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cphi (Class.cv (nb069_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_011 (a : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_012 : Var :=
  (freshVar (((Class.cab (nb069_alpha_dummy_006)
          (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
              (syn_cphi (Class.cv (nb069_alpha_dummy_007))))))).fv ∪
      ((Class.cab (nb069_alpha_dummy_006)
          (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
              (syn_cphi (Class.cv (nb069_alpha_dummy_007))))))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_013 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb069_alpha_dummy_008 a b)
          (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
              (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))))).fv ∪
      ((Class.cab (nb069_alpha_dummy_008 a b) (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
              (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_014 : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_007))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_015 : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_007))).fv) 1)

@[expose]
noncomputable def nb069_alpha_dummy_016 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_009 a b))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_017 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_009 a b))).fv) 1)

@[expose]
noncomputable def nb069_alpha_dummy_018 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb069_alpha_dummy_014)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb069_alpha_dummy_014)) (syn_c1c))).fv ∪
      ((Class.cv (nb069_alpha_dummy_014))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_019 (a : Var) (b : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb069_alpha_dummy_016 a b)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb069_alpha_dummy_016 a b)) (syn_c1c))).fv ∪
      ((Class.cv (nb069_alpha_dummy_016 a b))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_020 : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_021 : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb069_alpha_dummy_022 : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb069_alpha_dummy_023 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_024 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb069_alpha_dummy_025 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb069_alpha_dummy_026 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb069_alpha_dummy_021))
          (Class.cv (nb069_alpha_dummy_022)))).fv ∪
      ((syn_cnin (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022)))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_027 (a : Var) (b : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb069_alpha_dummy_024 a b))
          (Class.cv (nb069_alpha_dummy_025 a b)))).fv ∪
      ((syn_cnin (Class.cv (nb069_alpha_dummy_024 a b))
          (Class.cv (nb069_alpha_dummy_025 a b)))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_028 : Var :=
  (freshVar
    (((Class.cv (nb069_alpha_dummy_021))).fv ∪ ((Class.cv (nb069_alpha_dummy_022))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_029 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_024 a b))).fv ∪
      ((Class.cv (nb069_alpha_dummy_025 a b))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_030 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb069_alpha_dummy_021)))).fv ∪
      ((syn_ccompl (Class.cv (nb069_alpha_dummy_022)))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_031 (a : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb069_alpha_dummy_024 a b)))).fv ∪
      ((syn_ccompl (Class.cv (nb069_alpha_dummy_025 a b)))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_032 : Var :=
  (freshVar
    (((Class.cv (nb069_alpha_dummy_021))).fv ∪ ((Class.cv (nb069_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_033 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_024 a b))).fv ∪
      ((Class.cv (nb069_alpha_dummy_024 a b))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_034 : Var :=
  (freshVar
    (((Class.cv (nb069_alpha_dummy_022))).fv ∪ ((Class.cv (nb069_alpha_dummy_022))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_035 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069_alpha_dummy_025 a b))).fv ∪
      ((Class.cv (nb069_alpha_dummy_025 a b))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_036 : Var :=
  (freshVar (((Class.cab (nb069_alpha_dummy_006)
          (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
              (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb069_alpha_dummy_006)
          (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
              (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_037 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb069_alpha_dummy_008 a b)
          (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
            (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
              (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb069_alpha_dummy_008 a b)
          (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
            (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
              (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_038 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb069_alpha_dummy_007))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_039 (a : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_040 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb069_alpha_dummy_007)))).fv ∪
      ((syn_cphi (Class.cv (nb069_alpha_dummy_007)))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_041 (a : Var) (b : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))).fv ∪
      ((syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_042 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb069_alpha_dummy_002))
          (Class.cv (nb069_alpha_dummy_003)))).fv ∪
      ((syn_cnin (Class.cv (nb069_alpha_dummy_002)) (Class.cv (nb069_alpha_dummy_003)))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_043 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪
      ((syn_cnin (Class.cv x) (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_044 : Var :=
  (freshVar
    (((Class.cv (nb069_alpha_dummy_002))).fv ∪ ((Class.cv (nb069_alpha_dummy_003))).fv) 0)

@[expose]
noncomputable def nb069_alpha_dummy_045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

theorem nb069_fresh_000 :
    (nb069_alpha_dummy_012) ∉
      (((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cphi (Class.cv (nb069_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cphi (Class.cv (nb069_alpha_dummy_007))))))).fv) :=
  by
  simpa only [nb069_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cphi (Class.cv (nb069_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cphi (Class.cv (nb069_alpha_dummy_007))))))).fv)
      0

theorem nb069_fresh_001 :
    (nb069_alpha_dummy_036) ∉
      (((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb069_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb069_fresh_002 (a : Var) (b : Var) :
    (nb069_alpha_dummy_013 a b) ∉
      (((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))))).fv ∪
        ((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))))).fv) :=
  by
  simpa only [nb069_alpha_dummy_013] using
    freshVar_not_mem
      (((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))))).fv ∪
        ((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))))).fv)
      0

theorem nb069_fresh_003 (a : Var) (b : Var) :
    (nb069_alpha_dummy_037 a b) ∉
      (((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb069_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb069_fresh_004 (a : Var) (b : Var) :
    (nb069_alpha_dummy_008 a b) ∉ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) := by
  simpa only [nb069_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 0

theorem nb069_fresh_005 (a : Var) (b : Var) :
    (nb069_alpha_dummy_009 a b) ∉ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) := by
  simpa only [nb069_alpha_dummy_009] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 1

theorem nb069_distinct_006 (a : Var) (b : Var) :
    (nb069_alpha_dummy_008 a b) ≠ (nb069_alpha_dummy_009 a b) := by
  simpa only [nb069_alpha_dummy_008, nb069_alpha_dummy_009] using
    (freshVar_injective (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (i := 0) (j := 1) (by decide))

theorem nb069_fresh_007 :
    (nb069_alpha_dummy_006) ∉
      (((Class.cv (nb069_alpha_dummy_000))).fv ∪ ((Class.cv (nb069_alpha_dummy_001))).fv) :=
  by
  simpa only [nb069_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb069_alpha_dummy_000))).fv ∪ ((Class.cv (nb069_alpha_dummy_001))).fv)
      0

theorem nb069_fresh_008 :
    (nb069_alpha_dummy_007) ∉
      (((Class.cv (nb069_alpha_dummy_000))).fv ∪ ((Class.cv (nb069_alpha_dummy_001))).fv) :=
  by
  simpa only [nb069_alpha_dummy_007] using
    freshVar_not_mem
      (((Class.cv (nb069_alpha_dummy_000))).fv ∪ ((Class.cv (nb069_alpha_dummy_001))).fv)
      1

theorem nb069_distinct_009 : (nb069_alpha_dummy_006) ≠ (nb069_alpha_dummy_007) := by
  simpa only [nb069_alpha_dummy_006, nb069_alpha_dummy_007] using
    (freshVar_injective
      (((Class.cv (nb069_alpha_dummy_000))).fv ∪ ((Class.cv (nb069_alpha_dummy_001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb069_fresh_010 :
    (nb069_alpha_dummy_044) ∉
      (((Class.cv (nb069_alpha_dummy_002))).fv ∪ ((Class.cv (nb069_alpha_dummy_003))).fv) :=
  by
  simpa only [nb069_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cv (nb069_alpha_dummy_002))).fv ∪ ((Class.cv (nb069_alpha_dummy_003))).fv)
      0

theorem nb069_fresh_011 :
    (nb069_alpha_dummy_014) ∉ (((Class.cv (nb069_alpha_dummy_007))).fv) := by
  simpa only [nb069_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb069_alpha_dummy_007))).fv) 0

theorem nb069_fresh_012 :
    (nb069_alpha_dummy_015) ∉ (((Class.cv (nb069_alpha_dummy_007))).fv) := by
  simpa only [nb069_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb069_alpha_dummy_007))).fv) 1

theorem nb069_distinct_013 : (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_015) := by
  simpa only [nb069_alpha_dummy_014, nb069_alpha_dummy_015] using
    (freshVar_injective (((Class.cv (nb069_alpha_dummy_007))).fv) (i := 0) (j := 1) (by decide))

theorem nb069_fresh_014 (a : Var) (b : Var) :
    (nb069_alpha_dummy_016 a b) ∉ (((Class.cv (nb069_alpha_dummy_009 a b))).fv) := by
  simpa only [nb069_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb069_alpha_dummy_009 a b))).fv) 0

theorem nb069_fresh_015 (a : Var) (b : Var) :
    (nb069_alpha_dummy_017 a b) ∉ (((Class.cv (nb069_alpha_dummy_009 a b))).fv) := by
  simpa only [nb069_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb069_alpha_dummy_009 a b))).fv) 1

theorem nb069_distinct_016 (a : Var) (b : Var) :
    (nb069_alpha_dummy_016 a b) ≠ (nb069_alpha_dummy_017 a b) := by
  simpa only [nb069_alpha_dummy_016, nb069_alpha_dummy_017] using
    (freshVar_injective (((Class.cv (nb069_alpha_dummy_009 a b))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb069_fresh_017 :
    (nb069_alpha_dummy_020) ∉
      (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb069_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 0

theorem nb069_fresh_018 :
    (nb069_alpha_dummy_021) ∉
      (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb069_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 1

theorem nb069_fresh_019 :
    (nb069_alpha_dummy_022) ∉
      (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb069_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 2

theorem nb069_distinct_020 : (nb069_alpha_dummy_020) ≠ (nb069_alpha_dummy_021) := by
  simpa only [nb069_alpha_dummy_020, nb069_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb069_distinct_021 : (nb069_alpha_dummy_020) ≠ (nb069_alpha_dummy_022) := by
  simpa only [nb069_alpha_dummy_020, nb069_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb069_distinct_022 : (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_022) := by
  simpa only [nb069_alpha_dummy_021, nb069_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb069_fresh_023 (a : Var) (b : Var) :
    (nb069_alpha_dummy_023 a b) ∉
      (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb069_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 0

theorem nb069_fresh_024 (a : Var) (b : Var) :
    (nb069_alpha_dummy_024 a b) ∉
      (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb069_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 1

theorem nb069_fresh_025 (a : Var) (b : Var) :
    (nb069_alpha_dummy_025 a b) ∉
      (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb069_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 2

theorem nb069_distinct_026 (a : Var) (b : Var) :
    (nb069_alpha_dummy_023 a b) ≠ (nb069_alpha_dummy_024 a b) := by
  simpa only [nb069_alpha_dummy_023, nb069_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb069_distinct_027 (a : Var) (b : Var) :
    (nb069_alpha_dummy_023 a b) ≠ (nb069_alpha_dummy_025 a b) := by
  simpa only [nb069_alpha_dummy_023, nb069_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb069_distinct_028 (a : Var) (b : Var) :
    (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_025 a b) := by
  simpa only [nb069_alpha_dummy_024, nb069_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb069_fresh_029 :
    (nb069_alpha_dummy_032) ∉
      (((Class.cv (nb069_alpha_dummy_021))).fv ∪ ((Class.cv (nb069_alpha_dummy_021))).fv) :=
  by
  simpa only [nb069_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb069_alpha_dummy_021))).fv ∪ ((Class.cv (nb069_alpha_dummy_021))).fv)
      0

theorem nb069_fresh_030 :
    (nb069_alpha_dummy_028) ∉
      (((Class.cv (nb069_alpha_dummy_021))).fv ∪ ((Class.cv (nb069_alpha_dummy_022))).fv) :=
  by
  simpa only [nb069_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb069_alpha_dummy_021))).fv ∪ ((Class.cv (nb069_alpha_dummy_022))).fv)
      0

theorem nb069_fresh_031 :
    (nb069_alpha_dummy_034) ∉
      (((Class.cv (nb069_alpha_dummy_022))).fv ∪ ((Class.cv (nb069_alpha_dummy_022))).fv) :=
  by
  simpa only [nb069_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb069_alpha_dummy_022))).fv ∪ ((Class.cv (nb069_alpha_dummy_022))).fv)
      0

theorem nb069_fresh_032 (a : Var) (b : Var) :
    (nb069_alpha_dummy_033 a b) ∉
      (((Class.cv (nb069_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb069_alpha_dummy_024 a b))).fv) :=
  by
  simpa only [nb069_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb069_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb069_alpha_dummy_024 a b))).fv)
      0

theorem nb069_fresh_033 (a : Var) (b : Var) :
    (nb069_alpha_dummy_029 a b) ∉
      (((Class.cv (nb069_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb069_alpha_dummy_025 a b))).fv) :=
  by
  simpa only [nb069_alpha_dummy_029] using
    freshVar_not_mem
      (((Class.cv (nb069_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb069_alpha_dummy_025 a b))).fv)
      0

theorem nb069_fresh_034 (a : Var) (b : Var) :
    (nb069_alpha_dummy_035 a b) ∉
      (((Class.cv (nb069_alpha_dummy_025 a b))).fv ∪
        ((Class.cv (nb069_alpha_dummy_025 a b))).fv) :=
  by
  simpa only [nb069_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cv (nb069_alpha_dummy_025 a b))).fv ∪
        ((Class.cv (nb069_alpha_dummy_025 a b))).fv)
      0

theorem nb069_fresh_035 (x : Var) (y : Var) :
    (nb069_alpha_dummy_045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb069_alpha_dummy_045] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb069_fresh_036 :
    (nb069_alpha_dummy_018) ∉
      (((Wff.classMem (Class.cv (nb069_alpha_dummy_014)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb069_alpha_dummy_014)) (syn_c1c))).fv ∪
        ((Class.cv (nb069_alpha_dummy_014))).fv) :=
  by
  simpa only [nb069_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb069_alpha_dummy_014)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb069_alpha_dummy_014)) (syn_c1c))).fv ∪
        ((Class.cv (nb069_alpha_dummy_014))).fv)
      0

theorem nb069_fresh_037 (a : Var) (b : Var) :
    (nb069_alpha_dummy_019 a b) ∉
      (((Wff.classMem (Class.cv (nb069_alpha_dummy_016 a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb069_alpha_dummy_016 a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb069_alpha_dummy_016 a b))).fv) :=
  by
  simpa only [nb069_alpha_dummy_019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb069_alpha_dummy_016 a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb069_alpha_dummy_016 a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb069_alpha_dummy_016 a b))).fv)
      0

theorem nb069_fresh_038 :
    (nb069_alpha_dummy_010) ∉
      (((syn_ccompl (Class.cab (nb069_alpha_dummy_006)
              (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb069_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb069_alpha_dummy_006)
              (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb069_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb069_alpha_dummy_006)
              (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb069_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb069_alpha_dummy_006)
              (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb069_fresh_039 (a : Var) (b : Var) :
    (nb069_alpha_dummy_011 a b) ∉
      (((syn_ccompl (Class.cab (nb069_alpha_dummy_008 a b)
              (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                  (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb069_alpha_dummy_008 a b)
              (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                  (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb069_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb069_alpha_dummy_008 a b)
              (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                  (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb069_alpha_dummy_008 a b)
              (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                  (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb069_fresh_040 :
    (nb069_alpha_dummy_030) ∉
      (((syn_ccompl (Class.cv (nb069_alpha_dummy_021)))).fv ∪
        ((syn_ccompl (Class.cv (nb069_alpha_dummy_022)))).fv) :=
  by
  simpa only [nb069_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb069_alpha_dummy_021)))).fv ∪
        ((syn_ccompl (Class.cv (nb069_alpha_dummy_022)))).fv)
      0

theorem nb069_fresh_041 (a : Var) (b : Var) :
    (nb069_alpha_dummy_031 a b) ∉
      (((syn_ccompl (Class.cv (nb069_alpha_dummy_024 a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb069_alpha_dummy_025 a b)))).fv) :=
  by
  simpa only [nb069_alpha_dummy_031] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb069_alpha_dummy_024 a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb069_alpha_dummy_025 a b)))).fv)
      0

theorem nb069_fresh_042 :
    (nb069_alpha_dummy_038) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb069_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb069_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb069_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb069_fresh_043 (a : Var) (b : Var) :
    (nb069_alpha_dummy_039 a b) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb069_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb069_fresh_044 :
    (nb069_alpha_dummy_042) ∉
      (((syn_cnin (Class.cv (nb069_alpha_dummy_002)) (Class.cv (nb069_alpha_dummy_003)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_002))
            (Class.cv (nb069_alpha_dummy_003)))).fv) :=
  by
  simpa only [nb069_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb069_alpha_dummy_002)) (Class.cv (nb069_alpha_dummy_003)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_002)) (Class.cv (nb069_alpha_dummy_003)))).fv)
      0

theorem nb069_fresh_045 :
    (nb069_alpha_dummy_026) ∉
      (((syn_cnin (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_021))
            (Class.cv (nb069_alpha_dummy_022)))).fv) :=
  by
  simpa only [nb069_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022)))).fv)
      0

theorem nb069_fresh_046 (a : Var) (b : Var) :
    (nb069_alpha_dummy_027 a b) ∉
      (((syn_cnin (Class.cv (nb069_alpha_dummy_024 a b))
            (Class.cv (nb069_alpha_dummy_025 a b)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_024 a b))
            (Class.cv (nb069_alpha_dummy_025 a b)))).fv) :=
  by
  simpa only [nb069_alpha_dummy_027] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb069_alpha_dummy_024 a b))
            (Class.cv (nb069_alpha_dummy_025 a b)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_024 a b))
            (Class.cv (nb069_alpha_dummy_025 a b)))).fv)
      0

theorem nb069_fresh_047 (x : Var) (y : Var) :
    (nb069_alpha_dummy_043 x y) ∉
      (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪ ((syn_cnin (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb069_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪ ((syn_cnin (Class.cv x) (Class.cv y))).fv)
      0

theorem nb069_fresh_048 :
    (nb069_alpha_dummy_040) ∉
      (((syn_cphi (Class.cv (nb069_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb069_alpha_dummy_007)))).fv) :=
  by
  simpa only [nb069_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb069_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb069_alpha_dummy_007)))).fv)
      0

theorem nb069_fresh_049 (a : Var) (b : Var) :
    (nb069_alpha_dummy_041 a b) ∉
      (((syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))).fv ∪
        ((syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))).fv) :=
  by
  simpa only [nb069_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))).fv ∪
        ((syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))).fv)
      0

theorem nb069_fresh_050 :
    (nb069_alpha_dummy_004) ∉
      (({(nb069_alpha_dummy_000)} : Finset Var) ∪ ({(nb069_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wrex (nb069_alpha_dummy_002) (Class.cv (nb069_alpha_dummy_000))
            (syn_wrex (nb069_alpha_dummy_003) (Class.cv (nb069_alpha_dummy_001))
              (syn_wss (Class.cv (nb069_alpha_dummy_002))
                (Class.cv (nb069_alpha_dummy_003)))))).fv) :=
  by
  simpa only [nb069_alpha_dummy_004] using
    freshVar_not_mem
      (({(nb069_alpha_dummy_000)} : Finset Var) ∪ ({(nb069_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wrex (nb069_alpha_dummy_002) (Class.cv (nb069_alpha_dummy_000))
            (syn_wrex (nb069_alpha_dummy_003) (Class.cv (nb069_alpha_dummy_001))
              (syn_wss (Class.cv (nb069_alpha_dummy_002))
                (Class.cv (nb069_alpha_dummy_003)))))).fv)
      0

theorem nb069_fresh_051 (x : Var) (y : Var) (a : Var) (b : Var) :
    (nb069_alpha_dummy_005 x y a b) ∉
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((syn_wrex x (Class.cv a)
            (syn_wrex y (Class.cv b) (syn_wss (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb069_alpha_dummy_005] using
    freshVar_not_mem
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((syn_wrex x (Class.cv a)
            (syn_wrex y (Class.cv b) (syn_wss (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb069_fresh_052 : (nb069_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb069_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb069_fresh_053 : (nb069_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb069_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb069_fresh_054 : (nb069_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb069_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb069_fresh_055 : (nb069_alpha_dummy_003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb069_alpha_dummy_003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb069_distinct_056 : (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_001) := by
  simpa only [nb069_alpha_dummy_000, nb069_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb069_distinct_057 : (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_002) := by
  simpa only [nb069_alpha_dummy_000, nb069_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb069_distinct_058 : (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_003) := by
  simpa only [nb069_alpha_dummy_000, nb069_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb069_distinct_059 : (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_002) := by
  simpa only [nb069_alpha_dummy_001, nb069_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb069_distinct_060 : (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_003) := by
  simpa only [nb069_alpha_dummy_001, nb069_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb069_distinct_061 : (nb069_alpha_dummy_002) ≠ (nb069_alpha_dummy_003) := by
  simpa only [nb069_alpha_dummy_002, nb069_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb069_support_mem_0000 :
    (nb069_alpha_dummy_000) ∈
      (({(nb069_alpha_dummy_000)} : Finset Var) ∪ ({(nb069_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wrex (nb069_alpha_dummy_002) (Class.cv (nb069_alpha_dummy_000))
            (syn_wrex (nb069_alpha_dummy_003) (Class.cv (nb069_alpha_dummy_001))
              (syn_wss (Class.cv (nb069_alpha_dummy_002))
                (Class.cv (nb069_alpha_dummy_003)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0001 (x : Var) (y : Var) (a : Var) (b : Var) :
    a ∈
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((syn_wrex x (Class.cv a)
            (syn_wrex y (Class.cv b) (syn_wss (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0002 :
    (nb069_alpha_dummy_001) ∈
      (({(nb069_alpha_dummy_000)} : Finset Var) ∪ ({(nb069_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wrex (nb069_alpha_dummy_002) (Class.cv (nb069_alpha_dummy_000))
            (syn_wrex (nb069_alpha_dummy_003) (Class.cv (nb069_alpha_dummy_001))
              (syn_wss (Class.cv (nb069_alpha_dummy_002))
                (Class.cv (nb069_alpha_dummy_003)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0003 (x : Var) (y : Var) (a : Var) (b : Var) :
    b ∈
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((syn_wrex x (Class.cv a)
            (syn_wrex y (Class.cv b) (syn_wss (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0004 :
    (nb069_alpha_dummy_000) ∈
      (((Class.cv (nb069_alpha_dummy_000))).fv ∪ ((Class.cv (nb069_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0005 :
    (nb069_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb069_alpha_dummy_006)
              (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb069_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb069_alpha_dummy_006)
              (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_006) from (by
          unfold nb069_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_007) from (by
            unfold nb069_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0006 (a : Var) (b : Var) :
    a ∈ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0007 (a : Var) (b : Var) :
    a ∈
      (((syn_ccompl (Class.cab (nb069_alpha_dummy_008 a b)
              (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                  (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb069_alpha_dummy_008 a b)
              (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                  (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb069_alpha_dummy_008 a b) from (by
          unfold nb069_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb069_alpha_dummy_009 a b) from (by
            unfold nb069_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0008 :
    (nb069_alpha_dummy_000) ∈
      (((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cphi (Class.cv (nb069_alpha_dummy_007))))))).fv ∪
        ((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cphi (Class.cv (nb069_alpha_dummy_007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_006) from (by
          unfold nb069_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_007) from (by
            unfold nb069_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0009 (a : Var) (b : Var) :
    a ∈
      (((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))))).fv ∪
        ((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb069_alpha_dummy_008 a b) from (by
          unfold nb069_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb069_alpha_dummy_009 a b) from (by
            unfold nb069_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0010 :
    (nb069_alpha_dummy_007) ∈ (((Class.cv (nb069_alpha_dummy_007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0011 (a : Var) (b : Var) :
    (nb069_alpha_dummy_009 a b) ∈ (((Class.cv (nb069_alpha_dummy_009 a b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0012 :
    (nb069_alpha_dummy_014) ∈
      (((Wff.classMem (Class.cv (nb069_alpha_dummy_014)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb069_alpha_dummy_014)) (syn_c1c))).fv ∪
        ((Class.cv (nb069_alpha_dummy_014))).fv) :=
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

theorem nb069_support_mem_0013 (a : Var) (b : Var) :
    (nb069_alpha_dummy_016 a b) ∈
      (((Wff.classMem (Class.cv (nb069_alpha_dummy_016 a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb069_alpha_dummy_016 a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb069_alpha_dummy_016 a b))).fv) :=
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

theorem nb069_support_mem_0014 :
    (nb069_alpha_dummy_014) ∈
      (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0015 (a : Var) (b : Var) :
    (nb069_alpha_dummy_016 a b) ∈
      (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0016 :
    (nb069_alpha_dummy_021) ∈
      (((syn_cnin (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_021))
            (Class.cv (nb069_alpha_dummy_022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0017 (a : Var) (b : Var) :
    (nb069_alpha_dummy_024 a b) ∈
      (((syn_cnin (Class.cv (nb069_alpha_dummy_024 a b))
            (Class.cv (nb069_alpha_dummy_025 a b)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_024 a b))
            (Class.cv (nb069_alpha_dummy_025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0018 :
    (nb069_alpha_dummy_021) ∈
      (((Class.cv (nb069_alpha_dummy_021))).fv ∪ ((Class.cv (nb069_alpha_dummy_022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0019 (a : Var) (b : Var) :
    (nb069_alpha_dummy_024 a b) ∈
      (((Class.cv (nb069_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb069_alpha_dummy_025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0020 :
    (nb069_alpha_dummy_022) ∈
      (((syn_cnin (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_021))
            (Class.cv (nb069_alpha_dummy_022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0021 (a : Var) (b : Var) :
    (nb069_alpha_dummy_025 a b) ∈
      (((syn_cnin (Class.cv (nb069_alpha_dummy_024 a b))
            (Class.cv (nb069_alpha_dummy_025 a b)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_024 a b))
            (Class.cv (nb069_alpha_dummy_025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0022 :
    (nb069_alpha_dummy_022) ∈
      (((Class.cv (nb069_alpha_dummy_021))).fv ∪ ((Class.cv (nb069_alpha_dummy_022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0023 (a : Var) (b : Var) :
    (nb069_alpha_dummy_025 a b) ∈
      (((Class.cv (nb069_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb069_alpha_dummy_025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0024 :
    (nb069_alpha_dummy_021) ∈
      (((syn_ccompl (Class.cv (nb069_alpha_dummy_021)))).fv ∪
        ((syn_ccompl (Class.cv (nb069_alpha_dummy_022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0025 (a : Var) (b : Var) :
    (nb069_alpha_dummy_024 a b) ∈
      (((syn_ccompl (Class.cv (nb069_alpha_dummy_024 a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb069_alpha_dummy_025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0026 :
    (nb069_alpha_dummy_021) ∈
      (((Class.cv (nb069_alpha_dummy_021))).fv ∪ ((Class.cv (nb069_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0027 (a : Var) (b : Var) :
    (nb069_alpha_dummy_024 a b) ∈
      (((Class.cv (nb069_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb069_alpha_dummy_024 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0028 :
    (nb069_alpha_dummy_022) ∈
      (((syn_ccompl (Class.cv (nb069_alpha_dummy_021)))).fv ∪
        ((syn_ccompl (Class.cv (nb069_alpha_dummy_022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0029 (a : Var) (b : Var) :
    (nb069_alpha_dummy_025 a b) ∈
      (((syn_ccompl (Class.cv (nb069_alpha_dummy_024 a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb069_alpha_dummy_025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0030 :
    (nb069_alpha_dummy_022) ∈
      (((Class.cv (nb069_alpha_dummy_022))).fv ∪ ((Class.cv (nb069_alpha_dummy_022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0031 (a : Var) (b : Var) :
    (nb069_alpha_dummy_025 a b) ∈
      (((Class.cv (nb069_alpha_dummy_025 a b))).fv ∪
        ((Class.cv (nb069_alpha_dummy_025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0032 :
    (nb069_alpha_dummy_001) ∈
      (((Class.cv (nb069_alpha_dummy_000))).fv ∪ ((Class.cv (nb069_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0033 :
    (nb069_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb069_alpha_dummy_006)
              (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb069_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb069_alpha_dummy_006)
              (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_006) from (by
          unfold nb069_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_007) from (by
            unfold nb069_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0032) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0034 (a : Var) (b : Var) :
    b ∈ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0035 (a : Var) (b : Var) :
    b ∈
      (((syn_ccompl (Class.cab (nb069_alpha_dummy_008 a b)
              (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                  (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb069_alpha_dummy_008 a b)
              (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                  (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb069_alpha_dummy_008 a b) from (by
          unfold nb069_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0034 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb069_alpha_dummy_009 a b) from (by
            unfold nb069_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0034 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0036 :
    (nb069_alpha_dummy_001) ∈
      (((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb069_alpha_dummy_006)
            (syn_wrex (nb069_alpha_dummy_007) (Class.cv (nb069_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_006) from (by
          unfold nb069_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_007) from (by
            unfold nb069_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0032) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0037 (a : Var) (b : Var) :
    b ∈
      (((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb069_alpha_dummy_008 a b)
            (syn_wrex (nb069_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb069_alpha_dummy_008 a b) from (by
          unfold nb069_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0034 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb069_alpha_dummy_009 a b) from (by
            unfold nb069_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0034 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0038 :
    (nb069_alpha_dummy_007) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb069_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0039 (a : Var) (b : Var) :
    (nb069_alpha_dummy_009 a b) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0040 :
    (nb069_alpha_dummy_007) ∈
      (((syn_cphi (Class.cv (nb069_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb069_alpha_dummy_007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0041 (a : Var) (b : Var) :
    (nb069_alpha_dummy_009 a b) ∈
      (((syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))).fv ∪
        ((syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
