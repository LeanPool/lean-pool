/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C058C001Part001. -/


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
noncomputable def nb058_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb058_alpha_dummy_001 : Var :=
  (freshVar (({(nb058_alpha_dummy_000)} : Finset Var) ∪ ((syn_c1c)).fv ∪
      ((syn_cpw1 (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_002 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((syn_c1c)).fv ∪ ((syn_cpw1 (syn_cuni (Class.cv x)))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_003 : Var :=
  (freshVar
    (({(nb058_alpha_dummy_000)} : Finset Var) ∪ ({(nb058_alpha_dummy_001)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb058_alpha_dummy_000)) (syn_c1c))
          (Wff.classEq (Class.cv (nb058_alpha_dummy_001))
            (syn_cpw1 (syn_cuni (Class.cv (nb058_alpha_dummy_000))))))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_004 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({(nb058_alpha_dummy_002 x)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv x) (syn_c1c))
          (Wff.classEq (Class.cv (nb058_alpha_dummy_002 x))
            (syn_cpw1 (syn_cuni (Class.cv x)))))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_005 : Var :=
  (freshVar
    (((Class.cv (nb058_alpha_dummy_000))).fv ∪ ((Class.cv (nb058_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_006 : Var :=
  (freshVar
    (((Class.cv (nb058_alpha_dummy_000))).fv ∪ ((Class.cv (nb058_alpha_dummy_001))).fv) 1)

@[expose]
noncomputable def nb058_alpha_dummy_007 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb058_alpha_dummy_002 x))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_008 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb058_alpha_dummy_002 x))).fv) 1)

@[expose]
noncomputable def nb058_alpha_dummy_009 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cphi (Class.cv (nb058_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_010 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb058_alpha_dummy_007 x)
            (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb058_alpha_dummy_007 x)
            (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_011 : Var :=
  (freshVar (((Class.cab (nb058_alpha_dummy_005)
          (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
              (syn_cphi (Class.cv (nb058_alpha_dummy_006))))))).fv ∪
      ((Class.cab (nb058_alpha_dummy_005)
          (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
              (syn_cphi (Class.cv (nb058_alpha_dummy_006))))))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_012 (x : Var) : Var :=
  (freshVar (((Class.cab (nb058_alpha_dummy_007 x)
          (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
              (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))))).fv ∪
      ((Class.cab (nb058_alpha_dummy_007 x) (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
              (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_013 : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_006))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_014 : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_006))).fv) 1)

@[expose]
noncomputable def nb058_alpha_dummy_015 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_008 x))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_016 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_008 x))).fv) 1)

@[expose]
noncomputable def nb058_alpha_dummy_017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb058_alpha_dummy_013)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb058_alpha_dummy_013)) (syn_c1c))).fv ∪
      ((Class.cv (nb058_alpha_dummy_013))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_018 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb058_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb058_alpha_dummy_015 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb058_alpha_dummy_015 x))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_019 : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_020 : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb058_alpha_dummy_021 : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb058_alpha_dummy_022 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_023 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb058_alpha_dummy_024 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb058_alpha_dummy_025 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb058_alpha_dummy_020))
          (Class.cv (nb058_alpha_dummy_021)))).fv ∪
      ((syn_cnin (Class.cv (nb058_alpha_dummy_020)) (Class.cv (nb058_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_026 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb058_alpha_dummy_023 x))
          (Class.cv (nb058_alpha_dummy_024 x)))).fv ∪
      ((syn_cnin (Class.cv (nb058_alpha_dummy_023 x)) (Class.cv (nb058_alpha_dummy_024 x)))).fv)
    0)

@[expose]
noncomputable def nb058_alpha_dummy_027 : Var :=
  (freshVar
    (((Class.cv (nb058_alpha_dummy_020))).fv ∪ ((Class.cv (nb058_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_028 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_023 x))).fv ∪
      ((Class.cv (nb058_alpha_dummy_024 x))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_029 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb058_alpha_dummy_020)))).fv ∪
      ((syn_ccompl (Class.cv (nb058_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_030 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb058_alpha_dummy_023 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb058_alpha_dummy_024 x)))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_031 : Var :=
  (freshVar
    (((Class.cv (nb058_alpha_dummy_020))).fv ∪ ((Class.cv (nb058_alpha_dummy_020))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_032 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_023 x))).fv ∪
      ((Class.cv (nb058_alpha_dummy_023 x))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_033 : Var :=
  (freshVar
    (((Class.cv (nb058_alpha_dummy_021))).fv ∪ ((Class.cv (nb058_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_034 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_024 x))).fv ∪
      ((Class.cv (nb058_alpha_dummy_024 x))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_035 : Var :=
  (freshVar (((Class.cab (nb058_alpha_dummy_005)
          (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb058_alpha_dummy_005)
          (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_036 (x : Var) : Var :=
  (freshVar (((Class.cab (nb058_alpha_dummy_007 x)
          (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
              (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb058_alpha_dummy_007 x)
          (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
              (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_037 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb058_alpha_dummy_006))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_038 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_039 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb058_alpha_dummy_006)))).fv ∪
      ((syn_cphi (Class.cv (nb058_alpha_dummy_006)))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_040 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))).fv ∪
      ((syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_041 : Var :=
  (freshVar (((syn_cnin (syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000)))) (syn_c1c))).fv ∪
      ((syn_cnin (syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000)))) (syn_c1c))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_042 (x : Var) : Var :=
  (freshVar (((syn_cnin (syn_cpw (syn_cuni (Class.cv x))) (syn_c1c))).fv ∪
      ((syn_cnin (syn_cpw (syn_cuni (Class.cv x))) (syn_c1c))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_043 : Var :=
  (freshVar (((syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_044 (x : Var) : Var :=
  (freshVar (((syn_cpw (syn_cuni (Class.cv x)))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_045 : Var :=
  (freshVar (((syn_cuni (Class.cv (nb058_alpha_dummy_000)))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_046 (x : Var) : Var :=
  (freshVar (((syn_cuni (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_047 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb058_alpha_dummy_045))
          (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv ∪
      ((syn_cnin (Class.cv (nb058_alpha_dummy_045))
          (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_048 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb058_alpha_dummy_046 x)) (syn_cuni (Class.cv x)))).fv ∪
      ((syn_cnin (Class.cv (nb058_alpha_dummy_046 x)) (syn_cuni (Class.cv x)))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_049 : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_045))).fv ∪
      ((syn_cuni (Class.cv (nb058_alpha_dummy_000)))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_050 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_046 x))).fv ∪ ((syn_cuni (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_051 : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_052 : Var :=
  (freshVar (((Class.cv (nb058_alpha_dummy_000))).fv) 1)

@[expose]
noncomputable def nb058_alpha_dummy_053 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb058_alpha_dummy_054 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 1)

theorem nb058_fresh_000 :
    (nb058_alpha_dummy_011) ∉
      (((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cphi (Class.cv (nb058_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cphi (Class.cv (nb058_alpha_dummy_006))))))).fv) :=
  by
  simpa only [nb058_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cphi (Class.cv (nb058_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cphi (Class.cv (nb058_alpha_dummy_006))))))).fv)
      0

theorem nb058_fresh_001 :
    (nb058_alpha_dummy_035) ∉
      (((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb058_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb058_fresh_002 (x : Var) :
    (nb058_alpha_dummy_036 x) ∉
      (((Class.cab (nb058_alpha_dummy_007 x)
            (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb058_alpha_dummy_007 x)
            (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb058_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb058_alpha_dummy_007 x)
            (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb058_alpha_dummy_007 x)
            (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb058_fresh_003 (x : Var) :
    (nb058_alpha_dummy_012 x) ∉
      (((Class.cab (nb058_alpha_dummy_007 x) (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb058_alpha_dummy_007 x) (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))))).fv) :=
  by
  simpa only [nb058_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb058_alpha_dummy_007 x) (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb058_alpha_dummy_007 x) (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))))).fv)
      0

theorem nb058_fresh_004 :
    (nb058_alpha_dummy_051) ∉ (((Class.cv (nb058_alpha_dummy_000))).fv) := by
  simpa only [nb058_alpha_dummy_051] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_000))).fv) 0

theorem nb058_fresh_005 :
    (nb058_alpha_dummy_052) ∉ (((Class.cv (nb058_alpha_dummy_000))).fv) := by
  simpa only [nb058_alpha_dummy_052] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_000))).fv) 1

theorem nb058_distinct_006 : (nb058_alpha_dummy_051) ≠ (nb058_alpha_dummy_052) := by
  simpa only [nb058_alpha_dummy_051, nb058_alpha_dummy_052] using
    (freshVar_injective (((Class.cv (nb058_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb058_fresh_007 :
    (nb058_alpha_dummy_005) ∉
      (((Class.cv (nb058_alpha_dummy_000))).fv ∪ ((Class.cv (nb058_alpha_dummy_001))).fv) :=
  by
  simpa only [nb058_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb058_alpha_dummy_000))).fv ∪ ((Class.cv (nb058_alpha_dummy_001))).fv)
      0

theorem nb058_fresh_008 :
    (nb058_alpha_dummy_006) ∉
      (((Class.cv (nb058_alpha_dummy_000))).fv ∪ ((Class.cv (nb058_alpha_dummy_001))).fv) :=
  by
  simpa only [nb058_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb058_alpha_dummy_000))).fv ∪ ((Class.cv (nb058_alpha_dummy_001))).fv)
      1

theorem nb058_distinct_009 : (nb058_alpha_dummy_005) ≠ (nb058_alpha_dummy_006) := by
  simpa only [nb058_alpha_dummy_005, nb058_alpha_dummy_006] using
    (freshVar_injective
      (((Class.cv (nb058_alpha_dummy_000))).fv ∪ ((Class.cv (nb058_alpha_dummy_001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb058_fresh_010 :
    (nb058_alpha_dummy_013) ∉ (((Class.cv (nb058_alpha_dummy_006))).fv) := by
  simpa only [nb058_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_006))).fv) 0

theorem nb058_fresh_011 :
    (nb058_alpha_dummy_014) ∉ (((Class.cv (nb058_alpha_dummy_006))).fv) := by
  simpa only [nb058_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_006))).fv) 1

theorem nb058_distinct_012 : (nb058_alpha_dummy_013) ≠ (nb058_alpha_dummy_014) := by
  simpa only [nb058_alpha_dummy_013, nb058_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb058_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb058_fresh_013 (x : Var) :
    (nb058_alpha_dummy_015 x) ∉ (((Class.cv (nb058_alpha_dummy_008 x))).fv) := by
  simpa only [nb058_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_008 x))).fv) 0

theorem nb058_fresh_014 (x : Var) :
    (nb058_alpha_dummy_016 x) ∉ (((Class.cv (nb058_alpha_dummy_008 x))).fv) := by
  simpa only [nb058_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_008 x))).fv) 1

theorem nb058_distinct_015 (x : Var) :
    (nb058_alpha_dummy_015 x) ≠ (nb058_alpha_dummy_016 x) := by
  simpa only [nb058_alpha_dummy_015, nb058_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb058_alpha_dummy_008 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb058_fresh_016 :
    (nb058_alpha_dummy_019) ∉
      (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb058_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0

theorem nb058_fresh_017 :
    (nb058_alpha_dummy_020) ∉
      (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb058_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1

theorem nb058_fresh_018 :
    (nb058_alpha_dummy_021) ∉
      (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb058_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2

theorem nb058_distinct_019 : (nb058_alpha_dummy_019) ≠ (nb058_alpha_dummy_020) := by
  simpa only [nb058_alpha_dummy_019, nb058_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb058_distinct_020 : (nb058_alpha_dummy_019) ≠ (nb058_alpha_dummy_021) := by
  simpa only [nb058_alpha_dummy_019, nb058_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb058_distinct_021 : (nb058_alpha_dummy_020) ≠ (nb058_alpha_dummy_021) := by
  simpa only [nb058_alpha_dummy_020, nb058_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb058_fresh_022 (x : Var) :
    (nb058_alpha_dummy_022 x) ∉
      (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb058_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb058_fresh_023 (x : Var) :
    (nb058_alpha_dummy_023 x) ∉
      (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb058_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb058_fresh_024 (x : Var) :
    (nb058_alpha_dummy_024 x) ∉
      (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb058_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb058_distinct_025 (x : Var) :
    (nb058_alpha_dummy_022 x) ≠ (nb058_alpha_dummy_023 x) := by
  simpa only [nb058_alpha_dummy_022, nb058_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb058_distinct_026 (x : Var) :
    (nb058_alpha_dummy_022 x) ≠ (nb058_alpha_dummy_024 x) := by
  simpa only [nb058_alpha_dummy_022, nb058_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb058_distinct_027 (x : Var) :
    (nb058_alpha_dummy_023 x) ≠ (nb058_alpha_dummy_024 x) := by
  simpa only [nb058_alpha_dummy_023, nb058_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb058_fresh_028 :
    (nb058_alpha_dummy_031) ∉
      (((Class.cv (nb058_alpha_dummy_020))).fv ∪ ((Class.cv (nb058_alpha_dummy_020))).fv) :=
  by
  simpa only [nb058_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb058_alpha_dummy_020))).fv ∪ ((Class.cv (nb058_alpha_dummy_020))).fv)
      0

theorem nb058_fresh_029 :
    (nb058_alpha_dummy_027) ∉
      (((Class.cv (nb058_alpha_dummy_020))).fv ∪ ((Class.cv (nb058_alpha_dummy_021))).fv) :=
  by
  simpa only [nb058_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb058_alpha_dummy_020))).fv ∪ ((Class.cv (nb058_alpha_dummy_021))).fv)
      0

theorem nb058_fresh_030 :
    (nb058_alpha_dummy_033) ∉
      (((Class.cv (nb058_alpha_dummy_021))).fv ∪ ((Class.cv (nb058_alpha_dummy_021))).fv) :=
  by
  simpa only [nb058_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb058_alpha_dummy_021))).fv ∪ ((Class.cv (nb058_alpha_dummy_021))).fv)
      0

theorem nb058_fresh_031 (x : Var) :
    (nb058_alpha_dummy_032 x) ∉
      (((Class.cv (nb058_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb058_alpha_dummy_023 x))).fv) :=
  by
  simpa only [nb058_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb058_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb058_alpha_dummy_023 x))).fv)
      0

theorem nb058_fresh_032 (x : Var) :
    (nb058_alpha_dummy_028 x) ∉
      (((Class.cv (nb058_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb058_alpha_dummy_024 x))).fv) :=
  by
  simpa only [nb058_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb058_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb058_alpha_dummy_024 x))).fv)
      0

theorem nb058_fresh_033 (x : Var) :
    (nb058_alpha_dummy_034 x) ∉
      (((Class.cv (nb058_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb058_alpha_dummy_024 x))).fv) :=
  by
  simpa only [nb058_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb058_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb058_alpha_dummy_024 x))).fv)
      0

theorem nb058_fresh_034 :
    (nb058_alpha_dummy_049) ∉
      (((Class.cv (nb058_alpha_dummy_045))).fv ∪
        ((syn_cuni (Class.cv (nb058_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb058_alpha_dummy_049] using
    freshVar_not_mem
      (((Class.cv (nb058_alpha_dummy_045))).fv ∪
        ((syn_cuni (Class.cv (nb058_alpha_dummy_000)))).fv)
      0

theorem nb058_fresh_035 (x : Var) :
    (nb058_alpha_dummy_050 x) ∉
      (((Class.cv (nb058_alpha_dummy_046 x))).fv ∪ ((syn_cuni (Class.cv x))).fv) :=
  by
  simpa only [nb058_alpha_dummy_050] using
    freshVar_not_mem
      (((Class.cv (nb058_alpha_dummy_046 x))).fv ∪ ((syn_cuni (Class.cv x))).fv) 0

theorem nb058_fresh_036 (x : Var) : (nb058_alpha_dummy_053 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb058_alpha_dummy_053] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb058_fresh_037 (x : Var) : (nb058_alpha_dummy_054 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb058_alpha_dummy_054] using freshVar_not_mem (((Class.cv x)).fv) 1

theorem nb058_distinct_038 (x : Var) :
    (nb058_alpha_dummy_053 x) ≠ (nb058_alpha_dummy_054 x) := by
  simpa only [nb058_alpha_dummy_053, nb058_alpha_dummy_054] using
    (freshVar_injective (((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb058_fresh_039 (x : Var) :
    (nb058_alpha_dummy_007 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb058_alpha_dummy_002 x))).fv) :=
  by
  simpa only [nb058_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb058_alpha_dummy_002 x))).fv) 0

theorem nb058_fresh_040 (x : Var) :
    (nb058_alpha_dummy_008 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb058_alpha_dummy_002 x))).fv) :=
  by
  simpa only [nb058_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb058_alpha_dummy_002 x))).fv) 1

theorem nb058_distinct_041 (x : Var) :
    (nb058_alpha_dummy_007 x) ≠ (nb058_alpha_dummy_008 x) := by
  simpa only [nb058_alpha_dummy_007, nb058_alpha_dummy_008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb058_alpha_dummy_002 x))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb058_fresh_042 :
    (nb058_alpha_dummy_017) ∉
      (((Wff.classMem (Class.cv (nb058_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb058_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb058_alpha_dummy_013))).fv) :=
  by
  simpa only [nb058_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb058_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb058_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb058_alpha_dummy_013))).fv)
      0

theorem nb058_fresh_043 (x : Var) :
    (nb058_alpha_dummy_018 x) ∉
      (((Wff.classMem (Class.cv (nb058_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb058_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb058_alpha_dummy_015 x))).fv) :=
  by
  simpa only [nb058_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb058_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb058_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb058_alpha_dummy_015 x))).fv)
      0

theorem nb058_fresh_044 :
    (nb058_alpha_dummy_009) ∉
      (((syn_ccompl (Class.cab (nb058_alpha_dummy_005)
              (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb058_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb058_alpha_dummy_005)
              (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb058_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb058_alpha_dummy_005)
              (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb058_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb058_alpha_dummy_005)
              (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb058_fresh_045 (x : Var) :
    (nb058_alpha_dummy_010 x) ∉
      (((syn_ccompl (Class.cab (nb058_alpha_dummy_007 x)
              (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb058_alpha_dummy_007 x)
              (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb058_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb058_alpha_dummy_007 x)
              (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb058_alpha_dummy_007 x)
              (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb058_fresh_046 :
    (nb058_alpha_dummy_029) ∉
      (((syn_ccompl (Class.cv (nb058_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb058_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb058_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb058_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb058_alpha_dummy_021)))).fv)
      0

theorem nb058_fresh_047 (x : Var) :
    (nb058_alpha_dummy_030 x) ∉
      (((syn_ccompl (Class.cv (nb058_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb058_alpha_dummy_024 x)))).fv) :=
  by
  simpa only [nb058_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb058_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb058_alpha_dummy_024 x)))).fv)
      0

theorem nb058_fresh_048 :
    (nb058_alpha_dummy_037) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb058_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb058_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb058_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb058_fresh_049 (x : Var) :
    (nb058_alpha_dummy_038 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb058_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb058_fresh_050 :
    (nb058_alpha_dummy_025) ∉
      (((syn_cnin (Class.cv (nb058_alpha_dummy_020)) (Class.cv (nb058_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_020))
            (Class.cv (nb058_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb058_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb058_alpha_dummy_020)) (Class.cv (nb058_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_020)) (Class.cv (nb058_alpha_dummy_021)))).fv)
      0

theorem nb058_fresh_051 (x : Var) :
    (nb058_alpha_dummy_026 x) ∉
      (((syn_cnin (Class.cv (nb058_alpha_dummy_023 x))
            (Class.cv (nb058_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_023 x))
            (Class.cv (nb058_alpha_dummy_024 x)))).fv) :=
  by
  simpa only [nb058_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb058_alpha_dummy_023 x))
            (Class.cv (nb058_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_023 x))
            (Class.cv (nb058_alpha_dummy_024 x)))).fv)
      0

theorem nb058_fresh_052 :
    (nb058_alpha_dummy_047) ∉
      (((syn_cnin (Class.cv (nb058_alpha_dummy_045))
            (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_045))
            (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv) :=
  by
  simpa only [nb058_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb058_alpha_dummy_045))
            (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_045))
            (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv)
      0

theorem nb058_fresh_053 (x : Var) :
    (nb058_alpha_dummy_048 x) ∉
      (((syn_cnin (Class.cv (nb058_alpha_dummy_046 x)) (syn_cuni (Class.cv x)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_046 x)) (syn_cuni (Class.cv x)))).fv) :=
  by
  simpa only [nb058_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb058_alpha_dummy_046 x)) (syn_cuni (Class.cv x)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_046 x)) (syn_cuni (Class.cv x)))).fv)
      0

theorem nb058_fresh_054 :
    (nb058_alpha_dummy_041) ∉
      (((syn_cnin (syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000)))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000)))) (syn_c1c))).fv) :=
  by
  simpa only [nb058_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_cnin (syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000)))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000)))) (syn_c1c))).fv)
      0

theorem nb058_fresh_055 (x : Var) :
    (nb058_alpha_dummy_042 x) ∉
      (((syn_cnin (syn_cpw (syn_cuni (Class.cv x))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (syn_cuni (Class.cv x))) (syn_c1c))).fv) :=
  by
  simpa only [nb058_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_cnin (syn_cpw (syn_cuni (Class.cv x))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (syn_cuni (Class.cv x))) (syn_c1c))).fv)
      0

theorem nb058_fresh_056 :
    (nb058_alpha_dummy_039) ∉
      (((syn_cphi (Class.cv (nb058_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb058_alpha_dummy_006)))).fv) :=
  by
  simpa only [nb058_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb058_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb058_alpha_dummy_006)))).fv)
      0

theorem nb058_fresh_057 (x : Var) :
    (nb058_alpha_dummy_040 x) ∉
      (((syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))).fv) :=
  by
  simpa only [nb058_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))).fv)
      0

theorem nb058_fresh_058 :
    (nb058_alpha_dummy_043) ∉
      (((syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb058_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv ∪ ((syn_c1c)).fv) 0

theorem nb058_fresh_059 (x : Var) :
    (nb058_alpha_dummy_044 x) ∉
      (((syn_cpw (syn_cuni (Class.cv x)))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb058_alpha_dummy_044] using
    freshVar_not_mem (((syn_cpw (syn_cuni (Class.cv x)))).fv ∪ ((syn_c1c)).fv) 0

theorem nb058_fresh_060 :
    (nb058_alpha_dummy_045) ∉ (((syn_cuni (Class.cv (nb058_alpha_dummy_000)))).fv) := by
  simpa only [nb058_alpha_dummy_045] using
    freshVar_not_mem (((syn_cuni (Class.cv (nb058_alpha_dummy_000)))).fv) 0

theorem nb058_fresh_061 (x : Var) :
    (nb058_alpha_dummy_046 x) ∉ (((syn_cuni (Class.cv x))).fv) := by
  simpa only [nb058_alpha_dummy_046] using
    freshVar_not_mem (((syn_cuni (Class.cv x))).fv) 0

theorem nb058_fresh_062 :
    (nb058_alpha_dummy_001) ∉
      (({(nb058_alpha_dummy_000)} : Finset Var) ∪ ((syn_c1c)).fv ∪
        ((syn_cpw1 (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv) :=
  by
  simpa only [nb058_alpha_dummy_001] using
    freshVar_not_mem
      (({(nb058_alpha_dummy_000)} : Finset Var) ∪ ((syn_c1c)).fv ∪
        ((syn_cpw1 (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv)
      0

theorem nb058_fresh_063 :
    (nb058_alpha_dummy_003) ∉
      (({(nb058_alpha_dummy_000)} : Finset Var) ∪ ({(nb058_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb058_alpha_dummy_000)) (syn_c1c))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_001))
              (syn_cpw1 (syn_cuni (Class.cv (nb058_alpha_dummy_000))))))).fv) :=
  by
  simpa only [nb058_alpha_dummy_003] using
    freshVar_not_mem
      (({(nb058_alpha_dummy_000)} : Finset Var) ∪ ({(nb058_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb058_alpha_dummy_000)) (syn_c1c))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_001))
              (syn_cpw1 (syn_cuni (Class.cv (nb058_alpha_dummy_000))))))).fv)
      0

theorem nb058_fresh_064 (x : Var) :
    (nb058_alpha_dummy_002 x) ∉
      (({ x } : Finset Var) ∪ ((syn_c1c)).fv ∪ ((syn_cpw1 (syn_cuni (Class.cv x)))).fv) :=
  by
  simpa only [nb058_alpha_dummy_002] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((syn_c1c)).fv ∪ ((syn_cpw1 (syn_cuni (Class.cv x)))).fv) 0

theorem nb058_fresh_065 (x : Var) :
    (nb058_alpha_dummy_004 x) ∉
      (({ x } : Finset Var) ∪ ({(nb058_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_c1c))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_002 x))
              (syn_cpw1 (syn_cuni (Class.cv x)))))).fv) :=
  by
  simpa only [nb058_alpha_dummy_004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({(nb058_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_c1c))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_002 x))
              (syn_cpw1 (syn_cuni (Class.cv x)))))).fv)
      0

theorem nb058_fresh_066 : (nb058_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb058_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb058_support_mem_0000 :
    (nb058_alpha_dummy_000) ∈
      (({(nb058_alpha_dummy_000)} : Finset Var) ∪ ({(nb058_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb058_alpha_dummy_000)) (syn_c1c))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_001))
              (syn_cpw1 (syn_cuni (Class.cv (nb058_alpha_dummy_000))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0001 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({(nb058_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_c1c))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_002 x))
              (syn_cpw1 (syn_cuni (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0002 :
    (nb058_alpha_dummy_001) ∈
      (({(nb058_alpha_dummy_000)} : Finset Var) ∪ ({(nb058_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb058_alpha_dummy_000)) (syn_c1c))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_001))
              (syn_cpw1 (syn_cuni (Class.cv (nb058_alpha_dummy_000))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0003 (x : Var) :
    (nb058_alpha_dummy_002 x) ∈
      (({ x } : Finset Var) ∪ ({(nb058_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_c1c))
            (Wff.classEq (Class.cv (nb058_alpha_dummy_002 x))
              (syn_cpw1 (syn_cuni (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0004 :
    (nb058_alpha_dummy_000) ∈
      (({(nb058_alpha_dummy_000)} : Finset Var) ∪ ((syn_c1c)).fv ∪
        ((syn_cpw1 (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0005 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((syn_c1c)).fv ∪ ((syn_cpw1 (syn_cuni (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0006 :
    (nb058_alpha_dummy_000) ∈
      (((Class.cv (nb058_alpha_dummy_000))).fv ∪ ((Class.cv (nb058_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0007 :
    (nb058_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb058_alpha_dummy_005)
              (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb058_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb058_alpha_dummy_005)
              (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0008 (x : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb058_alpha_dummy_002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0009 (x : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb058_alpha_dummy_007 x)
              (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb058_alpha_dummy_007 x)
              (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0010 :
    (nb058_alpha_dummy_000) ∈
      (((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cphi (Class.cv (nb058_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cphi (Class.cv (nb058_alpha_dummy_006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0011 (x : Var) :
    x ∈
      (((Class.cab (nb058_alpha_dummy_007 x) (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb058_alpha_dummy_007 x) (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0012 :
    (nb058_alpha_dummy_006) ∈ (((Class.cv (nb058_alpha_dummy_006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0013 (x : Var) :
    (nb058_alpha_dummy_008 x) ∈ (((Class.cv (nb058_alpha_dummy_008 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0014 :
    (nb058_alpha_dummy_013) ∈
      (((Wff.classMem (Class.cv (nb058_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb058_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb058_alpha_dummy_013))).fv) :=
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

theorem nb058_support_mem_0015 (x : Var) :
    (nb058_alpha_dummy_015 x) ∈
      (((Wff.classMem (Class.cv (nb058_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb058_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb058_alpha_dummy_015 x))).fv) :=
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

theorem nb058_support_mem_0016 :
    (nb058_alpha_dummy_013) ∈
      (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0017 (x : Var) :
    (nb058_alpha_dummy_015 x) ∈
      (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0018 :
    (nb058_alpha_dummy_020) ∈
      (((syn_cnin (Class.cv (nb058_alpha_dummy_020)) (Class.cv (nb058_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_020))
            (Class.cv (nb058_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0019 (x : Var) :
    (nb058_alpha_dummy_023 x) ∈
      (((syn_cnin (Class.cv (nb058_alpha_dummy_023 x))
            (Class.cv (nb058_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_023 x))
            (Class.cv (nb058_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0020 :
    (nb058_alpha_dummy_020) ∈
      (((Class.cv (nb058_alpha_dummy_020))).fv ∪ ((Class.cv (nb058_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0021 (x : Var) :
    (nb058_alpha_dummy_023 x) ∈
      (((Class.cv (nb058_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb058_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0022 :
    (nb058_alpha_dummy_021) ∈
      (((syn_cnin (Class.cv (nb058_alpha_dummy_020)) (Class.cv (nb058_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_020))
            (Class.cv (nb058_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0023 (x : Var) :
    (nb058_alpha_dummy_024 x) ∈
      (((syn_cnin (Class.cv (nb058_alpha_dummy_023 x))
            (Class.cv (nb058_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_023 x))
            (Class.cv (nb058_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0024 :
    (nb058_alpha_dummy_021) ∈
      (((Class.cv (nb058_alpha_dummy_020))).fv ∪ ((Class.cv (nb058_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0025 (x : Var) :
    (nb058_alpha_dummy_024 x) ∈
      (((Class.cv (nb058_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb058_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0026 :
    (nb058_alpha_dummy_020) ∈
      (((syn_ccompl (Class.cv (nb058_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb058_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0027 (x : Var) :
    (nb058_alpha_dummy_023 x) ∈
      (((syn_ccompl (Class.cv (nb058_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb058_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
