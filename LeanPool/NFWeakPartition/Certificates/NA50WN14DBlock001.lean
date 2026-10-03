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

/-! Certificates from `NA50WN14DPart001`. -/


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
noncomputable def nb050_alpha_dummy_000 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_001 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({(nb050_alpha_dummy_000 x A B)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv x) A)
          (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_002 (x : Var) (y : Var) (A : Class) (B : Class) :
    Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_003 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_004 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) 1)

@[expose]
noncomputable def nb050_alpha_dummy_005 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_006 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb050_alpha_dummy_007 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb050_alpha_dummy_003 x A B)
            (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B)
              (Class.cv (nb050_alpha_dummy_000 x A B))
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_008 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_009 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (nb050_alpha_dummy_003 x A B)
          (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
            (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
              (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv ∪
      ((Class.cab (nb050_alpha_dummy_003 x A B)
          (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
            (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
              (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_010 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb050_alpha_dummy_005 x y)
          (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
              (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv ∪
      ((Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
              (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_011 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_004 x A B))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_012 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_004 x A B))).fv) 1)

@[expose]
noncomputable def nb050_alpha_dummy_013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_006 x y))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_014 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_006 x y))).fv) 1)

@[expose]
noncomputable def nb050_alpha_dummy_015 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_c1c))).fv ∪
      ((Class.cv (nb050_alpha_dummy_011 x A B))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_016 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb050_alpha_dummy_013 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb050_alpha_dummy_013 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb050_alpha_dummy_013 x y))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_017 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_018 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb050_alpha_dummy_019 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb050_alpha_dummy_020 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb050_alpha_dummy_022 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb050_alpha_dummy_023 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B))
          (Class.cv (nb050_alpha_dummy_019 x A B)))).fv ∪
      ((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B))
          (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_024 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y))
          (Class.cv (nb050_alpha_dummy_022 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y))
          (Class.cv (nb050_alpha_dummy_022 x y)))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_025 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪
      ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_026 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪
      ((Class.cv (nb050_alpha_dummy_022 x y))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_027 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb050_alpha_dummy_018 x A B)))).fv ∪
      ((syn_ccompl (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_028 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb050_alpha_dummy_021 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb050_alpha_dummy_022 x y)))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_029 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪
      ((Class.cv (nb050_alpha_dummy_018 x A B))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_030 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪
      ((Class.cv (nb050_alpha_dummy_021 x y))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_031 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_019 x A B))).fv ∪
      ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb050_alpha_dummy_022 x y))).fv ∪
      ((Class.cv (nb050_alpha_dummy_022 x y))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_033 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (nb050_alpha_dummy_003 x A B)
          (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B))
            (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
              (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_003 x A B)
          (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B))
            (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
              (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_034 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb050_alpha_dummy_005 x y)
          (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
              (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_005 x y)
          (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
              (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_035 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_036 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_037 (x : Var) (A : Class) (B : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv ∪
      ((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv) 0)

@[expose]
noncomputable def nb050_alpha_dummy_038 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart002`. -/


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

theorem nb050_fresh_000 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_033 x A B) ∉
      (((Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B)
              (Class.cv (nb050_alpha_dummy_000 x A B))
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_003 x A B)
            (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B))
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb050_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B)
              (Class.cv (nb050_alpha_dummy_000 x A B))
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_003 x A B)
            (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B))
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb050_fresh_001 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_009 x A B) ∉
      (((Class.cab (nb050_alpha_dummy_003 x A B)
            (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv ∪
        ((Class.cab (nb050_alpha_dummy_003 x A B)
            (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv) :=
  by
  simpa only [nb050_alpha_dummy_009] using
    freshVar_not_mem
      (((Class.cab (nb050_alpha_dummy_003 x A B)
            (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv ∪
        ((Class.cab (nb050_alpha_dummy_003 x A B)
            (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv)
      0

theorem nb050_fresh_002 (x : Var) (y : Var) :
    (nb050_alpha_dummy_010 x y) ∉
      (((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv ∪
        ((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv) :=
  by
  simpa only [nb050_alpha_dummy_010] using
    freshVar_not_mem
      (((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv ∪
        ((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv)
      0

theorem nb050_fresh_003 (x : Var) (y : Var) :
    (nb050_alpha_dummy_034 x y) ∉
      (((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb050_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb050_fresh_004 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_011 x A B) ∉ (((Class.cv (nb050_alpha_dummy_004 x A B))).fv) := by
  simpa only [nb050_alpha_dummy_011] using
    freshVar_not_mem (((Class.cv (nb050_alpha_dummy_004 x A B))).fv) 0

theorem nb050_fresh_005 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_012 x A B) ∉ (((Class.cv (nb050_alpha_dummy_004 x A B))).fv) := by
  simpa only [nb050_alpha_dummy_012] using
    freshVar_not_mem (((Class.cv (nb050_alpha_dummy_004 x A B))).fv) 1

theorem nb050_distinct_006 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_011 x A B) ≠ (nb050_alpha_dummy_012 x A B) := by
  simpa only [nb050_alpha_dummy_011, nb050_alpha_dummy_012] using
    (freshVar_injective (((Class.cv (nb050_alpha_dummy_004 x A B))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb050_fresh_007 (x : Var) (y : Var) :
    (nb050_alpha_dummy_013 x y) ∉ (((Class.cv (nb050_alpha_dummy_006 x y))).fv) := by
  simpa only [nb050_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb050_alpha_dummy_006 x y))).fv) 0

theorem nb050_fresh_008 (x : Var) (y : Var) :
    (nb050_alpha_dummy_014 x y) ∉ (((Class.cv (nb050_alpha_dummy_006 x y))).fv) := by
  simpa only [nb050_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb050_alpha_dummy_006 x y))).fv) 1

theorem nb050_distinct_009 (x : Var) (y : Var) :
    (nb050_alpha_dummy_013 x y) ≠ (nb050_alpha_dummy_014 x y) := by
  simpa only [nb050_alpha_dummy_013, nb050_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb050_alpha_dummy_006 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb050_fresh_010 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_017 x A B) ∉
      (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb050_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) 0

theorem nb050_fresh_011 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_018 x A B) ∉
      (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb050_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) 1

theorem nb050_fresh_012 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_019 x A B) ∉
      (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb050_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) 2

theorem nb050_distinct_013 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_017 x A B) ≠ (nb050_alpha_dummy_018 x A B) := by
  simpa only [nb050_alpha_dummy_017, nb050_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb050_distinct_014 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_017 x A B) ≠ (nb050_alpha_dummy_019 x A B) := by
  simpa only [nb050_alpha_dummy_017, nb050_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb050_distinct_015 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_018 x A B) ≠ (nb050_alpha_dummy_019 x A B) := by
  simpa only [nb050_alpha_dummy_018, nb050_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb050_fresh_016 (x : Var) (y : Var) :
    (nb050_alpha_dummy_020 x y) ∉
      (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb050_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb050_fresh_017 (x : Var) (y : Var) :
    (nb050_alpha_dummy_021 x y) ∉
      (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb050_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb050_fresh_018 (x : Var) (y : Var) :
    (nb050_alpha_dummy_022 x y) ∉
      (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb050_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb050_distinct_019 (x : Var) (y : Var) :
    (nb050_alpha_dummy_020 x y) ≠ (nb050_alpha_dummy_021 x y) := by
  simpa only [nb050_alpha_dummy_020, nb050_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb050_distinct_020 (x : Var) (y : Var) :
    (nb050_alpha_dummy_020 x y) ≠ (nb050_alpha_dummy_022 x y) := by
  simpa only [nb050_alpha_dummy_020, nb050_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb050_distinct_021 (x : Var) (y : Var) :
    (nb050_alpha_dummy_021 x y) ≠ (nb050_alpha_dummy_022 x y) := by
  simpa only [nb050_alpha_dummy_021, nb050_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb050_fresh_022 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_029 x A B) ∉
      (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪
        ((Class.cv (nb050_alpha_dummy_018 x A B))).fv) :=
  by
  simpa only [nb050_alpha_dummy_029] using
    freshVar_not_mem
      (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪
        ((Class.cv (nb050_alpha_dummy_018 x A B))).fv)
      0

theorem nb050_fresh_023 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_025 x A B) ∉
      (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪
        ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) :=
  by
  simpa only [nb050_alpha_dummy_025] using
    freshVar_not_mem
      (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪
        ((Class.cv (nb050_alpha_dummy_019 x A B))).fv)
      0

theorem nb050_fresh_024 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_031 x A B) ∉
      (((Class.cv (nb050_alpha_dummy_019 x A B))).fv ∪
        ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) :=
  by
  simpa only [nb050_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb050_alpha_dummy_019 x A B))).fv ∪
        ((Class.cv (nb050_alpha_dummy_019 x A B))).fv)
      0

theorem nb050_fresh_025 (x : Var) (y : Var) :
    (nb050_alpha_dummy_030 x y) ∉
      (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪
        ((Class.cv (nb050_alpha_dummy_021 x y))).fv) :=
  by
  simpa only [nb050_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪
        ((Class.cv (nb050_alpha_dummy_021 x y))).fv)
      0

theorem nb050_fresh_026 (x : Var) (y : Var) :
    (nb050_alpha_dummy_026 x y) ∉
      (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪
        ((Class.cv (nb050_alpha_dummy_022 x y))).fv) :=
  by
  simpa only [nb050_alpha_dummy_026] using
    freshVar_not_mem
      (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪
        ((Class.cv (nb050_alpha_dummy_022 x y))).fv)
      0

theorem nb050_fresh_027 (x : Var) (y : Var) :
    (nb050_alpha_dummy_032 x y) ∉
      (((Class.cv (nb050_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb050_alpha_dummy_022 x y))).fv) :=
  by
  simpa only [nb050_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb050_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb050_alpha_dummy_022 x y))).fv)
      0

theorem nb050_fresh_028 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_003 x A B) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) :=
  by
  simpa only [nb050_alpha_dummy_003] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) 0

theorem nb050_fresh_029 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_004 x A B) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) :=
  by
  simpa only [nb050_alpha_dummy_004] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) 1

theorem nb050_distinct_030 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_003 x A B) ≠ (nb050_alpha_dummy_004 x A B) := by
  simpa only [nb050_alpha_dummy_003, nb050_alpha_dummy_004] using
    (freshVar_injective
      (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb050_fresh_031 (x : Var) (y : Var) :
    (nb050_alpha_dummy_005 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb050_alpha_dummy_005] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb050_fresh_032 (x : Var) (y : Var) :
    (nb050_alpha_dummy_006 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb050_alpha_dummy_006] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb050_distinct_033 (x : Var) (y : Var) :
    (nb050_alpha_dummy_005 x y) ≠ (nb050_alpha_dummy_006 x y) := by
  simpa only [nb050_alpha_dummy_005, nb050_alpha_dummy_006] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb050_fresh_034 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_015 x A B) ∉
      (((Wff.classMem (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_c1c))).fv ∪
        ((Class.cv (nb050_alpha_dummy_011 x A B))).fv) :=
  by
  simpa only [nb050_alpha_dummy_015] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_c1c))).fv ∪
        ((Class.cv (nb050_alpha_dummy_011 x A B))).fv)
      0

theorem nb050_fresh_035 (x : Var) (y : Var) :
    (nb050_alpha_dummy_016 x y) ∉
      (((Wff.classMem (Class.cv (nb050_alpha_dummy_013 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb050_alpha_dummy_013 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb050_alpha_dummy_013 x y))).fv) :=
  by
  simpa only [nb050_alpha_dummy_016] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb050_alpha_dummy_013 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb050_alpha_dummy_013 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb050_alpha_dummy_013 x y))).fv)
      0

theorem nb050_fresh_036 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_007 x A B) ∉
      (((syn_ccompl (Class.cab (nb050_alpha_dummy_003 x A B)
              (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                  (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B)
                (Class.cv (nb050_alpha_dummy_000 x A B))
                (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                  (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb050_alpha_dummy_007] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb050_alpha_dummy_003 x A B)
              (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                  (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B)
                (Class.cv (nb050_alpha_dummy_000 x A B))
                (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                  (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb050_fresh_037 (x : Var) (y : Var) :
    (nb050_alpha_dummy_008 x y) ∉
      (((syn_ccompl (Class.cab (nb050_alpha_dummy_005 x y)
              (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                  (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb050_alpha_dummy_005 x y)
              (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                  (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb050_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb050_alpha_dummy_005 x y)
              (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                  (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb050_alpha_dummy_005 x y)
              (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                  (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb050_fresh_038 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_027 x A B) ∉
      (((syn_ccompl (Class.cv (nb050_alpha_dummy_018 x A B)))).fv ∪
        ((syn_ccompl (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) :=
  by
  simpa only [nb050_alpha_dummy_027] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb050_alpha_dummy_018 x A B)))).fv ∪
        ((syn_ccompl (Class.cv (nb050_alpha_dummy_019 x A B)))).fv)
      0

theorem nb050_fresh_039 (x : Var) (y : Var) :
    (nb050_alpha_dummy_028 x y) ∉
      (((syn_ccompl (Class.cv (nb050_alpha_dummy_021 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb050_alpha_dummy_022 x y)))).fv) :=
  by
  simpa only [nb050_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb050_alpha_dummy_021 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb050_alpha_dummy_022 x y)))).fv)
      0

theorem nb050_fresh_040 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_035 x A B) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb050_alpha_dummy_035] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb050_fresh_041 (x : Var) (y : Var) :
    (nb050_alpha_dummy_036 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb050_alpha_dummy_036] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb050_fresh_042 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_023 x A B) ∉
      (((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B))
            (Class.cv (nb050_alpha_dummy_019 x A B)))).fv ∪
        ((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B))
            (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) :=
  by
  simpa only [nb050_alpha_dummy_023] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B))
            (Class.cv (nb050_alpha_dummy_019 x A B)))).fv ∪
        ((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B))
            (Class.cv (nb050_alpha_dummy_019 x A B)))).fv)
      0

theorem nb050_fresh_043 (x : Var) (y : Var) :
    (nb050_alpha_dummy_024 x y) ∉
      (((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y))
            (Class.cv (nb050_alpha_dummy_022 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y))
            (Class.cv (nb050_alpha_dummy_022 x y)))).fv) :=
  by
  simpa only [nb050_alpha_dummy_024] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y))
            (Class.cv (nb050_alpha_dummy_022 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y))
            (Class.cv (nb050_alpha_dummy_022 x y)))).fv)
      0

theorem nb050_fresh_044 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_037 x A B) ∉
      (((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv ∪
        ((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv) :=
  by
  simpa only [nb050_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv ∪
        ((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv)
      0

theorem nb050_fresh_045 (x : Var) (y : Var) :
    (nb050_alpha_dummy_038 x y) ∉
      (((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv) :=
  by
  simpa only [nb050_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv)
      0

theorem nb050_fresh_046 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_000 x A B) ∉ (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb050_alpha_dummy_000] using
    freshVar_not_mem (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) 0

theorem nb050_fresh_047 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_001 x A B) ∉
      (({ x } : Finset Var) ∪ ({(nb050_alpha_dummy_000 x A B)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) A)
            (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B))).fv) :=
  by
  simpa only [nb050_alpha_dummy_001] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({(nb050_alpha_dummy_000 x A B)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) A)
            (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B))).fv)
      0

theorem nb050_fresh_048 (x : Var) (y : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_002 x y A B) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B))).fv) :=
  by
  simpa only [nb050_alpha_dummy_002] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B))).fv)
      0

theorem nb050_support_mem_0000 (x : Var) (A : Class) (B : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({(nb050_alpha_dummy_000 x A B)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) A)
            (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart003`. -/


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

theorem nb050_support_mem_0001 (x : Var) (y : Var) (A : Class) (B : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0002 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_000 x A B) ∈
      (({ x } : Finset Var) ∪ ({(nb050_alpha_dummy_000 x A B)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) A)
            (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0003 (x : Var) (y : Var) (A : Class) (B : Class) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0004 (x : Var) (A : Class) (B : Class) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0005 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0006 (x : Var) (A : Class) (B : Class) :
    x ∈
      (((Class.cab (nb050_alpha_dummy_003 x A B)
            (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv ∪
        ((Class.cab (nb050_alpha_dummy_003 x A B)
            (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv ∪
        ((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0008 (x : Var) (A : Class) (B : Class) :
    x ∈
      (((syn_ccompl (Class.cab (nb050_alpha_dummy_003 x A B)
              (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                  (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B)
                (Class.cv (nb050_alpha_dummy_000 x A B))
                (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                  (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0009 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb050_alpha_dummy_005 x y)
              (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                  (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb050_alpha_dummy_005 x y)
              (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                  (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0010 (x : Var) (A : Class) (B : Class) :
    x ∈ (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0011 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_004 x A B) ∈ (((Class.cv (nb050_alpha_dummy_004 x A B))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0012 (x : Var) (y : Var) :
    (nb050_alpha_dummy_006 x y) ∈ (((Class.cv (nb050_alpha_dummy_006 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0013 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_011 x A B) ∈
      (((Wff.classMem (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_c1c))).fv ∪
        ((Class.cv (nb050_alpha_dummy_011 x A B))).fv) :=
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

theorem nb050_support_mem_0014 (x : Var) (y : Var) :
    (nb050_alpha_dummy_013 x y) ∈
      (((Wff.classMem (Class.cv (nb050_alpha_dummy_013 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb050_alpha_dummy_013 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb050_alpha_dummy_013 x y))).fv) :=
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

theorem nb050_support_mem_0015 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_011 x A B) ∈
      (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0016 (x : Var) (y : Var) :
    (nb050_alpha_dummy_013 x y) ∈
      (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0017 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_018 x A B) ∈
      (((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B))
            (Class.cv (nb050_alpha_dummy_019 x A B)))).fv ∪
        ((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B))
            (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0018 (x : Var) (y : Var) :
    (nb050_alpha_dummy_021 x y) ∈
      (((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y))
            (Class.cv (nb050_alpha_dummy_022 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y))
            (Class.cv (nb050_alpha_dummy_022 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0019 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_018 x A B) ∈
      (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪
        ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0020 (x : Var) (y : Var) :
    (nb050_alpha_dummy_021 x y) ∈
      (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪
        ((Class.cv (nb050_alpha_dummy_022 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0021 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_019 x A B) ∈
      (((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B))
            (Class.cv (nb050_alpha_dummy_019 x A B)))).fv ∪
        ((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B))
            (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0022 (x : Var) (y : Var) :
    (nb050_alpha_dummy_022 x y) ∈
      (((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y))
            (Class.cv (nb050_alpha_dummy_022 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y))
            (Class.cv (nb050_alpha_dummy_022 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0023 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_019 x A B) ∈
      (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪
        ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0024 (x : Var) (y : Var) :
    (nb050_alpha_dummy_022 x y) ∈
      (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪
        ((Class.cv (nb050_alpha_dummy_022 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0025 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_018 x A B) ∈
      (((syn_ccompl (Class.cv (nb050_alpha_dummy_018 x A B)))).fv ∪
        ((syn_ccompl (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0026 (x : Var) (y : Var) :
    (nb050_alpha_dummy_021 x y) ∈
      (((syn_ccompl (Class.cv (nb050_alpha_dummy_021 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb050_alpha_dummy_022 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0027 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_018 x A B) ∈
      (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪
        ((Class.cv (nb050_alpha_dummy_018 x A B))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0028 (x : Var) (y : Var) :
    (nb050_alpha_dummy_021 x y) ∈
      (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪
        ((Class.cv (nb050_alpha_dummy_021 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0029 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_019 x A B) ∈
      (((syn_ccompl (Class.cv (nb050_alpha_dummy_018 x A B)))).fv ∪
        ((syn_ccompl (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0030 (x : Var) (y : Var) :
    (nb050_alpha_dummy_022 x y) ∈
      (((syn_ccompl (Class.cv (nb050_alpha_dummy_021 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb050_alpha_dummy_022 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0031 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_019 x A B) ∈
      (((Class.cv (nb050_alpha_dummy_019 x A B))).fv ∪
        ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0032 (x : Var) (y : Var) :
    (nb050_alpha_dummy_022 x y) ∈
      (((Class.cv (nb050_alpha_dummy_022 x y))).fv ∪
        ((Class.cv (nb050_alpha_dummy_022 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0033 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_000 x A B) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0034 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_000 x A B) ∈
      (((syn_ccompl (Class.cab (nb050_alpha_dummy_003 x A B)
              (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                  (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B)
                (Class.cv (nb050_alpha_dummy_000 x A B))
                (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                  (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0033 x A B) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0033 x A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0035 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0036 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb050_alpha_dummy_005 x y)
              (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                  (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb050_alpha_dummy_005 x y)
              (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                  (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0035 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0035 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0037 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_000 x A B) ∈
      (((Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B)
              (Class.cv (nb050_alpha_dummy_000 x A B))
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_003 x A B)
            (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B))
              (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0033 x A B) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0033 x A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0038 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_005 x y)
            (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
                (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0035 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0035 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0039 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_004 x A B) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0040 (x : Var) (y : Var) :
    (nb050_alpha_dummy_006 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0041 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_004 x A B) ∈
      (((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv ∪
        ((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0042 (x : Var) (y : Var) :
    (nb050_alpha_dummy_006 x y) ∈
      (((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_wpp_notmem_0000 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_004 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [nb050_alpha_dummy_004, fv_class_cv, Finset.mem_singleton] using
    (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 1)))

theorem nb050_wpp_notmem_0001 (x : Var) (y : Var) :
    (nb050_alpha_dummy_006 x y) ∉ ((Class.cv x)).fv := by
  simpa only [nb050_alpha_dummy_006, fv_class_cv, Finset.mem_singleton] using
    (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 1)))

theorem nb050_wpp_notmem_0002 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_003 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [nb050_alpha_dummy_003, fv_class_cv, Finset.mem_singleton] using
    (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 0)))

theorem nb050_wpp_notmem_0003 (x : Var) (y : Var) :
    (nb050_alpha_dummy_005 x y) ∉ ((Class.cv x)).fv := by
  simpa only [nb050_alpha_dummy_005, fv_class_cv, Finset.mem_singleton] using
    (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 0)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart004`. -/


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

theorem nb050_wpp_notmem_0004 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_009 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [nb050_alpha_dummy_009, fv_class_cv, Finset.mem_singleton] using
    (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0006 x A B) 0)))

theorem nb050_wpp_notmem_0005 (x : Var) (y : Var) :
    (nb050_alpha_dummy_010 x y) ∉ ((Class.cv x)).fv := by
  simpa only [nb050_alpha_dummy_010, fv_class_cv, Finset.mem_singleton] using
    (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0007 x y) 0)))

theorem nb050_wpp_notmem_0006 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_007 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [nb050_alpha_dummy_007, fv_class_cv, Finset.mem_singleton] using
    (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0008 x A B) 0)))

theorem nb050_wpp_notmem_0007 (x : Var) (y : Var) :
    (nb050_alpha_dummy_008 x y) ∉ ((Class.cv x)).fv := by
  simpa only [nb050_alpha_dummy_008, fv_class_cv, Finset.mem_singleton] using
    (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0009 x y) 0)))

theorem nb050_compact_fv_empty_0008 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_000 x A B) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0008 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_000 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [nb050_alpha_dummy_000, fv_class_cv, Finset.mem_singleton] using
    (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0010 x A B) 0)))

theorem nb050_compact_fv_empty_0009 (y : Var) : y ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0009 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    y ∉ ((Class.cv x)).fv := by
  simp only [fv_class_cv, (Ne.symm dv_x_y), Finset.mem_singleton, not_false_eq_true]

theorem nb050_compact_fv_empty_0010 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_001 x A B) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0010 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_001 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [nb050_alpha_dummy_001, fv_class_cv, Finset.mem_singleton] using
    (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0000 x A B) 0)))

theorem nb050_compact_fv_empty_0011 (x : Var) (y : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_002 x y A B) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0011 (x : Var) (y : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_002 x y A B) ∉ ((Class.cv x)).fv := by
  simpa only [nb050_alpha_dummy_002, fv_class_cv, Finset.mem_singleton] using
    (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0001 x y A B) 0)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart005`. -/


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

theorem nb050_compact_envfresh_0000 (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) :
    TEnvFresh
      [((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
        ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
        ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)),
        ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
        ((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
      ((Class.cv x)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb050_alpha_dummy_004 x A B) (nb050_alpha_dummy_006 x y)
      (nb050_wpp_notmem_0000 x A B) (nb050_wpp_notmem_0001 x y)
      (TEnvFresh.consFresh (nb050_alpha_dummy_003 x A B) (nb050_alpha_dummy_005 x y)
        (nb050_wpp_notmem_0002 x A B) (nb050_wpp_notmem_0003 x y)
        (TEnvFresh.consFresh (nb050_alpha_dummy_009 x A B) (nb050_alpha_dummy_010 x y)
          (nb050_wpp_notmem_0004 x A B) (nb050_wpp_notmem_0005 x y)
          (TEnvFresh.consFresh (nb050_alpha_dummy_007 x A B) (nb050_alpha_dummy_008 x y)
            (nb050_wpp_notmem_0006 x A B) (nb050_wpp_notmem_0007 x y)
            (TEnvFresh.consFresh (nb050_alpha_dummy_000 x A B) y
              (nb050_wpp_notmem_0008 x A B) (nb050_wpp_notmem_0009 x y dv_x_y)
              (TEnvFresh.consSame x (TEnvFresh.consFresh (nb050_alpha_dummy_001 x A B)
                  (nb050_alpha_dummy_002 x y A B) (nb050_wpp_notmem_0010 x A B)
                  (nb050_wpp_notmem_0011 x y A B) (TEnvFresh.nil ((Class.cv x)).fv))))))))

@[expose]
noncomputable def nb050_wpp_refl_0000 (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) :
    TReflOn
      [((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
        ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
        ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)),
        ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
        ((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
      ((Class.cv x)).fv :=
  TEnvFresh.reflOn (nb050_compact_envfresh_0000 x y A B dv_x_y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
