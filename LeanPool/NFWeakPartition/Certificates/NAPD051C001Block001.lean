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

/-! Certificates from `NAPD051C001Part001`. -/


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
noncomputable def nb051_alpha_dummy_000 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_001 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪
      ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
          (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_002 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
          (Wff.classEq (Class.cv z) C))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_003 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_004 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) 1)

@[expose]
noncomputable def nb051_alpha_dummy_005 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_006 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 1)

@[expose]
noncomputable def nb051_alpha_dummy_007 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C)
            (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb051_alpha_dummy_003 x y A B C)
            (syn_wrex (nb051_alpha_dummy_004 x y A B C)
              (Class.cv (nb051_alpha_dummy_000 x y A B C))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_008 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_009 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cab (nb051_alpha_dummy_003 x y A B C)
          (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
              (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv ∪
      ((Class.cab (nb051_alpha_dummy_003 x y A B C)
          (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
              (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_010 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb051_alpha_dummy_005 x y z)
          (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
              (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv ∪
      ((Class.cab (nb051_alpha_dummy_005 x y z)
          (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
              (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_011 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_012 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) 1)

@[expose]
noncomputable def nb051_alpha_dummy_013 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_014 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) 1)

@[expose]
noncomputable def nb051_alpha_dummy_015 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_c1c))).fv ∪
      ((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_016 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_c1c))).fv ∪
      ((Class.cv (nb051_alpha_dummy_013 x y z))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_017 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_018 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb051_alpha_dummy_019 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb051_alpha_dummy_020 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_021 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb051_alpha_dummy_022 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb051_alpha_dummy_023 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C))
          (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv ∪
      ((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C))
          (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_024 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z))
          (Class.cv (nb051_alpha_dummy_022 x y z)))).fv ∪
      ((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z))
          (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_025 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪
      ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_026 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪
      ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_027 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb051_alpha_dummy_018 x y A B C)))).fv ∪
      ((syn_ccompl (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_028 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb051_alpha_dummy_021 x y z)))).fv ∪
      ((syn_ccompl (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_029 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪
      ((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_030 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪
      ((Class.cv (nb051_alpha_dummy_021 x y z))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_031 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv ∪
      ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_032 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb051_alpha_dummy_022 x y z))).fv ∪
      ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_033 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((Class.cab (nb051_alpha_dummy_003 x y A B C)
          (syn_wrex (nb051_alpha_dummy_004 x y A B C)
            (Class.cv (nb051_alpha_dummy_000 x y A B C))
            (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
              (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C)
          (syn_wrex (nb051_alpha_dummy_004 x y A B C)
            (Class.cv (nb051_alpha_dummy_000 x y A B C))
            (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
              (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_034 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb051_alpha_dummy_005 x y z)
          (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
            (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
              (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z)
          (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
            (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
              (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_035 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_036 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_037 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv ∪
      ((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv) 0)

@[expose]
noncomputable def nb051_alpha_dummy_038 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv ∪
      ((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part002`. -/


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

theorem nb051_fresh_000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_033 x y A B C) ∉
      (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C)
              (Class.cv (nb051_alpha_dummy_000 x y A B C))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C)
            (syn_wrex (nb051_alpha_dummy_004 x y A B C)
              (Class.cv (nb051_alpha_dummy_000 x y A B C))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb051_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C)
              (Class.cv (nb051_alpha_dummy_000 x y A B C))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C)
            (syn_wrex (nb051_alpha_dummy_004 x y A B C)
              (Class.cv (nb051_alpha_dummy_000 x y A B C))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb051_fresh_001 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_009 x y A B C) ∉
      (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C)
              (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv ∪
        ((Class.cab (nb051_alpha_dummy_003 x y A B C)
            (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv) :=
  by
  simpa only [nb051_alpha_dummy_009] using
    freshVar_not_mem
      (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C)
              (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv ∪
        ((Class.cab (nb051_alpha_dummy_003 x y A B C)
            (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv)
      0

theorem nb051_fresh_002 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_034 x y z) ∉
      (((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb051_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb051_fresh_003 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_010 x y z) ∉
      (((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv ∪
        ((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv) :=
  by
  simpa only [nb051_alpha_dummy_010] using
    freshVar_not_mem
      (((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv ∪
        ((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv)
      0

theorem nb051_fresh_004 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_011 x y A B C) ∉
      (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) :=
  by
  simpa only [nb051_alpha_dummy_011] using
    freshVar_not_mem (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) 0

theorem nb051_fresh_005 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_012 x y A B C) ∉
      (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) :=
  by
  simpa only [nb051_alpha_dummy_012] using
    freshVar_not_mem (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) 1

theorem nb051_distinct_006 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_011 x y A B C) ≠ (nb051_alpha_dummy_012 x y A B C) := by
  simpa only [nb051_alpha_dummy_011, nb051_alpha_dummy_012] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb051_fresh_007 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_013 x y z) ∉ (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) := by
  simpa only [nb051_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) 0

theorem nb051_fresh_008 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_014 x y z) ∉ (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) := by
  simpa only [nb051_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) 1

theorem nb051_distinct_009 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_013 x y z) ≠ (nb051_alpha_dummy_014 x y z) := by
  simpa only [nb051_alpha_dummy_013, nb051_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb051_fresh_010 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_017 x y A B C) ∉
      (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb051_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv)
      0

theorem nb051_fresh_011 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_018 x y A B C) ∉
      (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb051_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv)
      1

theorem nb051_fresh_012 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_019 x y A B C) ∉
      (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb051_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv)
      2

theorem nb051_distinct_013 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_017 x y A B C) ≠ (nb051_alpha_dummy_018 x y A B C) := by
  simpa only [nb051_alpha_dummy_017, nb051_alpha_dummy_018] using
    (freshVar_injective
      (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb051_distinct_014 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_017 x y A B C) ≠ (nb051_alpha_dummy_019 x y A B C) := by
  simpa only [nb051_alpha_dummy_017, nb051_alpha_dummy_019] using
    (freshVar_injective
      (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) (i := 0) (j :=
      2) (by decide))

theorem nb051_distinct_015 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_018 x y A B C) ≠ (nb051_alpha_dummy_019 x y A B C) := by
  simpa only [nb051_alpha_dummy_018, nb051_alpha_dummy_019] using
    (freshVar_injective
      (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) (i := 1) (j :=
      2) (by decide))

theorem nb051_fresh_016 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_020 x y z) ∉
      (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb051_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 0

theorem nb051_fresh_017 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_021 x y z) ∉
      (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb051_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 1

theorem nb051_fresh_018 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_022 x y z) ∉
      (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb051_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 2

theorem nb051_distinct_019 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_020 x y z) ≠ (nb051_alpha_dummy_021 x y z) := by
  simpa only [nb051_alpha_dummy_020, nb051_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb051_distinct_020 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_020 x y z) ≠ (nb051_alpha_dummy_022 x y z) := by
  simpa only [nb051_alpha_dummy_020, nb051_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb051_distinct_021 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_021 x y z) ≠ (nb051_alpha_dummy_022 x y z) := by
  simpa only [nb051_alpha_dummy_021, nb051_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb051_fresh_022 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_029 x y A B C) ∉
      (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪
        ((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv) :=
  by
  simpa only [nb051_alpha_dummy_029] using
    freshVar_not_mem
      (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪
        ((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv)
      0

theorem nb051_fresh_023 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_025 x y A B C) ∉
      (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪
        ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) :=
  by
  simpa only [nb051_alpha_dummy_025] using
    freshVar_not_mem
      (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪
        ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv)
      0

theorem nb051_fresh_024 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_031 x y A B C) ∉
      (((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv ∪
        ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) :=
  by
  simpa only [nb051_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv ∪
        ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv)
      0

theorem nb051_fresh_025 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_030 x y z) ∉
      (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪
        ((Class.cv (nb051_alpha_dummy_021 x y z))).fv) :=
  by
  simpa only [nb051_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪
        ((Class.cv (nb051_alpha_dummy_021 x y z))).fv)
      0

theorem nb051_fresh_026 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_026 x y z) ∉
      (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪
        ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) :=
  by
  simpa only [nb051_alpha_dummy_026] using
    freshVar_not_mem
      (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪
        ((Class.cv (nb051_alpha_dummy_022 x y z))).fv)
      0

theorem nb051_fresh_027 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_032 x y z) ∉
      (((Class.cv (nb051_alpha_dummy_022 x y z))).fv ∪
        ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) :=
  by
  simpa only [nb051_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb051_alpha_dummy_022 x y z))).fv ∪
        ((Class.cv (nb051_alpha_dummy_022 x y z))).fv)
      0

theorem nb051_fresh_028 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_015 x y A B C) ∉
      (((Wff.classMem (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_c1c))).fv ∪
        ((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv) :=
  by
  simpa only [nb051_alpha_dummy_015] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_c1c))).fv ∪
        ((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv)
      0

theorem nb051_fresh_029 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_016 x y z) ∉
      (((Wff.classMem (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_c1c))).fv ∪
        ((Class.cv (nb051_alpha_dummy_013 x y z))).fv) :=
  by
  simpa only [nb051_alpha_dummy_016] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_c1c))).fv ∪
        ((Class.cv (nb051_alpha_dummy_013 x y z))).fv)
      0

theorem nb051_fresh_030 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_007 x y A B C) ∉
      (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C)
                (Class.cv (nb051_alpha_dummy_000 x y A B C))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb051_alpha_dummy_007] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C)
                (Class.cv (nb051_alpha_dummy_000 x y A B C))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb051_fresh_031 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_008 x y z) ∉
      (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb051_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb051_fresh_032 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_027 x y A B C) ∉
      (((syn_ccompl (Class.cv (nb051_alpha_dummy_018 x y A B C)))).fv ∪
        ((syn_ccompl (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) :=
  by
  simpa only [nb051_alpha_dummy_027] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb051_alpha_dummy_018 x y A B C)))).fv ∪
        ((syn_ccompl (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv)
      0

theorem nb051_fresh_033 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_028 x y z) ∉
      (((syn_ccompl (Class.cv (nb051_alpha_dummy_021 x y z)))).fv ∪
        ((syn_ccompl (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) :=
  by
  simpa only [nb051_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb051_alpha_dummy_021 x y z)))).fv ∪
        ((syn_ccompl (Class.cv (nb051_alpha_dummy_022 x y z)))).fv)
      0

theorem nb051_fresh_034 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_035 x y A B C) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb051_alpha_dummy_035] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb051_fresh_035 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_036 x y z) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb051_alpha_dummy_036] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb051_fresh_036 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_023 x y A B C) ∉
      (((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C))
            (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv ∪
        ((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C))
            (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) :=
  by
  simpa only [nb051_alpha_dummy_023] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C))
            (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv ∪
        ((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C))
            (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv)
      0

theorem nb051_fresh_037 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_024 x y z) ∉
      (((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z))
            (Class.cv (nb051_alpha_dummy_022 x y z)))).fv ∪
        ((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z))
            (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) :=
  by
  simpa only [nb051_alpha_dummy_024] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z))
            (Class.cv (nb051_alpha_dummy_022 x y z)))).fv ∪
        ((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z))
            (Class.cv (nb051_alpha_dummy_022 x y z)))).fv)
      0

theorem nb051_fresh_038 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_003 x y A B C) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) :=
  by
  simpa only [nb051_alpha_dummy_003] using
    freshVar_not_mem
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv)
      0

theorem nb051_fresh_039 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_004 x y A B C) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) :=
  by
  simpa only [nb051_alpha_dummy_004] using
    freshVar_not_mem
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv)
      1

theorem nb051_distinct_040 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_003 x y A B C) ≠ (nb051_alpha_dummy_004 x y A B C) := by
  simpa only [nb051_alpha_dummy_003, nb051_alpha_dummy_004] using
    (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) (i := 0) (j := 1) (by decide))

theorem nb051_fresh_041 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_005 x y z) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) :=
  by
  simpa only [nb051_alpha_dummy_005] using
    freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 0

theorem nb051_fresh_042 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_006 x y z) ∉
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) :=
  by
  simpa only [nb051_alpha_dummy_006] using
    freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 1

theorem nb051_distinct_043 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_005 x y z) ≠ (nb051_alpha_dummy_006 x y z) := by
  simpa only [nb051_alpha_dummy_005, nb051_alpha_dummy_006] using
    (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb051_fresh_044 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_037 x y A B C) ∉
      (((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv ∪
        ((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv) :=
  by
  simpa only [nb051_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv ∪
        ((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv)
      0

theorem nb051_fresh_045 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_038 x y z) ∉
      (((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv ∪
        ((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv) :=
  by
  simpa only [nb051_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv ∪
        ((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv)
      0

theorem nb051_fresh_046 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_000 x y A B C) ∉
      (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) :=
  by
  simpa only [nb051_alpha_dummy_000] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0

theorem nb051_fresh_047 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_001 x y A B C) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) :=
  by
  simpa only [nb051_alpha_dummy_001] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv)
      0

theorem nb051_fresh_048 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    (nb051_alpha_dummy_002 x y z A B C) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv z) C))).fv) :=
  by
  simpa only [nb051_alpha_dummy_002] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv z) C))).fv)
      0

theorem nb051_support_mem_0000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part003`. -/


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

theorem nb051_support_mem_0001 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv z) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0002 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0003 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv z) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0004 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_000 x y A B C) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0005 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    z ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
        ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
            (Wff.classEq (Class.cv z) C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0006 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    x ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0007 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    y ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0008 (x : Var) (y : Var) (z : Var) :
    x ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0009 (x : Var) (y : Var) (z : Var) :
    y ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0010 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    x ∈
      (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C)
              (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv ∪
        ((Class.cab (nb051_alpha_dummy_003 x y A B C)
            (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0011 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    y ∈
      (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C)
              (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv ∪
        ((Class.cab (nb051_alpha_dummy_003 x y A B C)
            (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0012 (x : Var) (y : Var) (z : Var) :
    x ∈
      (((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv ∪
        ((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0013 (x : Var) (y : Var) (z : Var) :
    y ∈
      (((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv ∪
        ((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0014 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    x ∈
      (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C)
                (Class.cv (nb051_alpha_dummy_000 x y A B C))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s := ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv)
        ((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C)
                (Class.cv (nb051_alpha_dummy_000 x y A B C))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                    (syn_csn (syn_c0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0015 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    y ∈
      (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C)
                (Class.cv (nb051_alpha_dummy_000 x y A B C))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s := ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv)
        ((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C)
                (Class.cv (nb051_alpha_dummy_000 x y A B C))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                    (syn_csn (syn_c0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0016 (x : Var) (y : Var) (z : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s := ((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv)
        ((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                    (syn_csn (syn_c0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0017 (x : Var) (y : Var) (z : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s := ((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv)
        ((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                    (syn_csn (syn_c0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0018 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    x ∈ (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) :=
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

theorem nb051_support_mem_0019 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    y ∈ (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0020 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_004 x y A B C) ∈
      (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0021 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_006 x y z) ∈ (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0022 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_011 x y A B C) ∈
      (((Wff.classMem (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_c1c))).fv ∪
        ((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv) :=
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

theorem nb051_support_mem_0023 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_013 x y z) ∈
      (((Wff.classMem (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_c1c))).fv ∪
        ((Class.cv (nb051_alpha_dummy_013 x y z))).fv) :=
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

theorem nb051_support_mem_0024 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_011 x y A B C) ∈
      (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0025 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_013 x y z) ∈
      (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0026 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_018 x y A B C) ∈
      (((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C))
            (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv ∪
        ((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C))
            (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0027 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_021 x y z) ∈
      (((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z))
            (Class.cv (nb051_alpha_dummy_022 x y z)))).fv ∪
        ((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z))
            (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0028 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_018 x y A B C) ∈
      (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪
        ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0029 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_021 x y z) ∈
      (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪
        ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0030 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_019 x y A B C) ∈
      (((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C))
            (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv ∪
        ((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C))
            (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0031 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_022 x y z) ∈
      (((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z))
            (Class.cv (nb051_alpha_dummy_022 x y z)))).fv ∪
        ((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z))
            (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0032 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_019 x y A B C) ∈
      (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪
        ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0033 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_022 x y z) ∈
      (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪
        ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0034 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_018 x y A B C) ∈
      (((syn_ccompl (Class.cv (nb051_alpha_dummy_018 x y A B C)))).fv ∪
        ((syn_ccompl (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0035 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_021 x y z) ∈
      (((syn_ccompl (Class.cv (nb051_alpha_dummy_021 x y z)))).fv ∪
        ((syn_ccompl (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0036 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_018 x y A B C) ∈
      (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪
        ((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0037 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_021 x y z) ∈
      (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪
        ((Class.cv (nb051_alpha_dummy_021 x y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0038 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_019 x y A B C) ∈
      (((syn_ccompl (Class.cv (nb051_alpha_dummy_018 x y A B C)))).fv ∪
        ((syn_ccompl (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0039 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_022 x y z) ∈
      (((syn_ccompl (Class.cv (nb051_alpha_dummy_021 x y z)))).fv ∪
        ((syn_ccompl (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0040 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_019 x y A B C) ∈
      (((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv ∪
        ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0041 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_022 x y z) ∈
      (((Class.cv (nb051_alpha_dummy_022 x y z))).fv ∪
        ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0042 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_000 x y A B C) ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0043 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_000 x y A B C) ∈
      (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C)
                (Class.cv (nb051_alpha_dummy_000 x y A B C))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_right (a := (nb051_alpha_dummy_000 x y A B C)) (t := ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C)
                (Class.cv (nb051_alpha_dummy_000 x y A B C))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                    (syn_csn (syn_c0c)))))))).fv)
        ((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C)
              (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0044 (x : Var) (y : Var) (z : Var) :
    z ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0045 (x : Var) (y : Var) (z : Var) :
    z ∈
      (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_right (a := z) (t := ((syn_ccompl
            (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                    (syn_csn (syn_c0c)))))))).fv)
        ((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z)
              (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                  (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0046 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_000 x y A B C) ∈
      (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C)
              (Class.cv (nb051_alpha_dummy_000 x y A B C))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C)
            (syn_wrex (nb051_alpha_dummy_004 x y A B C)
              (Class.cv (nb051_alpha_dummy_000 x y A B C))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0047 (x : Var) (y : Var) (z : Var) :
    z ∈
      (((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z)
            (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
                (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0048 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_004 x y A B C) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0049 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_006 x y z) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0050 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_004 x y A B C) ∈
      (((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv ∪
        ((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part004`. -/


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

theorem nb051_support_mem_0051 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_006 x y z) ∈
      (((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv ∪
        ((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_wpp_notmem_0000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_004 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_004, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 1)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 1))))

theorem nb051_wpp_notmem_0001 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_006 x y z) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_006, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 1)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 1))))

theorem nb051_wpp_notmem_0002 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_003 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_003, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 0)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 0))))

theorem nb051_wpp_notmem_0003 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_005 x y z) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_005, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 0)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 0))))

theorem nb051_wpp_notmem_0004 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_009 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv :=
  by
  have inequality0 : (nb051_alpha_dummy_009 x y A B C) ≠ x :=
    by
    unfold nb051_alpha_dummy_009
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0010 x y A B C) 0)))
  have inequality1 : (nb051_alpha_dummy_009 x y A B C) ≠ y :=
    by
    unfold nb051_alpha_dummy_009
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0011 x y A B C) 0)))
  simpa only [fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton,
    not_or] using (And.intro inequality0 inequality1)

theorem nb051_wpp_notmem_0005 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_010 x y z) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv :=
  by
  have inequality0 : (nb051_alpha_dummy_010 x y z) ≠ x :=
    by
    unfold nb051_alpha_dummy_010
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0012 x y z) 0)))
  have inequality1 : (nb051_alpha_dummy_010 x y z) ≠ y :=
    by
    unfold nb051_alpha_dummy_010
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0013 x y z) 0)))
  simpa only [fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton,
    not_or] using (And.intro inequality0 inequality1)

theorem nb051_wpp_notmem_0006 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_007 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv :=
  by
  have inequality0 : (nb051_alpha_dummy_007 x y A B C) ≠ x :=
    by
    unfold nb051_alpha_dummy_007
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0014 x y A B C) 0)))
  have inequality1 : (nb051_alpha_dummy_007 x y A B C) ≠ y :=
    by
    unfold nb051_alpha_dummy_007
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0015 x y A B C) 0)))
  simpa only [fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton,
    not_or] using (And.intro inequality0 inequality1)

theorem nb051_wpp_notmem_0007 (x : Var) (y : Var) (z : Var) :
    (nb051_alpha_dummy_008 x y z) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv :=
  by
  have inequality0 : (nb051_alpha_dummy_008 x y z) ≠ x :=
    by
    unfold nb051_alpha_dummy_008
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0016 x y z) 0)))
  have inequality1 : (nb051_alpha_dummy_008 x y z) ≠ y :=
    by
    unfold nb051_alpha_dummy_008
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0017 x y z) 0)))
  simpa only [fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton,
    not_or] using (And.intro inequality0 inequality1)

theorem nb051_compact_fv_empty_0008 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0008 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_000 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_000, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0018 x y A B C) 0)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0019 x y A B C) 0))))

theorem nb051_compact_fv_empty_0009 (z : Var) : z ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0009 (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) : z ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simp only [fv_syn_cop, Finset.mem_union, fv_class_cv, (Ne.symm dv_x_z),
    Finset.mem_singleton, (Ne.symm dv_y_z), or_false, not_false_eq_true]

theorem nb051_compact_fv_empty_0010 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0010 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_001 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_001, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0000 x y A B C) 0)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0002 x y A B C) 0))))

theorem nb051_compact_fv_empty_0011 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0011 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    (nb051_alpha_dummy_002 x y z A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_002, fv_syn_cop, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0001 x y z A B C) 0)))
      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0003 x y z A B C) 0))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part005`. -/


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

theorem nb051_compact_envfresh_0000 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TEnvFresh
      [((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
        ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
        ((nb051_alpha_dummy_009 x y A B C), (nb051_alpha_dummy_010 x y z)),
        ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
        ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      ((syn_cop (Class.cv x) (Class.cv y))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb051_alpha_dummy_004 x y A B C) (nb051_alpha_dummy_006 x y z)
      (nb051_wpp_notmem_0000 x y A B C) (nb051_wpp_notmem_0001 x y z)
      (TEnvFresh.consFresh (nb051_alpha_dummy_003 x y A B C) (nb051_alpha_dummy_005 x y z)
        (nb051_wpp_notmem_0002 x y A B C) (nb051_wpp_notmem_0003 x y z)
        (TEnvFresh.consFresh (nb051_alpha_dummy_009 x y A B C)
          (nb051_alpha_dummy_010 x y z) (nb051_wpp_notmem_0004 x y A B C)
          (nb051_wpp_notmem_0005 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_007 x y A B C)
            (nb051_alpha_dummy_008 x y z) (nb051_wpp_notmem_0006 x y A B C)
            (nb051_wpp_notmem_0007 x y z)
            (TEnvFresh.consFresh (nb051_alpha_dummy_000 x y A B C) z
              (nb051_wpp_notmem_0008 x y A B C) (nb051_wpp_notmem_0009 x y z dv_x_z dv_y_z)
              (TEnvFresh.consSame y (TEnvFresh.consSame x
                  (TEnvFresh.consFresh (nb051_alpha_dummy_001 x y A B C)
                    (nb051_alpha_dummy_002 x y z A B C) (nb051_wpp_notmem_0010 x y A B C)
                    (nb051_wpp_notmem_0011 x y z A B C)
                    (TEnvFresh.nil ((syn_cop (Class.cv x) (Class.cv y))).fv)))))))))

@[expose]
noncomputable def nb051_wpp_refl_0000 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TReflOn
      [((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
        ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
        ((nb051_alpha_dummy_009 x y A B C), (nb051_alpha_dummy_010 x y z)),
        ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
        ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      ((syn_cop (Class.cv x) (Class.cv y))).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0000 x y z A B C dv_x_z dv_y_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
