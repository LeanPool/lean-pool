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

/-! Certificates from `NAR4C072C001Part001`. -/


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
noncomputable def nb072_alpha_dummy_000 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_001 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_002 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_003 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_004 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_005 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_006 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))))))).fv ∪
      ((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_007 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_008 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv ∪
      ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_009 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_004 x y)
          (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
              (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv ∪
      ((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
              (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_010 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_011 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_012 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_005 x y))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_005 x y))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_014 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_c1c))).fv ∪
      ((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_015 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_012 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb072_alpha_dummy_012 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb072_alpha_dummy_012 x y))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_016 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_017 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_018 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb072_alpha_dummy_019 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_020 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb072_alpha_dummy_022 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H))
          (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv ∪
      ((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H))
          (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_023 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y))
          (Class.cv (nb072_alpha_dummy_021 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y))
          (Class.cv (nb072_alpha_dummy_021 x y)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_024 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪
      ((Class.cv (nb072_alpha_dummy_021 x y))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_026 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)))).fv ∪
      ((syn_ccompl (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_027 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_020 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb072_alpha_dummy_021 x y)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_028 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_029 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪
      ((Class.cv (nb072_alpha_dummy_020 x y))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_030 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_021 x y))).fv ∪
      ((Class.cv (nb072_alpha_dummy_021 x y))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_032 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_004 x y)
          (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y)
          (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_034 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_035 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_036 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv ∪
      ((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_037 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_038 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
      ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_039 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
      ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_040 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_041 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_042 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))).fv ∪
      ((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_043 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_044 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
            (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv ∪
      ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
            (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_045 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_040 x y H)
          (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv ∪
      ((Class.cab (nb072_alpha_dummy_040 x y H)
          (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_046 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_047 (x : Var) (H : Class) : Var :=
  (freshVar ((H).fv ∪ ((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_048 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (({(nb072_alpha_dummy_046 A B R S_cls H)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
          (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_049 (x : Var) (H : Class) : Var :=
  (freshVar (({(nb072_alpha_dummy_047 x H)} : Finset Var) ∪
      ((syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_050 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq
          (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
            (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
              (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
          (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_051 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq
          (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
            (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
              (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
          (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_052 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
          (Class.cab (nb072_alpha_dummy_047 x H)
            (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
          (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_053 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
          (Class.cab (nb072_alpha_dummy_047 x H)
            (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
          (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_054 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_055 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_056 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_057 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_058 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))))))).fv ∪
      ((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_059 (x : Var) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_060 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv ∪
      ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_061 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_056 x H)
          (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
            (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv ∪
      ((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
            (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_062 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_063 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_064 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_057 x H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_065 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_057 x H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_066 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_c1c))).fv ∪
      ((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_067 (x : Var) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_064 x H)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb072_alpha_dummy_064 x H)) (syn_c1c))).fv ∪
      ((Class.cv (nb072_alpha_dummy_064 x H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_068 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_069 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_070 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb072_alpha_dummy_071 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_072 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_073 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb072_alpha_dummy_074 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H))
          (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv ∪
      ((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H))
          (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_075 (x : Var) (H : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H))
          (Class.cv (nb072_alpha_dummy_073 x H)))).fv ∪
      ((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H))
          (Class.cv (nb072_alpha_dummy_073 x H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_076 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_077 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_073 x H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_078 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)))).fv ∪
      ((syn_ccompl (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_079 (x : Var) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_072 x H)))).fv ∪
      ((syn_ccompl (Class.cv (nb072_alpha_dummy_073 x H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_080 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_081 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_072 x H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_082 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_083 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_073 x H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_073 x H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_084 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_085 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_056 x H)
          (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H)
          (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_086 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_087 (x : Var) (H : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_088 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv ∪
      ((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_089 (x : Var) (H : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv ∪
      ((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_090 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_048 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_091 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_049 x H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_092 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_093 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_094 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_095 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_096 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_c1c))).fv ∪
      ((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_097 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_c1c))).fv ∪
      ((Class.cv (nb072_alpha_dummy_094 x y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_098 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_099 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_100 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb072_alpha_dummy_101 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_102 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_103 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb072_alpha_dummy_104 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H))
          (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv ∪
      ((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H))
          (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_105 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H))
          (Class.cv (nb072_alpha_dummy_103 x y H)))).fv ∪
      ((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H))
          (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_106 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_107 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_108 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)))).fv ∪
      ((syn_ccompl (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_109 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_102 x y H)))).fv ∪
      ((syn_ccompl (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_110 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_111 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_102 x y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_112 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_113 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_103 x y H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_114 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
            (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
            (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_115 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_040 x y H)
          (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H)
          (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_116 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_117 (y : Var) (H : Class) : Var :=
  (freshVar ((H).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_118 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (({(nb072_alpha_dummy_116 A B R S_cls H)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
          (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_119 (y : Var) (H : Class) : Var :=
  (freshVar (({(nb072_alpha_dummy_117 y H)} : Finset Var) ∪
      ((syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_120 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq
          (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
            (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
              (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
          (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_121 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq
          (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
            (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
              (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
          (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_122 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq
          (Class.cab (nb072_alpha_dummy_117 y H)
            (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
          (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_123 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq
          (Class.cab (nb072_alpha_dummy_117 y H)
            (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
          (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_124 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_125 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_126 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_127 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_128 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))))))).fv ∪
      ((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_129 (y : Var) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_130 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv ∪
      ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_131 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_126 y H)
          (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
            (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv ∪
      ((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
            (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
              (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_132 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_133 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_134 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_127 y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_135 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_127 y H))).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_136 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_c1c))).fv ∪
      ((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_137 (y : Var) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_134 y H)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb072_alpha_dummy_134 y H)) (syn_c1c))).fv ∪
      ((Class.cv (nb072_alpha_dummy_134 y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_138 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_139 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_140 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb072_alpha_dummy_141 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_142 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb072_alpha_dummy_143 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb072_alpha_dummy_144 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H))
          (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv ∪
      ((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H))
          (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_145 (y : Var) (H : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H))
          (Class.cv (nb072_alpha_dummy_143 y H)))).fv ∪
      ((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H))
          (Class.cv (nb072_alpha_dummy_143 y H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_146 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_147 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_143 y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_148 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)))).fv ∪
      ((syn_ccompl (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_149 (y : Var) (H : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_142 y H)))).fv ∪
      ((syn_ccompl (Class.cv (nb072_alpha_dummy_143 y H)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C072C001Part002`. -/


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
noncomputable def nb072_alpha_dummy_150 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_151 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_142 y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_152 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_153 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_143 y H))).fv ∪
      ((Class.cv (nb072_alpha_dummy_143 y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_154 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
          (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
            (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_155 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072_alpha_dummy_126 y H)
          (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_126 y H)
          (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
            (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
              (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_156 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_157 (y : Var) (H : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_158 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv ∪
      ((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_159 (y : Var) (H : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv ∪
      ((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_160 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_118 A B R S_cls H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_161 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072_alpha_dummy_119 y H))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_162 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_163 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_164 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv ∪
      ((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv) 0)

@[expose]
noncomputable def nb072_alpha_dummy_165 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv ∪
      ((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv) 0)

theorem nb072_fresh_000 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_008 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_008] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv)
      0

theorem nb072_fresh_001 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_032 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb072_fresh_002 (x : Var) (y : Var) :
    (nb072_alpha_dummy_009 x y) ∉
      (((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_009] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv)
      0

theorem nb072_fresh_003 (x : Var) (y : Var) :
    (nb072_alpha_dummy_033 x y) ∉
      (((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb072_fresh_004 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_044 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv)
      0

theorem nb072_fresh_005 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_114 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_114] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb072_fresh_006 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_045 x y H) ∉
      (((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv)
      0

theorem nb072_fresh_007 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_115 x y H) ∉
      (((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_115] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb072_fresh_008 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_050 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_050] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv)
      0

theorem nb072_fresh_009 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_051 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_051] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv)
      1

theorem nb072_distinct_010 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_050 A B R S_cls H) ≠ (nb072_alpha_dummy_051 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_050, nb072_alpha_dummy_051] using
    (freshVar_injective (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_011 (x : Var) (H : Class) :
    (nb072_alpha_dummy_052 x H) ∉
      (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_047 x H)
              (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_052] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_047 x H)
              (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv)
      0

theorem nb072_fresh_012 (x : Var) (H : Class) :
    (nb072_alpha_dummy_053 x H) ∉
      (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_047 x H)
              (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_053] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_047 x H)
              (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv)
      1

theorem nb072_distinct_013 (x : Var) (H : Class) :
    (nb072_alpha_dummy_052 x H) ≠ (nb072_alpha_dummy_053 x H) := by
  simpa only [nb072_alpha_dummy_052, nb072_alpha_dummy_053] using
    (freshVar_injective (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_047 x H)
              (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_014 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_060 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_060] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv)
      0

theorem nb072_fresh_015 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_084 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_084] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb072_fresh_016 (x : Var) (H : Class) :
    (nb072_alpha_dummy_085 x H) ∉
      (((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_085] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb072_fresh_017 (x : Var) (H : Class) :
    (nb072_alpha_dummy_061 x H) ∉
      (((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_061] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv)
      0

theorem nb072_fresh_018 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_120 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_120] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv)
      0

theorem nb072_fresh_019 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_121 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_121] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv)
      1

theorem nb072_distinct_020 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_120 A B R S_cls H) ≠ (nb072_alpha_dummy_121 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_120, nb072_alpha_dummy_121] using
    (freshVar_injective (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_021 (y : Var) (H : Class) :
    (nb072_alpha_dummy_122 y H) ∉
      (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_117 y H)
              (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_122] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_117 y H)
              (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv)
      0

theorem nb072_fresh_022 (y : Var) (H : Class) :
    (nb072_alpha_dummy_123 y H) ∉
      (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_117 y H)
              (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_123] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_117 y H)
              (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv)
      1

theorem nb072_distinct_023 (y : Var) (H : Class) :
    (nb072_alpha_dummy_122 y H) ≠ (nb072_alpha_dummy_123 y H) := by
  simpa only [nb072_alpha_dummy_122, nb072_alpha_dummy_123] using
    (freshVar_injective (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_117 y H)
              (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_024 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_130 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_130] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv)
      0

theorem nb072_fresh_025 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_154 A B R S_cls H) ∉
      (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_154] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb072_fresh_026 (y : Var) (H : Class) :
    (nb072_alpha_dummy_155 y H) ∉
      (((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_155] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb072_fresh_027 (y : Var) (H : Class) :
    (nb072_alpha_dummy_131 y H) ∉
      (((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_131] using
    freshVar_not_mem
      (((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv)
      0

theorem nb072_fresh_028 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_002 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_002] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv)
      0

theorem nb072_fresh_029 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_003 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_003] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv)
      1

theorem nb072_distinct_030 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_002 A B R S_cls H) ≠ (nb072_alpha_dummy_003 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_002, nb072_alpha_dummy_003] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_031 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_054 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_054] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv)
      0

theorem nb072_fresh_032 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_055 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_055] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv)
      1

theorem nb072_distinct_033 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_054 A B R S_cls H) ≠ (nb072_alpha_dummy_055 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_054, nb072_alpha_dummy_055] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_034 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_124 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_124] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv)
      0

theorem nb072_fresh_035 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_125 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_125] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv)
      1

theorem nb072_distinct_036 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_124 A B R S_cls H) ≠ (nb072_alpha_dummy_125 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_124, nb072_alpha_dummy_125] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_037 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_010 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_010] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) 0

theorem nb072_fresh_038 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_011 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_011] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) 1

theorem nb072_distinct_039 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_010 A B R S_cls H) ≠ (nb072_alpha_dummy_011 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_010, nb072_alpha_dummy_011] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_fresh_040 (x : Var) (y : Var) :
    (nb072_alpha_dummy_012 x y) ∉ (((Class.cv (nb072_alpha_dummy_005 x y))).fv) := by
  simpa only [nb072_alpha_dummy_012] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_005 x y))).fv) 0

theorem nb072_fresh_041 (x : Var) (y : Var) :
    (nb072_alpha_dummy_013 x y) ∉ (((Class.cv (nb072_alpha_dummy_005 x y))).fv) := by
  simpa only [nb072_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_005 x y))).fv) 1

theorem nb072_distinct_042 (x : Var) (y : Var) :
    (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_013 x y) := by
  simpa only [nb072_alpha_dummy_012, nb072_alpha_dummy_013] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_005 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb072_fresh_043 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_016 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_016] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_044 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_017 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_017] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_045 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_018 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_018] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_046 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_016 A B R S_cls H) ≠ (nb072_alpha_dummy_017 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_016, nb072_alpha_dummy_017] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_distinct_047 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_016 A B R S_cls H) ≠ (nb072_alpha_dummy_018 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_016, nb072_alpha_dummy_018] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb072_distinct_048 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_017 A B R S_cls H) ≠ (nb072_alpha_dummy_018 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_017, nb072_alpha_dummy_018] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb072_fresh_049 (x : Var) (y : Var) :
    (nb072_alpha_dummy_019 x y) ∉
      (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_050 (x : Var) (y : Var) :
    (nb072_alpha_dummy_020 x y) ∉
      (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_051 (x : Var) (y : Var) :
    (nb072_alpha_dummy_021 x y) ∉
      (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_052 (x : Var) (y : Var) :
    (nb072_alpha_dummy_019 x y) ≠ (nb072_alpha_dummy_020 x y) := by
  simpa only [nb072_alpha_dummy_019, nb072_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_distinct_053 (x : Var) (y : Var) :
    (nb072_alpha_dummy_019 x y) ≠ (nb072_alpha_dummy_021 x y) := by
  simpa only [nb072_alpha_dummy_019, nb072_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb072_distinct_054 (x : Var) (y : Var) :
    (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_021 x y) := by
  simpa only [nb072_alpha_dummy_020, nb072_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb072_fresh_055 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_028 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv)
      0

theorem nb072_fresh_056 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_024 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_024] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv)
      0

theorem nb072_fresh_057 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_030 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv)
      0

theorem nb072_fresh_058 (x : Var) (y : Var) :
    (nb072_alpha_dummy_029 x y) ∉
      (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪
        ((Class.cv (nb072_alpha_dummy_020 x y))).fv) :=
  by
  simpa only [nb072_alpha_dummy_029] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪
        ((Class.cv (nb072_alpha_dummy_020 x y))).fv)
      0

theorem nb072_fresh_059 (x : Var) (y : Var) :
    (nb072_alpha_dummy_025 x y) ∉
      (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪
        ((Class.cv (nb072_alpha_dummy_021 x y))).fv) :=
  by
  simpa only [nb072_alpha_dummy_025] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪
        ((Class.cv (nb072_alpha_dummy_021 x y))).fv)
      0

theorem nb072_fresh_060 (x : Var) (y : Var) :
    (nb072_alpha_dummy_031 x y) ∉
      (((Class.cv (nb072_alpha_dummy_021 x y))).fv ∪
        ((Class.cv (nb072_alpha_dummy_021 x y))).fv) :=
  by
  simpa only [nb072_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_021 x y))).fv ∪
        ((Class.cv (nb072_alpha_dummy_021 x y))).fv)
      0

theorem nb072_fresh_061 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_092 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_092] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) 0

theorem nb072_fresh_062 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_093 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_093] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) 1

theorem nb072_distinct_063 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_092 A B R S_cls H) ≠ (nb072_alpha_dummy_093 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_092, nb072_alpha_dummy_093] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_fresh_064 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_094 x y H) ∉ (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) := by
  simpa only [nb072_alpha_dummy_094] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) 0

theorem nb072_fresh_065 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_095 x y H) ∉ (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) := by
  simpa only [nb072_alpha_dummy_095] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) 1

theorem nb072_distinct_066 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_095 x y H) := by
  simpa only [nb072_alpha_dummy_094, nb072_alpha_dummy_095] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb072_fresh_067 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_090 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_048 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_090] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_048 A B R S_cls H))).fv) 0

theorem nb072_fresh_068 (x : Var) (H : Class) :
    (nb072_alpha_dummy_091 x H) ∉ (((Class.cv (nb072_alpha_dummy_049 x H))).fv) := by
  simpa only [nb072_alpha_dummy_091] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_049 x H))).fv) 0

theorem nb072_fresh_069 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_062 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_062] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) 0

theorem nb072_fresh_070 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_063 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_063] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) 1

theorem nb072_distinct_071 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_062 A B R S_cls H) ≠ (nb072_alpha_dummy_063 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_062, nb072_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_fresh_072 (x : Var) (H : Class) :
    (nb072_alpha_dummy_064 x H) ∉ (((Class.cv (nb072_alpha_dummy_057 x H))).fv) := by
  simpa only [nb072_alpha_dummy_064] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_057 x H))).fv) 0

theorem nb072_fresh_073 (x : Var) (H : Class) :
    (nb072_alpha_dummy_065 x H) ∉ (((Class.cv (nb072_alpha_dummy_057 x H))).fv) := by
  simpa only [nb072_alpha_dummy_065] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_057 x H))).fv) 1

theorem nb072_distinct_074 (x : Var) (H : Class) :
    (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_065 x H) := by
  simpa only [nb072_alpha_dummy_064, nb072_alpha_dummy_065] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_057 x H))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb072_fresh_075 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_068 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_076 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_069 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_077 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_070 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_078 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_068 A B R S_cls H) ≠ (nb072_alpha_dummy_069 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_068, nb072_alpha_dummy_069] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_distinct_079 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_068 A B R S_cls H) ≠ (nb072_alpha_dummy_070 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_068, nb072_alpha_dummy_070] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb072_distinct_080 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_070 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_069, nb072_alpha_dummy_070] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb072_fresh_081 (x : Var) (H : Class) :
    (nb072_alpha_dummy_071 x H) ∉
      (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_071] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_082 (x : Var) (H : Class) :
    (nb072_alpha_dummy_072 x H) ∉
      (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_072] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_083 (x : Var) (H : Class) :
    (nb072_alpha_dummy_073 x H) ∉
      (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_073] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_084 (x : Var) (H : Class) :
    (nb072_alpha_dummy_071 x H) ≠ (nb072_alpha_dummy_072 x H) := by
  simpa only [nb072_alpha_dummy_071, nb072_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_distinct_085 (x : Var) (H : Class) :
    (nb072_alpha_dummy_071 x H) ≠ (nb072_alpha_dummy_073 x H) := by
  simpa only [nb072_alpha_dummy_071, nb072_alpha_dummy_073] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb072_distinct_086 (x : Var) (H : Class) :
    (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_073 x H) := by
  simpa only [nb072_alpha_dummy_072, nb072_alpha_dummy_073] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb072_fresh_087 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_080 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_080] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv)
      0

theorem nb072_fresh_088 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_076 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_076] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv)
      0

theorem nb072_fresh_089 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_082 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_082] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv)
      0

theorem nb072_fresh_090 (x : Var) (H : Class) :
    (nb072_alpha_dummy_081 x H) ∉
      (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_072 x H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_081] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_072 x H))).fv)
      0

theorem nb072_fresh_091 (x : Var) (H : Class) :
    (nb072_alpha_dummy_077 x H) ∉
      (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_073 x H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_077] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_073 x H))).fv)
      0

theorem nb072_fresh_092 (x : Var) (H : Class) :
    (nb072_alpha_dummy_083 x H) ∉
      (((Class.cv (nb072_alpha_dummy_073 x H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_073 x H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_083] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_073 x H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_073 x H))).fv)
      0

theorem nb072_fresh_093 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_098 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_098] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_094 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_099 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_099] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_095 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_100 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_100] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_096 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_098 A B R S_cls H) ≠ (nb072_alpha_dummy_099 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_098, nb072_alpha_dummy_099] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_distinct_097 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_098 A B R S_cls H) ≠ (nb072_alpha_dummy_100 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_098, nb072_alpha_dummy_100] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb072_distinct_098 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_100 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_099, nb072_alpha_dummy_100] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb072_fresh_099 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_101 x y H) ∉
      (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_101] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_100 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_102 x y H) ∉
      (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_102] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_101 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_103 x y H) ∉
      (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_103] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_102 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_101 x y H) ≠ (nb072_alpha_dummy_102 x y H) := by
  simpa only [nb072_alpha_dummy_101, nb072_alpha_dummy_102] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_distinct_103 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_101 x y H) ≠ (nb072_alpha_dummy_103 x y H) := by
  simpa only [nb072_alpha_dummy_101, nb072_alpha_dummy_103] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb072_distinct_104 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_103 x y H) := by
  simpa only [nb072_alpha_dummy_102, nb072_alpha_dummy_103] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb072_fresh_105 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_110 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_110] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv)
      0

theorem nb072_fresh_106 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_106 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_106] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv)
      0

theorem nb072_fresh_107 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_112 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_112] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv)
      0

theorem nb072_fresh_108 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_111 x y H) ∉
      (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_102 x y H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_111] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_102 x y H))).fv)
      0

theorem nb072_fresh_109 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_107 x y H) ∉
      (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_107] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_103 x y H))).fv)
      0

theorem nb072_fresh_110 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_113 x y H) ∉
      (((Class.cv (nb072_alpha_dummy_103 x y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_113] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_103 x y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_103 x y H))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C072C001Part003`. -/


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

theorem nb072_fresh_111 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_160 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_118 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_160] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_118 A B R S_cls H))).fv) 0

theorem nb072_fresh_112 (y : Var) (H : Class) :
    (nb072_alpha_dummy_161 y H) ∉ (((Class.cv (nb072_alpha_dummy_119 y H))).fv) := by
  simpa only [nb072_alpha_dummy_161] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_119 y H))).fv) 0

theorem nb072_fresh_113 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_132 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_132] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) 0

theorem nb072_fresh_114 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_133 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_133] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) 1

theorem nb072_distinct_115 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_132 A B R S_cls H) ≠ (nb072_alpha_dummy_133 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_132, nb072_alpha_dummy_133] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_fresh_116 (y : Var) (H : Class) :
    (nb072_alpha_dummy_134 y H) ∉ (((Class.cv (nb072_alpha_dummy_127 y H))).fv) := by
  simpa only [nb072_alpha_dummy_134] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_127 y H))).fv) 0

theorem nb072_fresh_117 (y : Var) (H : Class) :
    (nb072_alpha_dummy_135 y H) ∉ (((Class.cv (nb072_alpha_dummy_127 y H))).fv) := by
  simpa only [nb072_alpha_dummy_135] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_127 y H))).fv) 1

theorem nb072_distinct_118 (y : Var) (H : Class) :
    (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_135 y H) := by
  simpa only [nb072_alpha_dummy_134, nb072_alpha_dummy_135] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_127 y H))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb072_fresh_119 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_138 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_138] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_120 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_139 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_139] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_121 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_140 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_140] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_122 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_138 A B R S_cls H) ≠ (nb072_alpha_dummy_139 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_138, nb072_alpha_dummy_139] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_distinct_123 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_138 A B R S_cls H) ≠ (nb072_alpha_dummy_140 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_138, nb072_alpha_dummy_140] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb072_distinct_124 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_140 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_139, nb072_alpha_dummy_140] using
    (freshVar_injective
      (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb072_fresh_125 (y : Var) (H : Class) :
    (nb072_alpha_dummy_141 y H) ∉
      (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_141] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_126 (y : Var) (H : Class) :
    (nb072_alpha_dummy_142 y H) ∉
      (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_142] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_127 (y : Var) (H : Class) :
    (nb072_alpha_dummy_143 y H) ∉
      (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb072_alpha_dummy_143] using
    freshVar_not_mem (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_128 (y : Var) (H : Class) :
    (nb072_alpha_dummy_141 y H) ≠ (nb072_alpha_dummy_142 y H) := by
  simpa only [nb072_alpha_dummy_141, nb072_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_distinct_129 (y : Var) (H : Class) :
    (nb072_alpha_dummy_141 y H) ≠ (nb072_alpha_dummy_143 y H) := by
  simpa only [nb072_alpha_dummy_141, nb072_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb072_distinct_130 (y : Var) (H : Class) :
    (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_143 y H) := by
  simpa only [nb072_alpha_dummy_142, nb072_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb072_fresh_131 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_150 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_150] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv)
      0

theorem nb072_fresh_132 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_146 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_146] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv)
      0

theorem nb072_fresh_133 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_152 A B R S_cls H) ∉
      (((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_152] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv)
      0

theorem nb072_fresh_134 (y : Var) (H : Class) :
    (nb072_alpha_dummy_151 y H) ∉
      (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_142 y H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_151] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_142 y H))).fv)
      0

theorem nb072_fresh_135 (y : Var) (H : Class) :
    (nb072_alpha_dummy_147 y H) ∉
      (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_143 y H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_147] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_143 y H))).fv)
      0

theorem nb072_fresh_136 (y : Var) (H : Class) :
    (nb072_alpha_dummy_153 y H) ∉
      (((Class.cv (nb072_alpha_dummy_143 y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_143 y H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_153] using
    freshVar_not_mem
      (((Class.cv (nb072_alpha_dummy_143 y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_143 y H))).fv)
      0

theorem nb072_fresh_137 (x : Var) (H : Class) :
    (nb072_alpha_dummy_056 x H) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_056] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) 0

theorem nb072_fresh_138 (x : Var) (H : Class) :
    (nb072_alpha_dummy_057 x H) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_057] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) 1

theorem nb072_distinct_139 (x : Var) (H : Class) :
    (nb072_alpha_dummy_056 x H) ≠ (nb072_alpha_dummy_057 x H) := by
  simpa only [nb072_alpha_dummy_056, nb072_alpha_dummy_057] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_140 (x : Var) (y : Var) :
    (nb072_alpha_dummy_004 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb072_alpha_dummy_004] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb072_fresh_141 (x : Var) (y : Var) :
    (nb072_alpha_dummy_005 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb072_alpha_dummy_005] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb072_distinct_142 (x : Var) (y : Var) :
    (nb072_alpha_dummy_004 x y) ≠ (nb072_alpha_dummy_005 x y) := by
  simpa only [nb072_alpha_dummy_004, nb072_alpha_dummy_005] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_143 (y : Var) (H : Class) :
    (nb072_alpha_dummy_126 y H) ∉
      (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_126] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) 0

theorem nb072_fresh_144 (y : Var) (H : Class) :
    (nb072_alpha_dummy_127 y H) ∉
      (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_127] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) 1

theorem nb072_distinct_145 (y : Var) (H : Class) :
    (nb072_alpha_dummy_126 y H) ≠ (nb072_alpha_dummy_127 y H) := by
  simpa only [nb072_alpha_dummy_126, nb072_alpha_dummy_127] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_146 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_014 A B R S_cls H) ∉
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_014] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv)
      0

theorem nb072_fresh_147 (x : Var) (y : Var) :
    (nb072_alpha_dummy_015 x y) ∉
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_012 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_012 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_012 x y))).fv) :=
  by
  simpa only [nb072_alpha_dummy_015] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_012 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_012 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_012 x y))).fv)
      0

theorem nb072_fresh_148 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_066 A B R S_cls H) ∉
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_066] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv)
      0

theorem nb072_fresh_149 (x : Var) (H : Class) :
    (nb072_alpha_dummy_067 x H) ∉
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_064 x H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_064 x H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_064 x H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_067] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_064 x H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_064 x H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_064 x H))).fv)
      0

theorem nb072_fresh_150 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_096 A B R S_cls H) ∉
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_096] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv)
      0

theorem nb072_fresh_151 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_097 x y H) ∉
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_094 x y H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_097] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_094 x y H))).fv)
      0

theorem nb072_fresh_152 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_136 A B R S_cls H) ∉
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_136] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv)
      0

theorem nb072_fresh_153 (y : Var) (H : Class) :
    (nb072_alpha_dummy_137 y H) ∉
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_134 y H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_134 y H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_134 y H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_137] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_134 y H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_134 y H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_134 y H))).fv)
      0

theorem nb072_fresh_154 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_006 A B R S_cls H) ∉
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_006] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb072_fresh_155 (x : Var) (y : Var) :
    (nb072_alpha_dummy_007 x y) ∉
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y)
              (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_004 x y)
              (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_007] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y)
              (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_004 x y)
              (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb072_fresh_156 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_042 A B R S_cls H) ∉
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb072_fresh_157 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_043 x y H) ∉
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb072_fresh_158 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_058 A B R S_cls H) ∉
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_058] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb072_fresh_159 (x : Var) (H : Class) :
    (nb072_alpha_dummy_059 x H) ∉
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H)
              (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_056 x H)
              (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_059] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H)
              (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_056 x H)
              (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb072_fresh_160 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_128 A B R S_cls H) ∉
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_128] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb072_fresh_161 (y : Var) (H : Class) :
    (nb072_alpha_dummy_129 y H) ∉
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H)
              (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_126 y H)
              (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb072_alpha_dummy_129] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H)
              (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_126 y H)
              (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb072_fresh_162 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_026 A B R S_cls H) ∉
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_163 (x : Var) (y : Var) :
    (nb072_alpha_dummy_027 x y) ∉
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_020 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_021 x y)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_027] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_020 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_021 x y)))).fv)
      0

theorem nb072_fresh_164 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_078 A B R S_cls H) ∉
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_078] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_165 (x : Var) (H : Class) :
    (nb072_alpha_dummy_079 x H) ∉
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_072 x H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_073 x H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_079] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_072 x H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_073 x H)))).fv)
      0

theorem nb072_fresh_166 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_108 A B R S_cls H) ∉
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_108] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_167 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_109 x y H) ∉
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_102 x y H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_109] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_102 x y H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_103 x y H)))).fv)
      0

theorem nb072_fresh_168 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_148 A B R S_cls H) ∉
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_148] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_169 (y : Var) (H : Class) :
    (nb072_alpha_dummy_149 y H) ∉
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_142 y H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_143 y H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_149] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_142 y H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_143 y H)))).fv)
      0

theorem nb072_fresh_170 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_034 A B R S_cls H) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_034] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb072_fresh_171 (x : Var) (y : Var) :
    (nb072_alpha_dummy_035 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_035] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb072_fresh_172 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_162 A B R S_cls H) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_162] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb072_fresh_173 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_163 x y H) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_163] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb072_fresh_174 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_086 A B R S_cls H) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_086] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb072_fresh_175 (x : Var) (H : Class) :
    (nb072_alpha_dummy_087 x H) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_087] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb072_fresh_176 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_156 A B R S_cls H) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_156] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb072_fresh_177 (y : Var) (H : Class) :
    (nb072_alpha_dummy_157 y H) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_157] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb072_fresh_178 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_038 A B R S_cls H) ∉
      (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
        ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
        ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_179 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_039 A B R S_cls H) ∉
      (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
        ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
        ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv)
      1

theorem nb072_distinct_180 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_038 A B R S_cls H) ≠ (nb072_alpha_dummy_039 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_038, nb072_alpha_dummy_039] using
    (freshVar_injective (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
        ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_181 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_040 x y H) ∉
      (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) :=
  by
  simpa only [nb072_alpha_dummy_040] using
    freshVar_not_mem (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) 0

theorem nb072_fresh_182 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_041 x y H) ∉
      (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) :=
  by
  simpa only [nb072_alpha_dummy_041] using
    freshVar_not_mem (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) 1

theorem nb072_distinct_183 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_040 x y H) ≠ (nb072_alpha_dummy_041 x y H) := by
  simpa only [nb072_alpha_dummy_040, nb072_alpha_dummy_041] using
    (freshVar_injective (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_184 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_022 A B R S_cls H) ∉
      (((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_022] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_185 (x : Var) (y : Var) :
    (nb072_alpha_dummy_023 x y) ∉
      (((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y))
            (Class.cv (nb072_alpha_dummy_021 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y))
            (Class.cv (nb072_alpha_dummy_021 x y)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_023] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y))
            (Class.cv (nb072_alpha_dummy_021 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y))
            (Class.cv (nb072_alpha_dummy_021 x y)))).fv)
      0

theorem nb072_fresh_186 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_074 A B R S_cls H) ∉
      (((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_074] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_187 (x : Var) (H : Class) :
    (nb072_alpha_dummy_075 x H) ∉
      (((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H))
            (Class.cv (nb072_alpha_dummy_073 x H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H))
            (Class.cv (nb072_alpha_dummy_073 x H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_075] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H))
            (Class.cv (nb072_alpha_dummy_073 x H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H))
            (Class.cv (nb072_alpha_dummy_073 x H)))).fv)
      0

theorem nb072_fresh_188 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_104 A B R S_cls H) ∉
      (((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_104] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_189 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_105 x y H) ∉
      (((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H))
            (Class.cv (nb072_alpha_dummy_103 x y H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H))
            (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_105] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H))
            (Class.cv (nb072_alpha_dummy_103 x y H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H))
            (Class.cv (nb072_alpha_dummy_103 x y H)))).fv)
      0

theorem nb072_fresh_190 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_144 A B R S_cls H) ∉
      (((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_144] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_191 (y : Var) (H : Class) :
    (nb072_alpha_dummy_145 y H) ∉
      (((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H))
            (Class.cv (nb072_alpha_dummy_143 y H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H))
            (Class.cv (nb072_alpha_dummy_143 y H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_145] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H))
            (Class.cv (nb072_alpha_dummy_143 y H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H))
            (Class.cv (nb072_alpha_dummy_143 y H)))).fv)
      0

theorem nb072_fresh_192 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_036 A B R S_cls H) ∉
      (((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_036] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_193 (x : Var) (y : Var) :
    (nb072_alpha_dummy_037 x y) ∉
      (((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv)
      0

theorem nb072_fresh_194 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_164 A B R S_cls H) ∉
      (((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_164] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_195 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_165 x y H) ∉
      (((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_165] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv)
      0

theorem nb072_fresh_196 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_088 A B R S_cls H) ∉
      (((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_088] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_197 (x : Var) (H : Class) :
    (nb072_alpha_dummy_089 x H) ∉
      (((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_089] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv)
      0

theorem nb072_fresh_198 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_158 A B R S_cls H) ∉
      (((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_158] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_199 (y : Var) (H : Class) :
    (nb072_alpha_dummy_159 y H) ∉
      (((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_159] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv)
      0

theorem nb072_fresh_200 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_046 A B R S_cls H) ∉
      ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_046] using
    freshVar_not_mem ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv) 0

theorem nb072_fresh_201 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_116 A B R S_cls H) ∉
      ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) :=
  by
  simpa only [nb072_alpha_dummy_116] using
    freshVar_not_mem ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) 0

theorem nb072_fresh_202 (x : Var) (H : Class) :
    (nb072_alpha_dummy_047 x H) ∉ ((H).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb072_alpha_dummy_047] using freshVar_not_mem ((H).fv ∪ ((Class.cv x)).fv) 0

theorem nb072_fresh_203 (y : Var) (H : Class) :
    (nb072_alpha_dummy_117 y H) ∉ ((H).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb072_alpha_dummy_117] using freshVar_not_mem ((H).fv ∪ ((Class.cv y)).fv) 0

theorem nb072_fresh_204 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∉
      ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) :=
  by
  simpa only [nb072_alpha_dummy_000] using
    freshVar_not_mem ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0

theorem nb072_fresh_205 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∉
      ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) :=
  by
  simpa only [nb072_alpha_dummy_001] using
    freshVar_not_mem ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1

theorem nb072_distinct_206 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_001 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_000, nb072_alpha_dummy_001] using
    (freshVar_injective ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (i := 0) (j := 1)
      (by decide))

theorem nb072_fresh_207 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_048 A B R S_cls H) ∉
      (({(nb072_alpha_dummy_046 A B R S_cls H)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_048] using
    freshVar_not_mem
      (({(nb072_alpha_dummy_046 A B R S_cls H)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_208 (x : Var) (H : Class) :
    (nb072_alpha_dummy_049 x H) ∉
      (({(nb072_alpha_dummy_047 x H)} : Finset Var) ∪
        ((syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_049] using
    freshVar_not_mem
      (({(nb072_alpha_dummy_047 x H)} : Finset Var) ∪
        ((syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))).fv)
      0

theorem nb072_fresh_209 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072_alpha_dummy_118 A B R S_cls H) ∉
      (({(nb072_alpha_dummy_116 A B R S_cls H)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_118] using
    freshVar_not_mem
      (({(nb072_alpha_dummy_116 A B R S_cls H)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_210 (y : Var) (H : Class) :
    (nb072_alpha_dummy_119 y H) ∉
      (({(nb072_alpha_dummy_117 y H)} : Finset Var) ∪
        ((syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))).fv) :=
  by
  simpa only [nb072_alpha_dummy_119] using
    freshVar_not_mem
      (({(nb072_alpha_dummy_117 y H)} : Finset Var) ∪
        ((syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))).fv)
      0

theorem nb072_support_mem_0000 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0001 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_002 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0000 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_003 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_003;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0000 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0002 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0003 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y)
              (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_004 x y)
              (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072_alpha_dummy_004 x y) from (by
          unfold nb072_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072_alpha_dummy_005 x y) from (by
            unfold nb072_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0004 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_002 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0000 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_003 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_003;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0000 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0005 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072_alpha_dummy_004 x y) from (by
          unfold nb072_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072_alpha_dummy_005 x y) from (by
            unfold nb072_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0006 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_003 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0007 (x : Var) (y : Var) :
    (nb072_alpha_dummy_005 x y) ∈ (((Class.cv (nb072_alpha_dummy_005 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0008 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_010 A B R S_cls H) ∈
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv) :=
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

theorem nb072_support_mem_0009 (x : Var) (y : Var) :
    (nb072_alpha_dummy_012 x y) ∈
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_012 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_012 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_012 x y))).fv) :=
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

theorem nb072_support_mem_0010 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_010 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0011 (x : Var) (y : Var) :
    (nb072_alpha_dummy_012 x y) ∈
      (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0012 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_017 A B R S_cls H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0013 (x : Var) (y : Var) :
    (nb072_alpha_dummy_020 x y) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y))
            (Class.cv (nb072_alpha_dummy_021 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y))
            (Class.cv (nb072_alpha_dummy_021 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0014 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_017 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0015 (x : Var) (y : Var) :
    (nb072_alpha_dummy_020 x y) ∈
      (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪
        ((Class.cv (nb072_alpha_dummy_021 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0016 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_018 A B R S_cls H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0017 (x : Var) (y : Var) :
    (nb072_alpha_dummy_021 x y) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y))
            (Class.cv (nb072_alpha_dummy_021 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y))
            (Class.cv (nb072_alpha_dummy_021 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0018 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_018 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0019 (x : Var) (y : Var) :
    (nb072_alpha_dummy_021 x y) ∈
      (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪
        ((Class.cv (nb072_alpha_dummy_021 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0020 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_017 A B R S_cls H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0021 (x : Var) (y : Var) :
    (nb072_alpha_dummy_020 x y) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_020 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_021 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0022 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_017 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0023 (x : Var) (y : Var) :
    (nb072_alpha_dummy_020 x y) ∈
      (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪
        ((Class.cv (nb072_alpha_dummy_020 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0024 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_018 A B R S_cls H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0025 (x : Var) (y : Var) :
    (nb072_alpha_dummy_021 x y) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_020 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_021 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0026 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_018 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0027 (x : Var) (y : Var) :
    (nb072_alpha_dummy_021 x y) ∈
      (((Class.cv (nb072_alpha_dummy_021 x y))).fv ∪
        ((Class.cv (nb072_alpha_dummy_021 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0028 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C072C001Part004`. -/


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

theorem nb072_support_mem_0029 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_002 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_003 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_003;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0030 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0031 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y)
              (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_004 x y)
              (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072_alpha_dummy_004 x y) from (by
          unfold nb072_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072_alpha_dummy_005 x y) from (by
            unfold nb072_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0032 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_002 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_003 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_003;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0033 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072_alpha_dummy_004 x y) from (by
          unfold nb072_alpha_dummy_004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072_alpha_dummy_005 x y) from (by
            unfold nb072_alpha_dummy_005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0034 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_003 A B R S_cls H) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0035 (x : Var) (y : Var) :
    (nb072_alpha_dummy_005 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0036 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_003 A B R S_cls H) ∈
      (((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0037 (x : Var) (y : Var) :
    (nb072_alpha_dummy_005 x y) ∈
      (((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0038 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
        ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0039 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_038 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0038 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_039 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_039;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0038 A B R S_cls H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0040 (x : Var) (y : Var) (H : Class) :
    x ∈ (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0041 (x : Var) (y : Var) (H : Class) :
    x ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072_alpha_dummy_040 x y H) from (by
          unfold nb072_alpha_dummy_040;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072_alpha_dummy_041 x y H) from (by
            unfold nb072_alpha_dummy_041;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0042 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_038 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0038 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_039 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_039;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0038 A B R S_cls H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0043 (x : Var) (y : Var) (H : Class) :
    x ∈
      (((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072_alpha_dummy_040 x y H) from (by
          unfold nb072_alpha_dummy_040;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072_alpha_dummy_041 x y H) from (by
            unfold nb072_alpha_dummy_041;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0044 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0045 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      (({(nb072_alpha_dummy_046 A B R S_cls H)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0046 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_048 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0045 A B R S_cls H) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_046 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_046;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0044 A B R S_cls H) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0047 (x : Var) (H : Class) : x ∈ ((H).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0048 (x : Var) (H : Class) :
    x ∈
      (({(nb072_alpha_dummy_047 x H)} : Finset Var) ∪
        ((syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0049 (x : Var) (H : Class) :
    x ∈
      (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_047 x H)
              (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072_alpha_dummy_049 x H) from (by
          unfold nb072_alpha_dummy_049;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0048 x H) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072_alpha_dummy_047 x H) from (by
            unfold nb072_alpha_dummy_047;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0047 x H) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0050 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0051 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_054 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_055 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_055;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0052 (x : Var) (H : Class) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0053 (x : Var) (H : Class) :
    x ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H)
              (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_056 x H)
              (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072_alpha_dummy_056 x H) from (by
          unfold nb072_alpha_dummy_056;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072_alpha_dummy_057 x H) from (by
            unfold nb072_alpha_dummy_057;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0054 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_000 A B R S_cls H) ∈
      (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_054 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_055 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_055;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0055 (x : Var) (H : Class) :
    x ∈
      (((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072_alpha_dummy_056 x H) from (by
          unfold nb072_alpha_dummy_056;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072_alpha_dummy_057 x H) from (by
            unfold nb072_alpha_dummy_057;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0056 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_055 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0057 (x : Var) (H : Class) :
    (nb072_alpha_dummy_057 x H) ∈ (((Class.cv (nb072_alpha_dummy_057 x H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0058 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_062 A B R S_cls H) ∈
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv) :=
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

theorem nb072_support_mem_0059 (x : Var) (H : Class) :
    (nb072_alpha_dummy_064 x H) ∈
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_064 x H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_064 x H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_064 x H))).fv) :=
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

theorem nb072_support_mem_0060 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_062 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0061 (x : Var) (H : Class) :
    (nb072_alpha_dummy_064 x H) ∈
      (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0062 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_069 A B R S_cls H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0063 (x : Var) (H : Class) :
    (nb072_alpha_dummy_072 x H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H))
            (Class.cv (nb072_alpha_dummy_073 x H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H))
            (Class.cv (nb072_alpha_dummy_073 x H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0064 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_069 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0065 (x : Var) (H : Class) :
    (nb072_alpha_dummy_072 x H) ∈
      (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_073 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0066 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_070 A B R S_cls H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0067 (x : Var) (H : Class) :
    (nb072_alpha_dummy_073 x H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H))
            (Class.cv (nb072_alpha_dummy_073 x H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H))
            (Class.cv (nb072_alpha_dummy_073 x H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0068 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_070 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0069 (x : Var) (H : Class) :
    (nb072_alpha_dummy_073 x H) ∈
      (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_073 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0070 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_069 A B R S_cls H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0071 (x : Var) (H : Class) :
    (nb072_alpha_dummy_072 x H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_072 x H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_073 x H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0072 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_069 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0073 (x : Var) (H : Class) :
    (nb072_alpha_dummy_072 x H) ∈
      (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_072 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0074 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_070 A B R S_cls H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0075 (x : Var) (H : Class) :
    (nb072_alpha_dummy_073 x H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_072 x H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_073 x H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0076 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_070 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0077 (x : Var) (H : Class) :
    (nb072_alpha_dummy_073 x H) ∈
      (((Class.cv (nb072_alpha_dummy_073 x H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_073 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0078 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_046 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0079 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_046 A B R S_cls H) ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_046 A B R S_cls H) ≠ (nb072_alpha_dummy_054 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_046 A B R S_cls H) ≠ (nb072_alpha_dummy_055 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_055;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0080 (x : Var) (H : Class) :
    (nb072_alpha_dummy_047 x H) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0081 (x : Var) (H : Class) :
    (nb072_alpha_dummy_047 x H) ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H)
              (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_056 x H)
              (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_056 x H) from (by
          unfold nb072_alpha_dummy_056;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_057 x H) from (by
            unfold nb072_alpha_dummy_057;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0082 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_046 A B R S_cls H) ∈
      (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_046 A B R S_cls H) ≠ (nb072_alpha_dummy_054 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_046 A B R S_cls H) ≠ (nb072_alpha_dummy_055 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_055;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0083 (x : Var) (H : Class) :
    (nb072_alpha_dummy_047 x H) ∈
      (((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_056 x H) from (by
          unfold nb072_alpha_dummy_056;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_057 x H) from (by
            unfold nb072_alpha_dummy_057;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0084 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_055 A B R S_cls H) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0085 (x : Var) (H : Class) :
    (nb072_alpha_dummy_057 x H) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0086 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_055 A B R S_cls H) ∈
      (((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0087 (x : Var) (H : Class) :
    (nb072_alpha_dummy_057 x H) ∈
      (((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0088 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_048 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_048 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0089 (x : Var) (H : Class) :
    (nb072_alpha_dummy_049 x H) ∈ (((Class.cv (nb072_alpha_dummy_049 x H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0090 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_039 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0091 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_041 x y H) ∈ (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0092 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_092 A B R S_cls H) ∈
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv) :=
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

theorem nb072_support_mem_0093 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_094 x y H) ∈
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_094 x y H))).fv) :=
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

theorem nb072_support_mem_0094 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_092 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0095 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_094 x y H) ∈
      (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0096 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_099 A B R S_cls H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0097 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_102 x y H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H))
            (Class.cv (nb072_alpha_dummy_103 x y H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H))
            (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0098 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_099 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0099 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_102 x y H) ∈
      (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0100 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_100 A B R S_cls H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0101 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_103 x y H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H))
            (Class.cv (nb072_alpha_dummy_103 x y H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H))
            (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0102 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_100 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0103 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_103 x y H) ∈
      (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0104 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_099 A B R S_cls H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0105 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_102 x y H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_102 x y H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0106 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_099 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0107 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_102 x y H) ∈
      (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_102 x y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0108 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_100 A B R S_cls H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0109 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_103 x y H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_102 x y H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0110 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_100 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0111 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_103 x y H) ∈
      (((Class.cv (nb072_alpha_dummy_103 x y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0112 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
        ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0113 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_038 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0112 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_039 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_039;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0112 A B R S_cls H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0114 (x : Var) (y : Var) (H : Class) :
    y ∈ (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0115 (x : Var) (y : Var) (H : Class) :
    y ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072_alpha_dummy_040 x y H) from (by
          unfold nb072_alpha_dummy_040;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072_alpha_dummy_041 x y H) from (by
            unfold nb072_alpha_dummy_041;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0116 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_038 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0112 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_039 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_039;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0112 A B R S_cls H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0117 (x : Var) (y : Var) (H : Class) :
    y ∈
      (((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072_alpha_dummy_040 x y H) from (by
          unfold nb072_alpha_dummy_040;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072_alpha_dummy_041 x y H) from (by
            unfold nb072_alpha_dummy_041;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0118 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0119 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      (({(nb072_alpha_dummy_116 A B R S_cls H)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0120 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
              (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
                (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_118 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0119 A B R S_cls H) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_116 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_116;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0118 A B R S_cls H) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0121 (y : Var) (H : Class) : y ∈ ((H).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0122 (y : Var) (H : Class) :
    y ∈
      (({(nb072_alpha_dummy_117 y H)} : Finset Var) ∪
        ((syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0123 (y : Var) (H : Class) :
    y ∈
      (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq
            (Class.cab (nb072_alpha_dummy_117 y H)
              (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
            (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072_alpha_dummy_119 y H) from (by
          unfold nb072_alpha_dummy_119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0122 y H) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072_alpha_dummy_117 y H) from (by
            unfold nb072_alpha_dummy_117;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0121 y H) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0124 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0125 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_124 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_125 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_125;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0126 (y : Var) (H : Class) :
    y ∈ (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0127 (y : Var) (H : Class) :
    y ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H)
              (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_126 y H)
              (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072_alpha_dummy_126 y H) from (by
          unfold nb072_alpha_dummy_126;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072_alpha_dummy_127 y H) from (by
            unfold nb072_alpha_dummy_127;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0128 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_001 A B R S_cls H) ∈
      (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_124 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_125 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_125;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0129 (y : Var) (H : Class) :
    y ∈
      (((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072_alpha_dummy_126 y H) from (by
          unfold nb072_alpha_dummy_126;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072_alpha_dummy_127 y H) from (by
            unfold nb072_alpha_dummy_127;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0130 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_125 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0131 (y : Var) (H : Class) :
    (nb072_alpha_dummy_127 y H) ∈ (((Class.cv (nb072_alpha_dummy_127 y H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0132 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_132 A B R S_cls H) ∈
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv) :=
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

theorem nb072_support_mem_0133 (y : Var) (H : Class) :
    (nb072_alpha_dummy_134 y H) ∈
      (((Wff.classMem (Class.cv (nb072_alpha_dummy_134 y H)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb072_alpha_dummy_134 y H)) (syn_c1c))).fv ∪
        ((Class.cv (nb072_alpha_dummy_134 y H))).fv) :=
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

theorem nb072_support_mem_0134 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_132 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0135 (y : Var) (H : Class) :
    (nb072_alpha_dummy_134 y H) ∈
      (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0136 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_139 A B R S_cls H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0137 (y : Var) (H : Class) :
    (nb072_alpha_dummy_142 y H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H))
            (Class.cv (nb072_alpha_dummy_143 y H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H))
            (Class.cv (nb072_alpha_dummy_143 y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0138 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_139 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0139 (y : Var) (H : Class) :
    (nb072_alpha_dummy_142 y H) ∈
      (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_143 y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0140 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_140 A B R S_cls H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H))
            (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0141 (y : Var) (H : Class) :
    (nb072_alpha_dummy_143 y H) ∈
      (((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H))
            (Class.cv (nb072_alpha_dummy_143 y H)))).fv ∪
        ((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H))
            (Class.cv (nb072_alpha_dummy_143 y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0142 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_140 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0143 (y : Var) (H : Class) :
    (nb072_alpha_dummy_143 y H) ∈
      (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_143 y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C072C001Part005`. -/


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

theorem nb072_support_mem_0144 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_139 A B R S_cls H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0145 (y : Var) (H : Class) :
    (nb072_alpha_dummy_142 y H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_142 y H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_143 y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0146 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_139 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0147 (y : Var) (H : Class) :
    (nb072_alpha_dummy_142 y H) ∈
      (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_142 y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0148 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_140 A B R S_cls H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0149 (y : Var) (H : Class) :
    (nb072_alpha_dummy_143 y H) ∈
      (((syn_ccompl (Class.cv (nb072_alpha_dummy_142 y H)))).fv ∪
        ((syn_ccompl (Class.cv (nb072_alpha_dummy_143 y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0150 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_140 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0151 (y : Var) (H : Class) :
    (nb072_alpha_dummy_143 y H) ∈
      (((Class.cv (nb072_alpha_dummy_143 y H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_143 y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0152 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_116 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0153 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_116 A B R S_cls H) ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_116 A B R S_cls H) ≠ (nb072_alpha_dummy_124 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0152 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_116 A B R S_cls H) ≠ (nb072_alpha_dummy_125 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_125;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0152 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0154 (y : Var) (H : Class) :
    (nb072_alpha_dummy_117 y H) ∈
      (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0155 (y : Var) (H : Class) :
    (nb072_alpha_dummy_117 y H) ∈
      (((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H)
              (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb072_alpha_dummy_126 y H)
              (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_126 y H) from (by
          unfold nb072_alpha_dummy_126;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0154 y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_127 y H) from (by
            unfold nb072_alpha_dummy_127;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0154 y H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0156 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_116 A B R S_cls H) ∈
      (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_116 A B R S_cls H) ≠ (nb072_alpha_dummy_124 A B R S_cls H) from
        (by
          unfold nb072_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0152 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_116 A B R S_cls H) ≠ (nb072_alpha_dummy_125 A B R S_cls H) from
          (by
            unfold nb072_alpha_dummy_125;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0152 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0157 (y : Var) (H : Class) :
    (nb072_alpha_dummy_117 y H) ∈
      (((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_126 y H) from (by
          unfold nb072_alpha_dummy_126;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0154 y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_127 y H) from (by
            unfold nb072_alpha_dummy_127;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0154 y H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0158 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_125 A B R S_cls H) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0159 (y : Var) (H : Class) :
    (nb072_alpha_dummy_127 y H) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0160 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_125 A B R S_cls H) ∈
      (((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0161 (y : Var) (H : Class) :
    (nb072_alpha_dummy_127 y H) ∈
      (((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0162 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_118 A B R S_cls H) ∈
      (((Class.cv (nb072_alpha_dummy_118 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0163 (y : Var) (H : Class) :
    (nb072_alpha_dummy_119 y H) ∈ (((Class.cv (nb072_alpha_dummy_119 y H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0164 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_039 A B R S_cls H) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0165 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_041 x y H) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0166 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072_alpha_dummy_039 A B R S_cls H) ∈
      (((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0167 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_041 x y H) ∈
      (((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv ∪
        ((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_compact_envfresh_0000 (A : Class) (B : Class) (H : Class) :
    TEnvFresh [] ((syn_wf1o H A B)).fv := by exact (TEnvFresh.nil ((syn_wf1o H A B)).fv)

@[expose]
noncomputable def nb072_wpp_refl_0000 (A : Class) (B : Class) (H : Class) :
    TReflOn [] ((syn_wf1o H A B)).fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0000 A B H)

theorem nb072_focused_notmem_0000 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∉ A.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb072_compact_envfresh_0001 (x : Var) (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) (dv_A_x : x ∉ A.fv) :
    TEnvFresh [((nb072_alpha_dummy_000 A B R S_cls H), x)] A.fv := by
  exact
    (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x
      (nb072_focused_notmem_0000 A B R S_cls H) dv_A_x (TEnvFresh.nil A.fv))

@[expose]
noncomputable def nb072_focused_refl_0000 (x : Var) (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) (dv_A_x : x ∉ A.fv) :
    TReflOn [((nb072_alpha_dummy_000 A B R S_cls H), x)] A.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0001 x A B R S_cls H dv_A_x)

theorem nb072_focused_notmem_0001 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∉ A.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb072_compact_envfresh_0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TEnvFresh
      [((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      A.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y
      (nb072_focused_notmem_0001 A B R S_cls H) dv_A_y
      (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x
        (nb072_focused_notmem_0000 A B R S_cls H) dv_A_x (TEnvFresh.nil A.fv)))

@[expose]
noncomputable def nb072_focused_refl_0001 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TReflOn
      [((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      A.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0002 x y A B R S_cls H dv_A_x dv_A_y)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
